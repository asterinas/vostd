use colored::Colorize;
use indexmap::IndexMap;
use memoize::memoize;
use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, IsTerminal, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::Instant;

use cargo_metadata;
use cargo_metadata::CrateType;

use crate::commands::CargoBuildExterns;
use crate::{commands, dep_tree, executable, files, projects, serialization};

pub type DynError = Box<dyn std::error::Error>;

/// Verus binary location
///
/// This struct is used to locate the Verus binary and Z3 binary.
/// It uses the `Executable` struct to locate the binaries in the system PATH or in the specified hints.
/// It also provides a method to get the root directory of the project.
///

pub const CARGO_VERUS_BIN: &str = "cargo-verus";
pub const CARGO_VERUS_ENV: &str = "CARGO_VERUS_PATH";
/// Rust target triple used when `--target` is not given.
pub const DEFAULT_RUST_TARGET: &str = "x86_64-unknown-none";

/// Rust target triples that `--target` accepts. Bare-metal targets support OSTD;
/// the Linux host target supports packages that depend on `std`.
pub const SUPPORTED_RUST_TARGETS: &[&str] = &[
    "x86_64-unknown-none",
    "riscv64imac-unknown-none-elf",
    "loongarch64-unknown-none-softfloat",
    "x86_64-unknown-linux-gnu",
];

/// Rust target triples exercised end to end with OSTD on bare-metal targets
/// and `linux-bzimage-builder` on the Linux host target.
pub const VALIDATED_RUST_TARGETS: &[&str] = &[
    "x86_64-unknown-none",
    "riscv64imac-unknown-none-elf",
    "loongarch64-unknown-none-softfloat",
    "x86_64-unknown-linux-gnu",
];

pub fn parse_rust_target(triple: &str) -> Result<String, String> {
    if !SUPPORTED_RUST_TARGETS.contains(&triple) {
        return Err(format!(
            "unsupported Rust target `{triple}`; supported targets: {}",
            SUPPORTED_RUST_TARGETS.join(", ")
        ));
    }
    if !VALIDATED_RUST_TARGETS.contains(&triple) {
        warn!(
            "Rust target `{triple}` is experimental: build and verification have not \
             been validated for it. Validated targets: {}",
            VALIDATED_RUST_TARGETS.join(", ")
        );
    }
    Ok(triple.to_string())
}

pub const VERUS_HINT_RELEASE: &str = "tools/verus/source/target-verus/release";
pub const VERUS_HINT: &str = "tools/verus/source/target-verus/debug";

pub const Z3_BIN: &str = "z3";
pub const Z3_HINT: &str = "tools/verus/source";

pub const VERUSFMT_BIN: &str = "verusfmt";

pub const RUSTDOC_BIN: &str = "rustdoc";

pub const VERUSDOC_BIN: &str = "verusdoc";
pub const VERUSDOC_HINT_RELEASE: &str = "tools/verus/source/target-verus/release";
pub const VERUSDOC_HINT: &str = "tools/verus/source/target-verus/debug";

#[memoize]
pub fn get_cargo_verus(release: bool) -> PathBuf {
    executable::locate(
        CARGO_VERUS_BIN,
        Some(CARGO_VERUS_ENV),
        if release {
            &[VERUS_HINT_RELEASE, VERUS_HINT]
        } else {
            &[VERUS_HINT, VERUS_HINT_RELEASE]
        },
    )
    .unwrap_or_else(|| {
        error!(
            "Cannot find the cargo-verus binary, please run `cargo dv bootstrap --upgrade`, set CARGO_VERUS_PATH, or add cargo-verus to your PATH"
        );
    })
}

#[memoize]
pub fn get_z3() -> PathBuf {
    executable::locate(Z3_BIN, Some(CARGO_VERUS_ENV), &[Z3_HINT]).unwrap_or_else(|| {
            error!(
                "Cannot find the Z3 binary, please run `cargo dv bootstrap`, set CARGO_VERUS_PATH to the Verus toolchain directory, or add z3 to your PATH"
            );
        })
}

#[memoize]
pub fn get_rustdoc() -> PathBuf {
    executable::locate(
            RUSTDOC_BIN,
            None,
            &[] as &[&str]
        ).unwrap_or_else(|| {
            error!("Cannot find the rustdoc binary, please install it using `rustup component add rust-docs`");
        })
}

#[memoize]
pub fn get_verusdoc() -> PathBuf {
    executable::locate(VERUSDOC_BIN, None, &[VERUSDOC_HINT_RELEASE, VERUSDOC_HINT]).unwrap_or_else(
        || {
            error!("Cannot find the verusdoc binary, please try `cargo dv bootstrap --upgrade`");
        },
    )
}

#[memoize]
pub fn get_target_dir() -> PathBuf {
    let metadata = cargo_metadata::MetadataCommand::new()
        .no_deps()
        .exec()
        .expect("Failed to get metadata");
    metadata.target_directory.into_std_path_buf()
}

#[memoize]
pub fn get_workspace_root() -> PathBuf {
    let metadata = cargo_metadata::MetadataCommand::new()
        .no_deps()
        .exec()
        .expect("Failed to get metadata");
    metadata.workspace_root.into_std_path_buf()
}

#[memoize]
pub fn get_verus_target_dir() -> PathBuf {
    let verus_dir = install::verus_dir();
    verus_dir
        .join("source")
        .join("target-verus")
        .join("release")
}

#[cfg(target_os = "windows")]
#[memoize]
pub fn system_crates() -> HashSet<&'static str> {
    HashSet::from([
        "build-script-build",
        "borsh",
        "vstd",
        "verus_state_machines_macros",
    ])
}

#[cfg(target_os = "linux")]
#[memoize]
pub fn system_crates() -> HashSet<&'static str> {
    HashSet::from([
        "build-script-build",
        "borsh",
        "vstd",
        "verus_state_machines_macros",
    ])
}

#[cfg(target_os = "macos")]
#[memoize]
pub fn system_crates() -> HashSet<&'static str> {
    HashSet::from([
        "build-script-build",
        "borsh",
        "vstd",
        "verus_state_machines_macros",
    ])
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VerusDependency {
    // target name of the dependency
    pub name: String,
    // path to the dependency, only if the dependency is a local path
    pub path: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VerusTarget {
    /// name of the package, as declared in `Cargo.toml` (e.g. `id-alloc`)
    pub name: String,
    /// crate identifier of the package (e.g. `id_alloc`); differs from `name`
    /// for packages with hyphens
    pub crate_name: String,
    /// version of the package
    pub version: String,
    /// directory of the package
    pub dir: PathBuf,
    /// crate root file of the package
    pub file: PathBuf,
    /// crate type of the primary target of the package
    pub crate_type: CrateType,
    /// dependencies of the package
    pub dependencies: Vec<VerusDependency>,
    /// whether or not generate lifetime
    pub gen_lifetime: bool,
    /// runtime, has been rebuilt this session
    pub rebuilt: bool,
    /// carrying `default` features for this target
    pub features: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VerificationMode {
    Verify,
    Focus,
}

impl VerificationMode {
    fn cargo_verus_subcommand(&self) -> &'static str {
        match self {
            Self::Verify => "verify",
            Self::Focus => "focus",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExtraOptions {
    /// if log is enabled
    pub log: bool,
    /// if trace is enabled
    pub trace: bool,
    /// if release debug version
    pub release: bool,
    /// max number of errors before stopping
    pub max_errors: usize,
    /// needs to disassemble the output
    pub disasm: bool,
    /// feature options passed to cargo-verus before the verifier separator
    pub cargo_args: Vec<String>,
    /// pass-through options to the Verus verifier
    pub verus_args: Vec<String>,
    /// whether cargo-verus performs full or focused verification
    pub verification_mode: VerificationMode,
    /// Rust target triple the verified crate is compiled for
    pub rust_target: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DocOptions {}

impl VerusTarget {
    pub fn root_file(&self) -> PathBuf {
        self.file.clone()
    }

    pub fn crate_type(&self) -> CrateType {
        self.crate_type.clone()
    }

    pub fn library_prefix(&self) -> String {
        match self.crate_type {
            CrateType::Bin => "",
            CrateType::Lib => "lib",
            _ => {
                fatal!("Unknown crate type {}", self.crate_type)
            }
        }
        .to_string()
    }

    pub fn library_suffix(&self) -> String {
        match self.crate_type {
            CrateType::Bin => "",
            CrateType::Lib => "rlib",
            _ => {
                fatal!("Unknown crate type {}", self.crate_type)
            }
        }
        .to_string()
    }

    pub fn library_proof(&self) -> PathBuf {
        get_target_dir()
            .join(format!("{}.verusdata", self.crate_name))
            .to_path_buf()
    }

    pub fn library_path(&self) -> PathBuf {
        let lib = format!(
            "{}{}.{}",
            self.library_prefix(),
            self.crate_name,
            self.library_suffix()
        );
        get_target_dir().join(lib).to_path_buf()
    }
}

fn extract_dependencies(package: &cargo_metadata::Package) -> Vec<VerusDependency> {
    let mut deps = Vec::new();
    for dep in package.dependencies.iter() {
        let name: String = match dep.rename {
            Some(ref rename) => rename.replace('-', "_"),
            None => dep.name.replace('-', "_"),
        };
        let path = dep.path.as_ref().map(|utf| Path::new(&utf).to_path_buf());
        deps.push(VerusDependency { name, path });
    }
    deps
}

fn extract_features(
    package: &cargo_metadata::Package,
    workspace_features: &[String],
) -> Vec<String> {
    let mut features: HashSet<String> = HashSet::new();
    features.extend(workspace_features.iter().map(|s| s.to_string()));

    // level-traverse of the feature tree
    let mut q = vec!["default"];
    q.extend(workspace_features.iter().map(|s| s.as_str()));

    while let Some(feat) = q.pop() {
        if let Some(f) = package.features.get(feat) {
            for f in f.iter() {
                if !features.contains(f) {
                    features.insert(f.clone());
                    q.push(f);
                }
            }
        }
    }
    features.into_iter().collect()
}

pub fn workspace_features(name: &str, metadata: &cargo_metadata::Metadata) -> Vec<String> {
    metadata
        .workspace_metadata
        .get(name)
        .and_then(|v| v.get("features"))
        .and_then(|v| v.as_array())
        .map(|features_array| {
            features_array
                .iter()
                .filter_map(|feature| feature.as_str())
                .map(|feature_str| feature_str.to_string())
                .collect()
        })
        .unwrap_or_else(Vec::new)
}

fn package_verus_enabled(package: &cargo_metadata::Package) -> bool {
    package
        .metadata
        .get("verus")
        .and_then(|v| v.get("verify"))
        .and_then(|v| v.as_bool())
        .unwrap_or(false)
}

#[memoize]
pub fn verus_targets() -> HashMap<String, VerusTarget> {
    let metadata = cargo_metadata::MetadataCommand::new()
        .no_deps()
        .exec()
        .unwrap_or_else(|e| {
            error!("Failed to get metadata: {:?}", e);
        });

    let workspace: HashSet<String> = metadata
        .workspace_members
        .iter()
        .map(|id| id.to_string())
        .collect();

    let mut targets: HashMap<String, VerusTarget> = HashMap::new();
    for package in metadata.packages.iter() {
        if !workspace.contains(package.id.to_string().as_str()) || !package_verus_enabled(package) {
            // Not a valid verus target
            continue;
        }

        let target_file = package
            .metadata
            .get("verus")
            .and_then(|v| v.get("path"))
            .and_then(|v| v.as_str());

        // check if the package has a target
        if let Some(target) = package.targets.first() {
            let name = package.name.as_str().to_string();
            let crate_name = name.replace('-', "_");
            let version = package.version.to_string();
            let dir = Path::new(&package.manifest_path)
                .parent()
                .unwrap()
                .to_path_buf();
            let crate_type = if target.crate_types.contains(&CrateType::Bin) {
                CrateType::Bin
            } else {
                CrateType::Lib
            };
            let file = dir.clone().join(target_file.unwrap_or(match crate_type {
                CrateType::Bin => "src/main.rs",
                _ => "src/lib.rs",
            }));

            let deps = extract_dependencies(package);

            let gen_lifetime = package
                .metadata
                .get("verus")
                .and_then(|v| v.get("check_lifetime"))
                .and_then(|v| v.as_bool())
                .unwrap_or(true);

            let ws_features = workspace_features(&name, &metadata);
            let features = extract_features(package, ws_features.as_slice());

            targets.insert(
                crate_name.clone(),
                VerusTarget {
                    name,
                    crate_name,
                    version,
                    dir,
                    file,
                    crate_type,
                    dependencies: deps,
                    gen_lifetime,
                    rebuilt: false,
                    features,
                },
            );
        } else {
            // No valid target
            continue;
        }
    }
    targets
}

pub fn find_target(t: &str) -> Result<VerusTarget, String> {
    let all = verus_targets();
    let s = files::dir_as_package(t);
    // Target names are keyed by crate identifier (`-` -> `_`); accept both
    // spellings so users can pass the package name as well.
    let key = s.replace('-', "_");

    let target = all.get(&key).cloned().unwrap_or_else(|| {
        error!(
            "Cannot find target {}\n\n  Targets available:\n{}",
            t,
            all.keys()
                .fold(String::new(), |acc, k| { acc + "\n - " + k })
        );
    });
    Ok(target)
}

fn get_local_dependency_direct(target: &VerusTarget) -> IndexMap<String, VerusTarget> {
    let all = verus_targets();
    let mut deps = IndexMap::new();

    for dep in target.dependencies.iter() {
        if system_crates().contains(dep.name.as_str()) {
            // Skip system crates
            continue;
        }
        if dep.path.is_none() {
            // Not a local path dependency
            continue;
        }
        let dep_key = dep.name.replace('-', "_");
        if !all.contains_key(&dep_key) {
            // Not in current workspace
            continue;
        }
        let dep_target = all.get(&dep_key).unwrap();
        deps.insert(dep_key, dep_target.clone());
    }

    deps
}

pub fn get_local_dependency(target: &VerusTarget) -> IndexMap<String, VerusTarget> {
    let mut result = IndexMap::new();
    let mut visited = std::collections::HashSet::new();

    fn collect_deps_recursively(
        target: &VerusTarget,
        result: &mut IndexMap<String, VerusTarget>,
        visited: &mut std::collections::HashSet<String>,
        _is_root: bool,
    ) {
        let target_name = target.crate_name.clone();

        // Prevent infinite recursion
        if visited.contains(&target_name) {
            return;
        }
        visited.insert(target_name.clone());

        // Get direct dependencies
        let direct_deps = get_local_dependency_direct(target);

        // Add direct dependencies to result (unless it's the root target)
        for (dep_name, dep_target) in direct_deps.iter() {
            if !result.contains_key(dep_name) {
                result.insert(dep_name.clone(), dep_target.clone());
            }
            // Recursively collect dependencies of this dependency
            collect_deps_recursively(dep_target, result, visited, false);
        }
    }

    collect_deps_recursively(target, &mut result, &mut visited, true);
    result
}

pub fn get_remote_dependency(
    target: &VerusTarget,
    release: bool,
    rust_target: &str,
) -> IndexMap<String, String> {
    let externs = resolve_deps_cached(target, release, rust_target).renamed_full_externs();

    let mut deps = IndexMap::new();

    let local_verus = verus_targets()
        .values()
        .map(|t| t.crate_name.clone())
        .collect::<HashSet<_>>();

    for (name, path) in externs.iter() {
        if system_crates().contains(name.as_str()) {
            // Skip system crates
            continue;
        }

        if local_verus.contains(name) {
            // Skip local verus dependencies
            continue;
        }
        deps.insert(name.clone(), path.clone());
    }

    deps
}

pub fn check_externs(externs: &IndexMap<String, String>) -> Result<(), DynError> {
    for (name, path) in externs.iter() {
        if !Path::new(path).exists() {
            return Err(format!(
                "Cannot find the external library file at `{}` for `{}`",
                path, name
            )
            .into());
        }
    }
    Ok(())
}

pub fn cmd_push_externs(cmd: &mut Command, externs: &IndexMap<String, String>) {
    for (name, path) in externs.iter() {
        cmd.arg("--extern").arg(format!("{}={}", name, path));
    }
}

pub fn reorder_deps(target: &VerusTarget, deps: &mut CargoBuildExterns) {
    let raw = dep_tree::cargo_tree(&target.name);
    let tree = dep_tree::CargoTree::parse(&raw);
    let rank = tree.rank();
    let rk = |x: &String| -> usize { *rank.get(x).unwrap_or(&usize::MAX) };

    deps.last_level.sort_by(|a, _, b, _| rk(a).cmp(&rk(b)));

    deps.libraries.sort_by(|_, a, _, b| {
        let a = a.name.replace('-', "_");
        let b = b.name.replace('-', "_");
        rk(&a).cmp(&rk(&b))
    })
}

pub fn resolve_deps(target: &VerusTarget, release: bool, rust_target: &str) -> CargoBuildExterns {
    let dummy_rs = target.dir.join("src").join(".dummy.rs");
    files::touch(&dummy_rs.to_string_lossy());

    let mut externs = commands::cargo_build_resolve_deps(
        &target.name,
        &target.crate_name,
        &HashMap::new(),
        release,
        rust_target,
    );

    if externs.deps_ready {
        reorder_deps(target, &mut externs);
        return externs;
    }
    warn!("Unable to resolve dependencies for `{}`", target.name);
    CargoBuildExterns::default()
}

/// Cache file name for a target's resolved dependencies.
///
/// Externs differ by Rust target triple (other architectures' artifacts) and by
/// profile (`--release` changes the rlib directory), so both are part of the key.
fn deps_cache_file_name(package: &str, release: bool, rust_target: &str) -> String {
    let profile = if release { "release" } else { "debug" };
    format!("{package}.{rust_target}.{profile}.deps.toml")
}

pub fn resolve_deps_cached(
    target: &VerusTarget,
    release: bool,
    rust_target: &str,
) -> serialization::Dependencies {
    let deps_path = get_target_dir().join(deps_cache_file_name(&target.name, release, rust_target));
    let cargo_toml = target.dir.join("Cargo.toml");
    if deps_path.exists() && files::newer(&deps_path, &cargo_toml) {
        // cache is up to date, read it directly
        let deps: serialization::Dependencies = serialization::deserialize(&deps_path);
        deps
    } else {
        // rebuild cache
        let externs = resolve_deps(target, release, rust_target);
        let deps: serialization::Dependencies = externs.into();
        serialization::serialize(&deps_path, &deps);
        deps
    }
}

/// Move files from workspace `.verus-log` root into a per-crate subdirectory.
fn move_verus_log_files(crate_name: &str) {
    let workspace_root = get_workspace_root();
    let verus_log_dir = workspace_root.join(".verus-log");
    if !verus_log_dir.exists() || !verus_log_dir.is_dir() {
        return;
    }

    let crate_dir = verus_log_dir.join(crate_name);
    // If crate_dir exists, clear its contents; otherwise create it.
    if crate_dir.exists() {
        if let Ok(entries) = fs::read_dir(&crate_dir) {
            for entry in entries.filter_map(|e| e.ok()) {
                let p = entry.path();
                if p.is_file() {
                    if let Err(e) = fs::remove_file(&p) {
                        warn!("Failed to remove file {}: {}", p.display(), e);
                    }
                } else if p.is_dir() {
                    if let Err(e) = fs::remove_dir_all(&p) {
                        warn!("Failed to remove dir {}: {}", p.display(), e);
                    }
                }
            }
        }
    } else if let Err(e) = fs::create_dir_all(&crate_dir) {
        warn!(
            "Failed to create crate log dir {}: {}",
            crate_dir.display(),
            e
        );
        return;
    }

    if let Ok(entries) = fs::read_dir(&verus_log_dir) {
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_file() {
                let dest = crate_dir.join(path.file_name().unwrap());
                if let Err(e) = fs::rename(&path, &dest) {
                    warn!(
                        "Failed to move log file {} -> {}: {}",
                        path.display(),
                        dest.display(),
                        e
                    );
                }
            }
        }
    }
}

pub fn exec_verify(targets: &[VerusTarget], options: &ExtraOptions) -> Result<(), DynError> {
    let z3 = get_z3();
    let run = |target: Option<&VerusTarget>| -> Result<(), DynError> {
        let ts_start = Instant::now();
        let cmd = &mut Command::new(get_cargo_verus(options.release));
        cmd.env("RUSTC_BOOTSTRAP", "1")
            .env("VERUS_Z3_PATH", &z3)
            .arg(options.verification_mode.cargo_verus_subcommand());
        push_cargo_args(
            cmd,
            target.map(|target| target.name.as_str()),
            &options.cargo_args,
            false,
            &options.rust_target,
        );

        let mut verus_args = Vec::new();
        if options.log {
            verus_args.push("--log-all".to_string());
        }
        if options.trace {
            cmd.env("RUST_BACKTRACE", "full");
            verus_args.push("--trace".to_string());
        }
        verus_args.push(format!("--multiple-errors={}", options.max_errors));
        verus_args.extend(options.verus_args.clone());
        push_verus_args(cmd, &verus_args);

        info!(
            "  {} {} {}",
            "Verifying".bold().green(),
            target
                .map(|t| t.name.as_str())
                .unwrap_or("workspace")
                .white(),
            target.map(|t| t.version.as_str()).unwrap_or("").white()
        );
        debug!(">> {:?}", cmd);

        let status = run_filtered_command(cmd).unwrap_or_else(|e| {
            error!("Error during verification: {}", e);
        });

        if status.success() {
            // duration
            let duration = ts_start.elapsed();
            info!(
                "  {} {} {} in {:.2}s",
                "Verified".bold().green(),
                target
                    .map(|t| t.name.as_str())
                    .unwrap_or("workspace")
                    .white(),
                target.map(|t| t.version.as_str()).unwrap_or("").white(),
                duration.as_secs_f64()
            );

            if options.log && target.is_some() {
                let target = target.unwrap();
                move_verus_log_files(&target.crate_name);
            }
        } else {
            error!(
                "Verification failed for {}",
                target.map(|t| t.name.as_str()).unwrap_or("workspace")
            );
        }

        Ok(())
    };

    if targets.is_empty() {
        run(None)?;
    } else {
        for target in targets.iter() {
            run(Some(target))?;
        }
    }
    Ok(())
}

const VERUS_SPEC_WARNING_START: &str =
    "warning: #[verus_spec] is likely used inside a verus! block.";
const VERUS_SPEC_WARNING_END: &str =
    "= note: this warning originates in the attribute macro `verus_spec`";

pub fn run_filtered_command(cmd: &mut Command) -> std::io::Result<std::process::ExitStatus> {
    let configured_color = std::env::var_os("CARGO_TERM_COLOR");
    if should_force_cargo_color(std::io::stderr().is_terminal(), configured_color.as_deref()) {
        // Piping stderr for filtering would otherwise make Cargo disable the
        // colors it normally emits to an interactive terminal.
        cmd.env("CARGO_TERM_COLOR", "always");
    }
    cmd.stderr(Stdio::piped());
    let mut child = cmd.spawn()?;
    let child_stderr = child.stderr.take().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::Other,
            "could not capture the process stderr",
        )
    })?;

    let filter_result =
        filter_verus_spec_warnings(BufReader::new(child_stderr), &mut std::io::stderr().lock());
    let status_result = child.wait();

    // If stderr filtering failed (e.g. the writer closed), don't leave the
    // child process orphaned and running during a long `make` flow.
    if filter_result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }

    filter_result?;
    status_result
}

fn should_force_cargo_color(stderr_is_terminal: bool, configured: Option<&OsStr>) -> bool {
    stderr_is_terminal
        && configured
            .map(|value| value.eq_ignore_ascii_case("auto"))
            .unwrap_or(true)
}

fn filter_verus_spec_warnings<R: BufRead, W: Write>(
    reader: R,
    writer: &mut W,
) -> std::io::Result<()> {
    let mut candidate = Vec::new();
    let mut suppress_following_blank_line = false;

    for line in reader.lines() {
        let line = line?;
        let plain_line = strip_ansi_escape_codes(&line);

        if suppress_following_blank_line {
            suppress_following_blank_line = false;
            if plain_line.trim().is_empty() {
                continue;
            }
        }

        if !candidate.is_empty() {
            let is_warning_end = plain_line.contains(VERUS_SPEC_WARNING_END);
            candidate.push(line);
            if is_warning_end {
                candidate.clear();
                suppress_following_blank_line = true;
            }
            continue;
        }

        if plain_line.contains(VERUS_SPEC_WARNING_START) {
            candidate.push(line);
        } else {
            writeln!(writer, "{line}")?;
        }
    }

    // A truncated or changed diagnostic is not a confirmed match. Preserve it
    // instead of accidentally hiding unrelated compiler output.
    for line in candidate {
        writeln!(writer, "{line}")?;
    }
    writer.flush()
}

fn strip_ansi_escape_codes(line: &str) -> String {
    let mut plain = String::with_capacity(line.len());
    let mut chars = line.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '\u{1b}' && chars.next_if_eq(&'[').is_some() {
            for code in chars.by_ref() {
                if ('@'..='~').contains(&code) {
                    break;
                }
            }
        } else {
            plain.push(ch);
        }
    }

    plain
}

fn push_cargo_args(
    cmd: &mut Command,
    package: Option<&str>,
    cargo_args: &[String],
    release: bool,
    rust_target: &str,
) {
    if let Some(package) = package {
        cmd.arg("-p").arg(package);
    }
    // cargo-verus stops recognizing Verus-relevant Cargo options after options
    // such as --release and --target, so features must be inserted first.
    cmd.args(cargo_args);
    if release {
        cmd.arg("--release");
    }
    cmd.arg("--target").arg(rust_target);
}

fn push_verus_args(cmd: &mut Command, verus_args: &[String]) {
    if !verus_args.is_empty() {
        cmd.arg("--").args(verus_args);
    }
}

pub fn disassemble(target: &VerusTarget) -> Result<(), DynError> {
    let objdump = commands::get_objdump();
    let cmd = &mut Command::new(&objdump);
    let mut status = cmd
        .arg("-d")
        .arg(target.library_path())
        .stdout(Stdio::piped())
        .spawn()?;

    let out = status.stdout.take().unwrap_or_else(|| {
        error!("Error during disassembly: {:?}", cmd);
    });

    let mut rustfilt = Command::new(commands::get_rustfilt());
    let mut status = rustfilt
        .stdin(Stdio::from(out))
        .stdout(Stdio::piped())
        .spawn()?;

    let mut disasm = File::create(format!("{}.S", target.library_path().display()))?;

    let mut out = status.stdout.take().unwrap_or_else(|| {
        error!("Error during disassembly: {:?}", rustfilt);
    });

    let mut content = Vec::<u8>::new();
    out.read_to_end(&mut content)?;
    disasm.write_all(&content)?;
    disasm.flush()?;
    Ok(())
}

pub fn exec_build(targets: &[VerusTarget], options: &ExtraOptions) -> Result<(), DynError> {
    let z3 = get_z3();
    let run = |target: Option<&VerusTarget>| -> Result<(), DynError> {
        let cmd = &mut Command::new(get_cargo_verus(options.release));
        cmd.env("RUSTC_BOOTSTRAP", "1")
            .env("VERUS_Z3_PATH", &z3)
            .arg("build");
        push_cargo_args(
            cmd,
            target.map(|target| target.name.as_str()),
            &options.cargo_args,
            options.release,
            &options.rust_target,
        );

        let mut verus_args = Vec::new();
        if options.log {
            verus_args.push("--log-all".to_string());
        }
        if options.trace {
            cmd.env("RUST_BACKTRACE", "full");
            verus_args.push("--trace".to_string());
        }
        verus_args.push(format!("--multiple-errors={}", options.max_errors));
        verus_args.extend(options.verus_args.clone());
        push_verus_args(cmd, &verus_args);

        let target_name = target
            .map(|target| target.name.as_str())
            .unwrap_or("workspace");
        let target_version = target.map(|target| target.version.as_str()).unwrap_or("");

        info!(
            "  {} {} {}",
            "Building".bold().green(),
            target_name.white(),
            target_version.white()
        );
        debug!(">> {:?}", cmd);

        let status = run_filtered_command(cmd).unwrap_or_else(|e| {
            error!("Error during build: {}", e);
        });

        if status.success() {
            info!(
                "  {} {} {}",
                "Built".bold().green(),
                target_name.white(),
                target_version.white()
            );
        } else {
            error!("Build failed for target {}", target_name);
        }

        Ok(())
    };

    if targets.is_empty() {
        run(None)?;
    } else {
        for target in targets.iter() {
            run(Some(target))?;
        }
    }

    Ok(())
}

pub fn exec_clean() -> Result<(), DynError> {
    let status = Command::new("cargo").arg("clean").status()?;
    if status.success() {
        Ok(())
    } else {
        Err("cargo clean failed".into())
    }
}

#[cfg(test)]
mod argument_tests {
    use super::*;

    #[test]
    fn cargo_features_precede_target_and_verus_args() {
        let mut cmd = Command::new("cargo-verus");
        cmd.arg(VerificationMode::Focus.cargo_verus_subcommand());
        push_cargo_args(
            &mut cmd,
            Some("ostd"),
            &["--features".to_string(), "irc11".to_string()],
            false,
            DEFAULT_RUST_TARGET,
        );
        push_verus_args(&mut cmd, &["--verify-only-module=sync::rcu".to_string()]);

        let args = cmd
            .get_args()
            .map(|arg| arg.to_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            args,
            [
                "focus",
                "-p",
                "ostd",
                "--features",
                "irc11",
                "--target",
                DEFAULT_RUST_TARGET,
                "--",
                "--verify-only-module=sync::rcu",
            ]
        );
    }

    #[test]
    fn cargo_features_precede_release_for_build() {
        let mut cmd = Command::new("cargo-verus");
        cmd.arg("build");
        push_cargo_args(
            &mut cmd,
            Some("ostd"),
            &["--features".to_string(), "allow_panic".to_string()],
            true,
            DEFAULT_RUST_TARGET,
        );

        let args = cmd
            .get_args()
            .map(|arg| arg.to_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            args,
            [
                "build",
                "-p",
                "ostd",
                "--features",
                "allow_panic",
                "--release",
                "--target",
                DEFAULT_RUST_TARGET,
            ]
        );
    }

    #[test]
    fn cargo_target_follows_selected_rust_target() {
        for (package, triple) in [
            ("ostd", "riscv64imac-unknown-none-elf"),
            ("linux-bzimage-builder", "x86_64-unknown-linux-gnu"),
        ] {
            let mut cmd = Command::new("cargo-verus");
            cmd.arg("build");
            push_cargo_args(&mut cmd, Some(package), &[], false, triple);

            let args = cmd
                .get_args()
                .map(|arg| arg.to_str().unwrap())
                .collect::<Vec<_>>();
            assert_eq!(args, ["build", "-p", package, "--target", triple]);
        }
    }
}

pub mod install {
    use super::*;
    use crate::toolchain;
    use git2::Repository;

    pub struct VerusInstallOpts {
        pub restart: bool,
        pub release: bool,
        pub branch: Option<String>,
        pub build_args: Vec<String>,
        pub force_reset: bool,
        pub upstream_verus: bool,
    }

    pub const VERUS_REPO_HTTPS: &str = "https://github.com/asterinas/verus.git";
    pub const VERUS_REPO_SSH: &str = "git@github.com:asterinas/verus.git";
    pub const UPSTREAM_VERUS_REPO_HTTPS: &str = "https://github.com/verus-lang/verus.git";
    pub const UPSTREAM_VERUS_REPO_SSH: &str = "git@github.com:verus-lang/verus.git";

    fn target_repo_urls(upstream: bool) -> (&'static str, &'static str) {
        if upstream {
            (UPSTREAM_VERUS_REPO_SSH, UPSTREAM_VERUS_REPO_HTTPS)
        } else {
            (VERUS_REPO_SSH, VERUS_REPO_HTTPS)
        }
    }

    fn is_target_origin(origin_url: &str, upstream: bool) -> bool {
        let (ssh, https) = target_repo_urls(upstream);
        origin_url == ssh || origin_url == https
    }

    fn maybe_switch_origin_remote(dir: &Path, upstream: bool) -> Result<bool, DynError> {
        let repo = Repository::open(dir).unwrap_or_else(|e| {
            error!(
                "Unable to find the git repo of verus under {}: {}",
                dir.display(),
                e
            );
        });

        let mut remote = repo.find_remote("origin")?;
        let origin_url = remote.url().unwrap_or("");
        if is_target_origin(origin_url, upstream) {
            return Ok(false);
        }

        let (target_ssh, target_https) = target_repo_urls(upstream);
        let use_ssh = origin_url.starts_with("git@") || origin_url.contains("ssh://");
        let target_url = if use_ssh { target_ssh } else { target_https };

        info!(
            "Switching origin remote from {} to {}",
            origin_url, target_url
        );
        repo.remote_set_url("origin", target_url)?;

        // Refresh local remote handle after remote update.
        remote = repo.find_remote("origin")?;
        debug!("Updated origin remote URL: {}", remote.url().unwrap_or(""));
        Ok(true)
    }

    fn force_reset_to_origin(dir: &Path, branch: Option<&str>) -> Result<(), DynError> {
        let repo = Repository::open(dir).unwrap_or_else(|e| {
            error!(
                "Unable to find the git repo of verus under {}: {}",
                dir.display(),
                e
            );
        });

        let target_branch = branch.unwrap_or("main");

        let mut remote = repo.find_remote("origin")?;
        let remote_url = remote.url().unwrap_or("");
        let is_ssh = remote_url.starts_with("git@") || remote_url.contains("ssh://");

        let mut callbacks = git2::RemoteCallbacks::new();
        if is_ssh {
            callbacks.credentials(|_url, username_from_url, _allowed_types| {
                git2::Cred::ssh_key_from_agent(username_from_url.unwrap_or("git"))
            });
        }

        let mut fetch_opts = git2::FetchOptions::new();
        fetch_opts.remote_callbacks(callbacks);
        remote.fetch(&[target_branch], Some(&mut fetch_opts), None)?;

        let upstream_branch = format!("refs/remotes/origin/{}", target_branch);
        let upstream_ref = repo.find_reference(&upstream_branch).map_err(|_| {
            format!(
                "Branch '{}' does not exist in the remote repository. Please check the branch name.",
                target_branch
            )
        })?;
        let upstream_commit = upstream_ref.peel_to_commit()?;

        repo.reset(upstream_commit.as_object(), git2::ResetType::Hard, None)?;

        let refname = format!("refs/heads/{}", target_branch);
        if repo.find_reference(&refname).is_err() {
            repo.reference(
                &refname,
                upstream_commit.id(),
                false,
                &format!("Create branch {}", target_branch),
            )?;
        } else {
            let mut reference = repo.find_reference(&refname)?;
            reference.set_target(
                upstream_commit.id(),
                &format!("Force reset to origin/{}", target_branch),
            )?;
        }

        repo.set_head(&refname)?;
        let mut checkout_opts = git2::build::CheckoutBuilder::new();
        checkout_opts.force();
        repo.checkout_head(Some(&mut checkout_opts))?;

        status!("Force reset to origin/{} completed", target_branch);
        status!(
            "Repo {} updated to commit {}",
            dir.display(),
            upstream_commit.id()
        );
        Ok(())
    }

    #[memoize]
    pub fn tools_dir() -> PathBuf {
        projects::get_root().join("tools")
    }

    #[memoize]
    pub fn verus_dir() -> PathBuf {
        tools_dir().join("verus")
    }

    #[memoize]
    pub fn verus_source_dir() -> PathBuf {
        verus_dir().join("source")
    }

    #[memoize]
    pub fn tools_patch_dir() -> PathBuf {
        tools_dir().join("patches")
    }

    pub fn clone_repo(
        verus_dir: &Path,
        branch: Option<&str>,
        upstream: bool,
    ) -> Result<(), DynError> {
        let repo_ssh = if upstream {
            UPSTREAM_VERUS_REPO_SSH
        } else {
            VERUS_REPO_SSH
        };
        let repo_https = if upstream {
            UPSTREAM_VERUS_REPO_HTTPS
        } else {
            VERUS_REPO_HTTPS
        };

        let branch_name = branch.unwrap_or("main");
        let clone_dir_existed = verus_dir.exists();
        let cleanup_failed_clone = || -> Result<(), DynError> {
            if !clone_dir_existed && verus_dir.exists() {
                std::fs::remove_dir_all(verus_dir).map_err(|e| {
                    format!(
                        "Failed to clean up incomplete clone at {}: {}",
                        verus_dir.display(),
                        e
                    )
                })?;
            }
            Ok(())
        };

        info!(
            "Cloning Verus repo from {} (branch: {}) to {} ...",
            repo_https,
            branch_name,
            verus_dir.display()
        );

        let mut builder = git2::build::RepoBuilder::new();
        builder.branch(branch_name);

        let https_error = match builder.clone(repo_https, verus_dir) {
            Ok(_) => return Ok(()),
            Err(e) => e,
        };
        cleanup_failed_clone()?;

        info!("HTTPS failed, trying SSH: {}", repo_ssh);

        let mut builder_ssh = git2::build::RepoBuilder::new();
        builder_ssh.branch(branch_name);

        let mut callbacks = git2::RemoteCallbacks::new();

        callbacks.credentials(|_url, username_from_url, _allowed_types| {
            git2::Cred::ssh_key_from_agent(username_from_url.unwrap_or("git"))
        });

        let mut fetch_opts = git2::FetchOptions::new();
        fetch_opts.remote_callbacks(callbacks);
        builder_ssh.fetch_options(fetch_opts);
        let ssh_error = match builder_ssh.clone(repo_ssh, verus_dir) {
            Ok(_) => return Ok(()),
            Err(e) => e,
        };
        cleanup_failed_clone()?;

        Err(format!(
            "Failed to clone Verus repo via HTTPS ({}) or SSH ({})",
            https_error, ssh_error
        )
        .into())
    }

    #[cfg(target_os = "windows")]
    pub fn install_z3() -> Result<(), DynError> {
        let z3 = verus_source_dir().join("z3.exe");
        if !z3.exists() {
            info!("Z3 not found, downloading...");
            let mut cmd = executable::get_powershell_command()?;
            cmd.current_dir(verus_source_dir())
                .arg("/c")
                .arg(".\\tools\\get-z3.ps1")
                .status()
                .unwrap_or_else(|e| {
                    error!("Failed to download z3: {}", e);
                });
        }
        Ok(())
    }

    #[cfg(not(target_os = "windows"))]
    pub fn install_z3() -> Result<(), DynError> {
        let z3 = verus_source_dir().join("z3");
        if !z3.exists() {
            info!("Z3 not found, downloading...");
            Command::new("bash")
                .current_dir(verus_source_dir())
                .arg("-c")
                .arg("./tools/get-z3.sh")
                .status()
                .unwrap_or_else(|e| {
                    error!("Failed to download z3: {}", e);
                });
        }
        Ok(())
    }

    fn is_verusfmt_installed() -> bool {
        let output = Command::new("verusfmt").arg("--version").output();
        match output {
            Ok(output) => {
                if output.status.success() {
                    return true;
                }
            }
            Err(_) => {}
        }
        false
    }

    fn install_verusfmt() -> Result<(), DynError> {
        println!("Start to install verusfmt");
        let status = {
            #[cfg(target_os = "windows")]
            {
                // pwsh -ExecutionPolicy Bypass -c "irm https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.ps1 | iex"
                let mut cmd = executable::get_powershell_command()?;
                cmd
                .arg("-ExecutionPolicy")
                .arg("Bypass")
                .arg("-c")
                .arg("irm https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.ps1 | iex");
                println!("{:?}", cmd);
                cmd.status()
            }
            #[cfg(not(target_os = "windows"))]
            {
                // curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.sh | sh
                let mut cmd = Command::new("bash");
                cmd
                .arg("-c")
                .arg("curl --proto '=https' --tlsv1.2 -LsSf https://github.com/verus-lang/verusfmt/releases/latest/download/verusfmt-installer.sh | sh");
                println!("{:?}", cmd);
                cmd.status()
            }
        };
        if let Err(err) = status {
            eprintln!("Failed to install verusfmt {:?}", err);
            return Err(err.into());
        }
        Ok(())
    }

    fn vstd_build_args(release: bool, extra_args: &[String]) -> Vec<String> {
        let mut args = vec![
            "-p".to_string(),
            "cargo-verus".to_string(),
            "--".to_string(),
            "build".to_string(),
        ];
        if release {
            args.push("--release".to_string());
        }
        args.extend(["--manifest-path".to_string(), "vstd/Cargo.toml".to_string()]);

        for arg in extra_args {
            if arg == "--vstd-weak-memory" {
                args.extend(["--features".to_string(), "weak-memory".to_string()]);
            } else {
                args.push(arg.clone());
            }
        }
        args
    }

    pub fn build_verus(release: bool, extra_args: &[String]) -> Result<(), DynError> {
        let toolchain = verus_dir().join("rust-toolchain.toml");
        let toolchain_name = toolchain::load_toolchain(&toolchain);
        let source_dir = verus_source_dir();

        let cargo = |subcommand: &str| {
            let mut cmd = Command::new("cargo");
            cmd.current_dir(&source_dir)
                .env("RUSTUP_TOOLCHAIN", &toolchain_name)
                .arg(subcommand);
            cmd
        };

        if release
            && !cargo("make")
                .arg("--version")
                .output()
                .is_ok_and(|out| out.status.success())
        {
            let status = cargo("install").args(["cargo-make", "--locked"]).status()?;
            if !status.success() {
                return Err(format!("Installing cargo-make failed with {}", status).into());
            }
        }

        let mut build_cmd = cargo(if release { "make" } else { "build" });
        if release {
            build_cmd.arg("build");
        } else {
            build_cmd.args(["--features", "singular"]);
        }
        let mut commands = vec![(build_cmd, "Building Verus")];
        if !release || !extra_args.is_empty() {
            let mut vstd_cmd = cargo("run");
            if release {
                vstd_cmd.arg("--release");
            }
            vstd_cmd.args(vstd_build_args(release, extra_args));
            commands.push((vstd_cmd, "Building vstd"));
        }
        for (mut cmd, description) in commands {
            debug!("{:?}", cmd);
            let status = cmd.status()?;
            if !status.success() {
                return Err(format!("{} failed with {}", description, status).into());
            }
        }

        status!("Verus build complete");
        Ok(())
    }

    pub fn exec_bootstrap(options: &VerusInstallOpts) -> Result<(), DynError> {
        let verus_dir = verus_dir();

        if options.restart && verus_dir.exists() {
            info!("Removing old verus installation...");
            std::fs::remove_dir_all(&verus_dir)?;
        }

        // Clone the Verus repo if it doesn't exist
        if !verus_dir.exists() {
            clone_repo(
                &verus_dir,
                options.branch.as_deref(),
                options.upstream_verus,
            )?;
        }

        // Download Z3
        install_z3()?;

        // Build Verus
        build_verus(options.release, &options.build_args)?;

        // Update the workspace toolchain
        toolchain::sync_toolchain(
            &verus_dir.join("rust-toolchain.toml"),
            &projects::get_root().join("rust-toolchain.toml"),
        );

        // Install Verusfmt
        if options.restart || !is_verusfmt_installed() {
            install_verusfmt()?;
        }

        status!("Verus installation complete");
        Ok(())
    }

    pub fn git_pull(dir: &Path, branch: Option<&str>, force_reset: bool) -> Result<(), DynError> {
        let repo = Repository::open(dir).unwrap_or_else(|e| {
            error!(
                "Unable to find the git repo of verus under {}: {}",
                dir.display(),
                e
            );
        });

        // Determine target branch (default to "main")
        let target_branch = branch.unwrap_or("main");

        // Find the remote and check its URL to determine authentication method
        let mut remote = repo.find_remote("origin")?;
        let remote_url = remote.url().unwrap_or("");
        let is_ssh = remote_url.starts_with("git@") || remote_url.contains("ssh://");

        let mut callbacks = git2::RemoteCallbacks::new();

        if is_ssh {
            // SSH repository - use SSH key authentication
            callbacks.credentials(|_url, username_from_url, _allowed_types| {
                git2::Cred::ssh_key_from_agent(username_from_url.unwrap_or("git"))
            });
        }
        let mut fetch_opts = git2::FetchOptions::new();
        fetch_opts.remote_callbacks(callbacks);
        remote.fetch(&[target_branch], Some(&mut fetch_opts), None)?;

        // Get the current branch
        let head = repo.head()?;
        if !head.is_branch() {
            return Err("HEAD is not a branch. Cannot pull.".into());
        }

        let _ = head.shorthand().map_err(|_| "Could not get branch name")?;
        let local_commit = head.peel_to_commit()?;

        // Find the matching remote branch
        let upstream_branch = format!("refs/remotes/origin/{}", target_branch);
        let upstream_ref = repo.find_reference(&upstream_branch).map_err(|_| {
            format!(
                "Branch '{}' does not exist in the remote repository. Please check the branch name.",
                target_branch
            )
        })?;
        let upstream_commit = upstream_ref.peel_to_commit()?;

        // Check merge analysis
        let annotated_commit = repo.find_annotated_commit(upstream_commit.id())?;
        let analysis = repo.merge_analysis(&[&annotated_commit])?.0;

        if analysis.is_up_to_date() {
            status!("Already up to date");
        } else if analysis.is_fast_forward() {
            // Fast-forward
            let refname = format!("refs/heads/{}", target_branch);

            // Create local branch if it doesn't exist
            if repo.find_reference(&refname).is_err() {
                repo.reference(
                    &refname,
                    upstream_commit.id(),
                    false,
                    &format!("Create branch {}", target_branch),
                )?;
            }

            let mut reference = repo.find_reference(&refname)?;
            reference.set_target(upstream_commit.id(), "Fast-forward")?;
            repo.set_head(&refname)?;

            // Update working directory
            let mut checkout_opts = git2::build::CheckoutBuilder::new();
            checkout_opts.force();
            repo.checkout_head(Some(&mut checkout_opts))?;

            status!(
                "Fast-forwarded {} to {}",
                target_branch,
                upstream_commit.id()
            );
        } else if force_reset {
            status!(
                "Diverged from origin/{}, performing force reset",
                target_branch
            );

            let refname = format!("refs/heads/{}", target_branch);
            if repo.find_reference(&refname).is_err() {
                repo.reference(
                    &refname,
                    upstream_commit.id(),
                    false,
                    &format!("Force reset to origin/{}", target_branch),
                )?;
            } else {
                let mut reference = repo.find_reference(&refname)?;
                reference.set_target(
                    upstream_commit.id(),
                    &format!("Force reset to origin/{}", target_branch),
                )?;
            }

            repo.set_head(&refname)?;

            let mut checkout_opts = git2::build::CheckoutBuilder::new();
            checkout_opts.force();
            repo.checkout_head(Some(&mut checkout_opts))?;

            status!("Force reset to origin/{} completed", target_branch);
        } else {
            // Need to perform a merge
            let mut merge_opts = git2::MergeOptions::new();
            let mut checkout_opts = git2::build::CheckoutBuilder::new();

            // Start the merge
            repo.merge(
                &[&annotated_commit],
                Some(&mut merge_opts),
                Some(&mut checkout_opts),
            )?;

            // Check for conflicts
            if repo.index()?.has_conflicts() {
                error!("There are conflicts between the recent updates and patches. Please resolve them manually.");
            }

            // Create the merge commit
            let sig = repo.signature()?;
            let tree_id = repo.index()?.write_tree()?;
            let tree = repo.find_tree(tree_id)?;

            repo.commit(
                Some("HEAD"),
                &sig,
                &sig,
                &format!("Merge remote-tracking branch 'origin/{}'", target_branch),
                &tree,
                &[&local_commit, &upstream_commit],
            )?;

            // Clean up merge state
            repo.cleanup_state()?;

            status!("Merged origin/{} into {}", target_branch, target_branch);
        }

        status!(
            "Repo {} updated to commit {}",
            dir.display(),
            upstream_commit.id()
        );
        Ok(())
    }

    pub fn exec_upgrade(options: &VerusInstallOpts) -> Result<(), DynError> {
        // rebuild if required or if the directory doesn't exist
        if !verus_dir().exists() {
            return exec_bootstrap(options);
        }

        // git pull the Verus repo
        let verus_dir = verus_dir();
        let branch = options.branch.as_ref().map(|s| s.as_str());
        let switched = maybe_switch_origin_remote(&verus_dir, options.upstream_verus)?;
        if switched {
            force_reset_to_origin(&verus_dir, branch)?;
        } else {
            git_pull(&verus_dir, branch, options.force_reset)?;
        }
        status!("Verus repo updated to the latest version");

        // Build Verus
        build_verus(options.release, &options.build_args)?;

        // Update the workspace toolchain
        toolchain::sync_toolchain(
            &verus_dir.join("rust-toolchain.toml"),
            &projects::get_root().join("rust-toolchain.toml"),
        );

        // Install Verusfmt
        install_verusfmt()?;

        status!("Verus upgrade complete");
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn irc11_build_argument_enables_weak_memory_for_vstd() {
            let extra_args = vec!["--vstd-weak-memory".to_string()];
            assert_eq!(
                vstd_build_args(true, &extra_args),
                [
                    "-p",
                    "cargo-verus",
                    "--",
                    "build",
                    "--release",
                    "--manifest-path",
                    "vstd/Cargo.toml",
                    "--features",
                    "weak-memory",
                ]
            );
        }

        #[test]
        fn extra_vstd_build_arguments_are_forwarded() {
            let extra_args = vec!["--locked".to_string()];
            assert_eq!(
                vstd_build_args(false, &extra_args),
                [
                    "-p",
                    "cargo-verus",
                    "--",
                    "build",
                    "--manifest-path",
                    "vstd/Cargo.toml",
                    "--locked",
                ]
            );
        }
    }
}
