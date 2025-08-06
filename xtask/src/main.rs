#[macro_use]
extern crate lazy_static;

use clap::{ArgAction, Parser, Subcommand};
use cargo_metadata::{MetadataCommand};
use cargo_toml::{Manifest, Dependency};
use std::{
    collections::HashSet,
    env,
    fs::{self, File},
    io::{Read, Write},
    path::{self, Path, PathBuf},
    process::{Command, Stdio},
};
use memoize::memoize;
use git2::{
    Repository, ResetType,
    build::{RepoBuilder, CheckoutBuilder},
};
use walkdir::WalkDir;
use owo_colors::{OwoColorize, Stream};
#[cfg(not(target_os = "windows"))]
use std::os::unix::fs::PermissionsExt;
use rayon::prelude::*;

static VERUS_REPO: &str = "https://github.com/asterinas/verus.git";

fn get_platform_specific_binary_name(base_name: &str) -> String {
    #[cfg(target_os = "windows")]
    return format!("{}.exe", base_name);

    #[cfg(not(target_os = "windows"))]
    return base_name.to_string();
}

// On Windows, prefer pwsh if available, otherwise fall back to powershell.
#[cfg(target_os = "windows")]
fn get_powershell_command() -> std::io::Result<Command> {
    let check_pwsh = Command::new("pwsh")
        .arg("/?")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    if matches!(check_pwsh, Ok(status) if status.success()) {
        return Ok(Command::new("pwsh"));
    }

    let check_ps = Command::new("powershell")
        .arg("/?")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    if matches!(check_ps, Ok(status) if status.success()) {
        eprintln!(
            "{}",
            "Warning: Using powershell.exe (Windows PowerShell 5.x)."
                .if_supports_color(Stream::Stderr, |text| text.yellow())
        );
        eprintln!(
            "{}",
            "If you encounter errors related to `Get‑ExecutionPolicy` or \
            failure loading the `Microsoft.PowerShell.Security` module, please \
            try using `pwsh` (PowerShell 7 or later) instead."
                .if_supports_color(Stream::Stderr, |text| text.yellow())
        );
        return Ok(Command::new("powershell"));
    }

    Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "No working PowerShell version found",
    ))
}

fn locate_from_path<P>(binary: &P) -> Option<PathBuf>
where
    P: AsRef<Path>,
{
    env::var_os("PATH").and_then(|paths| {
        env::split_paths(&paths)
            .filter_map(|dir| {
                let full_path = dir.join(&binary);
                if full_path.is_file() {
                    Some(full_path)
                } else {
                    None
                }
            })
            .next()
    })
}

fn locate_from_hints<PB, PH>(binary: &PB, hints: &[PH]) -> Option<PathBuf>
where
    PB: AsRef<Path>,
    PH: AsRef<Path>,
{
    hints
        .iter()
        .filter_map(|hint| {
            let full_path = hint.as_ref().join(binary);
            if full_path.is_file() {
                Some(full_path)
            } else {
                None
            }
        })
        .next()
}

fn locate_from_env<P>(binary: &P, env_var: &str) -> Option<PathBuf>
where
    P: AsRef<Path>,
{
    env::var_os(env_var).and_then(|path| {
        let full_path = PathBuf::from(path);
        if full_path.is_file() {
            return Some(full_path);
        }
        let full_path = full_path.join(&binary);
        if full_path.is_file() {
            return Some(full_path);
        }
        None
    })
}

fn absolutize(path: &Path) -> PathBuf {
    if path.is_absolute() {
        return path.to_path_buf();
    }
    let mut abs = env::current_dir().unwrap();
    abs.push(path);
    abs
}

fn locate<PB, PH>(binary: PB, env_var: Option<&str>, hints: Vec<PH>) -> Option<PathBuf>
where
    PB: AsRef<Path>,
    PH: AsRef<Path>,
{
    let path = locate_from_hints(&binary, &hints)
        .or_else(|| env_var.and_then(|env_var| locate_from_env(&binary, env_var)))
        .or_else(|| locate_from_path(&binary));

    path.and_then(|path| Some(absolutize(&path)))
}

#[memoize]
fn get_verus() -> PathBuf {
    let hints = vec![PathBuf::from("tools/verus/source/target-verus/release")];
    locate(get_platform_specific_binary_name("verus"), Some("VERUS_PATH"), hints)
    .unwrap_or_else(|| {
      eprintln!("Cannot find the Verus binary, please set the VERUS_PATH environment variable or add it to your PATH");
      std::process::exit(1);
    })
}

fn get_z3() -> PathBuf {
    let verus_root = get_verus_root();
    let hints = vec![verus_root];
    locate(get_platform_specific_binary_name("z3"), Some("VERUS_Z3_PATH"), hints)
    .unwrap_or_else(|| {
      eprintln!("Cannot find the Z3 binary, please set the VERUS_Z3_PATH environment variable or add it to your PATH");
      std::process::exit(1);
    })
}

fn cargo_install(name: &str) {
    Command::new("cargo")
        .arg("install")
        .arg(name)
        .status()
        .expect("Failed to install cargo package");
}

#[memoize]
fn get_rustfilt() -> PathBuf {
    let rustfilt = locate(
        get_platform_specific_binary_name("rustfilt"),
        None,
        Vec::<PathBuf>::new(),
    );
    if rustfilt.is_none() {
        cargo_install("rustfilt");
    }
    locate(
        get_platform_specific_binary_name("rustfilt"),
        None,
        Vec::<PathBuf>::new(),
    )
    .expect("Failed to find or install rustfilt")
}

fn get_host_triple_from_sysroot(sysroot_path: &Path) -> Option<String> {
    sysroot_path
        .file_name()
        .and_then(|os_str| os_str.to_str())
        .map(|toolchain_name| {
            let mut parts = toolchain_name.splitn(2, '-');
            parts.next();
            parts.next().unwrap_or("").to_string()
        })
}

#[memoize]
fn get_objdump() -> PathBuf {
    // Check if the environment variable is set
    if let Ok(path) = std::env::var("LLVM_OBJDUMP") {
        let path = PathBuf::from(path);
        if path.is_file() {
            return path;
        }
    }

    let llvm_objdump_name = get_platform_specific_binary_name("llvm-objdump");

    // Try to find llvm-objdump in the toolchain
    if let Ok(sysroot) = std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
    {
        if sysroot.status.success() {
            let sysroot_path =
                PathBuf::from(String::from_utf8_lossy(&sysroot.stdout).trim().to_string());

            if let Some(host_triple) = get_host_triple_from_sysroot(&sysroot_path) {
                let bin_path = sysroot_path
                    .join("lib")
                    .join("rustlib")
                    .join(&host_triple)
                    .join("bin")
                    .join(&llvm_objdump_name);

                if bin_path.is_file() {
                    return bin_path;
                }
            }
        }
    }

    // Try to find llvm-objdump in the PATH
    if let Some(path) = locate(&llvm_objdump_name, None, Vec::<PathBuf>::new()) {
        if path.is_file() {
            return path;
        }
    }

    // If llvm-objdump is not found, install it using cargo
    cargo_install("cargo-binutils");

    if let Some(path) = locate(&llvm_objdump_name, None, Vec::<PathBuf>::new()) {
        if path.is_file() {
            return path;
        }
    }

    panic!("Failed to find or install llvm-objdump, please specify `LLVM_OBJDUMP` as the path to the executable")
}

#[memoize]
fn get_all_targets() -> HashSet<String> {
    let metadata = MetadataCommand::new()
        .no_deps()
        .exec()
        .expect("Failed to get cargo metadata");

    metadata
        .workspace_members
        .into_iter()
        .map(|id| {
            let package_name = &metadata
                .packages
                .iter()
                .find(|pkg| pkg.id == id)
                .expect("Failed to find package")
                .name;
            package_name.to_string()
        })
        .collect()
}

#[derive(Parser, Debug)]
#[command(
    name = "cli",
    author = "Hao",
    version = "0.1.0",
    about = "A tool to manage the formal verification targets"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Verify(VerifyArgs),
    Doc(DocArgs),
    Bootstrap(BootstrapArgs),
    Compile(CompileArgs),
    Fmt(FmtArgs),
    Update(UpdateArgs),
}

#[derive(Parser, Debug)]
struct BootstrapArgs {
    #[arg(long = "restart", help = "Remove all toolchain and restart the bootstrap",
        default_value = "false", action = ArgAction::SetTrue)]
    restart: bool,

    #[arg(long = "rust-version", help = "The rust version to use",
        default_value = "1.88.0", action = ArgAction::Set)]
    rust_version: String,
}

#[derive(Parser, Debug)]
struct UpdateArgs {
    #[arg(long = "no-verus", help = "Do not update verus",
        default_value = "false", action = ArgAction::SetTrue)]
    no_verus: bool,

    #[arg(long = "rust-version", help = "The rust version to use",
        default_value = "1.88.0", action = ArgAction::Set)]
    rust_version: String,

    #[arg(long = "test", help = "Use the test branch of Verus",
        default_value = "false", action = ArgAction::SetTrue)]
    test: bool,
}

#[derive(Parser, Debug)]
struct VerifyArgs {
    #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to verify", num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<String>,

    #[arg(short = 'e', long = "max-errors",
    help = "The maximum number of errors to display",
    default_value = "5", action = ArgAction::Set)]
    max_errors: usize,

    #[arg(short = 'i', long = "import", value_parser = target_parser,
    help = "Import verified local crates (they need to be compiled first)",
    num_args = 0.., action = ArgAction::Append)]
    imports: Vec<String>,

    #[arg(short = 'l', long = "log",
    help = "Log the verification process",
    default_value = "false", action = ArgAction::SetTrue)]
    log: bool,

    #[arg(
        last = true,
        help = "Pass-through arguments to the Verus verifier",
        allow_hyphen_values = true
    )]
    pass_through: Vec<String>,

    #[arg(long = "emit-dep-info",
    help = "Emit dependency information",
    default_value = "false", action = ArgAction::SetTrue)]
    emit_dep_info: bool,

    #[arg(short = 'c', long = "count-line",
    help = "Count the number of lines of code",
    default_value = "false", action = ArgAction::SetTrue)]
    count_line: bool,

    #[arg(short = 'p', long = "parallel",
    help = "Run verification in parallel",
    default_value = "false", action = ArgAction::SetTrue)]
    parallel: bool,
}

#[derive(Parser, Debug)]
struct DocArgs {
    #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to generate document", num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<String>,
}

#[derive(Parser, Debug)]
struct CompileArgs {
    #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to compile", num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<String>,

    #[arg(short = 'i', long = "import", value_parser = target_parser,
    help = "Import verified local crates (they need to be compiled first)",
    num_args = 0.., action = ArgAction::Append)]
    imports: Vec<String>,

    #[arg(short = 'l', long = "log",
    help = "Log the verification process",
    default_value = "false", action = ArgAction::SetTrue)]
    log: bool,

    #[arg(short = 'o', long = "release", default_value = "false",
        help = "Build artifacts in release mode",
        action = ArgAction::SetTrue)]
    release: bool,

    #[arg(short = 'd', long = "no-disasm", default_value = "false",
        help = "Do not disassemble the compiled binary",
        action = ArgAction::SetTrue)]
    no_disasm: bool,

    #[arg(
        last = true,
        help = "Pass-through arguments to the Verus verifier",
        allow_hyphen_values = true
    )]
    pass_through: Vec<String>,
}

#[derive(Parser, Debug)]
struct FmtArgs {
    #[arg(short = 't', long = "targets", value_parser = target_parser,
        help = "The targets to format", num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<String>,
}

fn target_parser(s: &str) -> Result<String, String> {
    let all_targets = get_all_targets();
    let s = s
        .trim_start_matches(".\\")
        .trim_end_matches(path::MAIN_SEPARATOR);
    if all_targets.contains(s) {
        Ok(s.to_string())
    } else {
        Err(format!("Unknown target: {}", s))
    }
}

type DynError = Box<dyn std::error::Error + Send + Sync>;

fn crate_type(target: &str) -> (PathBuf, &str) {
    let target_root = Path::new(&target).join("src");
    if target_root.join("lib.rs").is_file() {
        (target_root.join("lib.rs"), "lib")
    } else {
        (target_root.join("main.rs"), "bin")
    }
}

fn binary_suffix(crate_type: &str) -> &str {
    match crate_type {
        "lib" => "rlib",
        "bin" => "",
        _ => panic!("Unknown crate type: {}", crate_type),
    }
}

fn binary_prefix(crate_type: &str) -> &str {
    match crate_type {
        "lib" => "lib",
        "bin" => "",
        _ => panic!("Unknown crate type: {}", crate_type),
    }
}

fn verus_data(target: &str) -> PathBuf {
    let target_verus = Path::new("target").join(format!("{}.verusdata", target));
    if target_verus.is_file() {
        target_verus
    } else {
        panic!("Cannot find the verus data file for target: {}", target);
    }
}

fn verus_library(target: &str) -> PathBuf {
    let (_, crate_type) = crate_type(target);
    let output = format!(
        "{}{}.{}",
        binary_prefix(crate_type),
        target,
        binary_suffix(crate_type)
    );
    let target_library = Path::new("target").join(output);
    if target_library.is_file() {
        target_library
    } else {
        panic!("Cannot find the library file for target: {}", target);
    }
}

fn push_imports(cmd: &mut Command, imports: Vec<&str>) {
    for import in imports {
        cmd.arg("--import")
            .arg(format!("{}={}", import, verus_data(import).display()));
        cmd.arg("--extern")
            .arg(format!("{}={}", import, verus_library(import).display()));
    }
}

lazy_static! {
    static ref SYSTEM_CRATES: HashSet<&'static str> = {
        let mut set = HashSet::new();
        set.insert("vstd");
        set
    };
}

lazy_static! {
    static ref WORKSPACE_CRATES: HashSet<&'static str> = {
        let mut set = HashSet::new();
        set.insert("vstd_extra");
        set.insert("aster_common");
        set
    };
}

fn path_simplify(path: PathBuf) -> PathBuf {
    path.canonicalize()
        .unwrap_or_else(|_| PathBuf::from(path))
        .to_string_lossy()
        .to_string()
        .into()
}

fn get_dependency(target: &String) -> Vec<(String, PathBuf)> {
    let toml = Path::new(&target).join("Cargo.toml");
    let content =
        fs::read_to_string(&toml).expect(format!("Failed to read {}", &toml.display()).as_str());
    let manifest = Manifest::from_str(&content)
        .expect(format!("Failed to parse {}", &toml.display()).as_str());
    let deps = manifest
        .dependencies
        .iter()
        .filter_map(|(name, dep)| {
            if SYSTEM_CRATES.contains(name.as_str()) {
                return None;
            }
            let local: PathBuf = match dep {
                Dependency::Detailed(pkg) => {
                    if pkg.path.is_some() {
                        Path::new(target).join(pkg.path.as_ref().unwrap())
                    } else {
                        Path::new(name).to_path_buf()
                    }
                }
                _ => Path::new(name).to_path_buf(),
            };
            let local = path_simplify(local);
            if local.is_dir() {
                Some((name.clone(), local))
            } else {
                None
            }
        })
        .collect();
    deps
}

fn exec_verify(args: &VerifyArgs) -> Result<(), DynError> {
    if args.parallel && args.count_line {
        return Err("`--parallel` and `--count-line` cannot be used together".into());
    }

    let verus = get_verus();
    let z3 = get_z3();
    let imports: HashSet<_> = args.imports.iter().map(|s| s.as_str()).collect();

    let results: Result<Vec<_>, DynError> = if args.parallel {
        eprintln!(
            "{}",
            "Warning: Running verification in parallel mode, the output may be out of order."
                .if_supports_color(Stream::Stderr, |text| text.yellow())
        );
        args.targets
            .par_iter()
            .map(|target| verify_single_target(target, &verus, &z3, &imports, args))
            .collect()
    } else {
        args.targets
            .iter()
            .map(|target| verify_single_target(target, &verus, &z3, &imports, args))
            .collect()
    };

    results?;
    Ok(())
}

fn verify_single_target(
    target: &String,
    verus: &PathBuf,
    z3: &PathBuf,
    imports: &HashSet<&str>,
    args: &VerifyArgs,
) -> Result<(), DynError> {
    let (target_file, crate_type) = crate_type(target);
    let mut cmd = Command::new(verus);
    cmd.env("VERUS_PATH", verus).env("VERUS_Z3_PATH", z3);

    let deps = get_dependency(target);
    let mut target_import: HashSet<_> = imports.clone();
    target_import.extend(deps.iter().map(|(name, _)| name.as_str()));
    push_imports(&mut cmd, target_import.iter().cloned().collect());

    if args.log {
        cmd.arg("--log-all");
    }
    if args.emit_dep_info || args.count_line {
        cmd.arg("--emit=dep-info");
    }

    cmd.arg(target_file)
        .arg(format!("--crate-type={}", crate_type))
        .arg("--expand-errors")
        .arg(format!("--multiple-errors={}", args.max_errors))
        .args(&args.pass_through)
        .arg("--")
        .arg("-C")
        .arg(format!("metadata={}", target))
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    println!("Verifying target: {}", target);
    let status = cmd.status()?;
    if !status.success() {
        return Err(format!("Target {} failed with status {}", target, status).into());
    }

    if args.count_line {
        let verus_root = get_verus_root();
        let line_count_dir = verus_root.join("tools/line_count");
        let dependency_file = env::current_dir()?.join("lib.d");
        env::set_current_dir(&line_count_dir)?;
        let mut cargo_cmd = Command::new("cargo");
        cargo_cmd
            .arg("run")
            .arg("--release")
            .arg(&dependency_file)
            .arg("-p");

        println!("Counting lines for target: {}", target);
        cargo_cmd.status()?;
        fs::remove_file(&dependency_file)?;
    }

    Ok(())
}

fn exec_compile(args: &CompileArgs) -> Result<(), DynError> {
    let targets = &args.targets;
    let verus = get_verus();
    let z3 = get_z3();
    let out_dir = Path::new("target");
    let mut imports: HashSet<&str> = HashSet::new();
    imports.extend(args.imports.iter().map(|s| s.as_str()));

    if !out_dir.exists() {
        fs::create_dir(out_dir)?;
    }

    for target in targets {
        let (target_file, crate_type) = crate_type(target);
        let output = format!(
            "target/{}{}.{}",
            binary_prefix(crate_type),
            target,
            binary_suffix(crate_type)
        );
        let cmd = &mut Command::new(&verus);
        cmd.env("VERUS_PATH", &verus)
            .env("VERUS_Z3_PATH", &z3)
            .arg("--compile")
            .arg("--export")
            .arg(format!("target/{}.verusdata", target));

        let deps = get_dependency(target);
        let mut target_import = HashSet::new();
        target_import.extend(imports.clone());
        target_import.extend(deps.iter().map(|(name, _)| name.as_str()));
        push_imports(cmd, target_import.iter().cloned().collect());

        if args.log {
            cmd.arg("--log-all");
        }
        cmd.arg(target_file)
            .arg(format!("--crate-type={}", crate_type))
            .arg("-o")
            .arg(&output)
            .arg("-C")
            .arg("opt-level=2")
            .arg("-V")
            .arg("use-crate-name")
            .args(&args.pass_through)
            .arg("--")
            .arg("-C")
            .arg(format!("metadata={}", target))
            .stdout(Stdio::inherit());

        // if !args.release {
        //   cmd.arg("-V").arg("debug");
        // }

        println!("Compiling target: {}\n{:?}", target, cmd);
        cmd.status()?;

        if !args.no_disasm {
            let objdump_binary = get_objdump();
            let objdump = &mut Command::new(&objdump_binary);
            let mut status = objdump
                .arg("-d")
                .arg(&output)
                .stdout(Stdio::piped())
                .spawn()?;

            let out = status.stdout.take().expect("Failed to get objdump stdout");

            let rustfilt_binary = get_rustfilt();
            let mut rustfilt = Command::new(&rustfilt_binary);
            let mut status = rustfilt
                .stdin(Stdio::from(out))
                .stdout(Stdio::piped())
                .spawn()?;

            let mut disasm = File::create(format!(
                "target/{}{}.{}.S",
                binary_prefix(crate_type),
                target,
                binary_suffix(crate_type)
            ))?;

            let mut out = status.stdout.take().expect("Failed to get rustfilt stdout");
            let mut content = Vec::new();
            out.read_to_end(&mut content)?;
            disasm.write_all(&content)?;
        }
    }

    Ok(())
}

fn get_verus_doc() -> PathBuf {
    let verus_root = get_verus_root();
    let verus_doc = verus_root.join("target/release/verusdoc");
    if !verus_doc.is_file() {
        println!("Build verusdoc ...");
        Command::new("bash")
            .current_dir(&verus_root)
            .arg("-c")
            .arg("source ../tools/activate && vargo build --package verusdoc")
            .status()
            .expect("Failed to build verusdoc");

        Command::new("bash")
            .current_dir(&verus_root)
            .arg("-c")
            .arg("source ../tools/activate && vargo build --vstd-no-verify")
            .status()
            .expect("Failed to build debug vstd");

        println!("Done! verusdoc at {:?}", verus_doc);
    }
    absolutize(&verus_doc)
}

#[memoize]
fn get_verus_root() -> PathBuf {
    let verus_bin = get_verus();
    let verus_root = verus_bin
        .parent() // release/
        .and_then(|p| p.parent()) // target-verus/
        .and_then(|p| p.parent()) // source/
        .map(|p| p.to_path_buf());
    match verus_root {
        Some(root) if root.is_dir() => absolutize(&root),
        _ => {
            eprintln!(
                "Cannot determine the Verus source root directory based on the verus binary path.\n
                Please clone the Verus repository to tools/verus. It is available at: {}",
                VERUS_REPO
            );
            std::process::exit(1);
        }
    }
}

fn exec_doc(args: &DocArgs) -> Result<(), DynError> {
    let targets = &args.targets;
    let verus = get_verus();
    let z3 = get_z3();
    let verus_doc = get_verus_doc();
    let verus_root = get_verus_root();
    let dll_ext = match env::consts::OS {
        "windows" => "dll",
        "macos" => "dylib",
        _ => "so",
    };

    for target in targets {
        let target_root = Path::new(&target).join("src");
        let (target_file, crate_type) = if target_root.join("lib.rs").is_file() {
            (target_root.join("lib.rs"), "lib")
        } else {
            (target_root.join("main.rs"), "bin")
        };

        let cmd = &mut Command::new("rustdoc");
        cmd.env("RUSTC_BOOTSTRAP", "1")
            .env("VERUSDOC", "1")
            .env("VERUS_Z3_PATH", &z3)
            .env("VERUS", &verus_root)
            .arg("--extern")
            .arg(format!(
                "vstd={}/target-verus/debug/libvstd.rlib",
                verus_root.display()
            ))
            .arg("--extern")
            .arg(format!(
                "verus_state_machines_macros={}/target-verus/debug/lib_verus_state_machines_macros.{}",
                verus_root.display(),
                dll_ext
            ))
            .arg("--library-path")
            .arg(format!("{}/vstd", verus_root.display()))
            .arg("--edition=2018")
            .arg("--cfg")
            .arg("verus_keep_ghost")
            .arg("--cfg")
            .arg("verus_keep_ghost_body")
            .arg("--cfg")
            .arg("feature=\"std\"")
            .arg("--cfg")
            .arg("feature=\"alloc\"")
            .arg("-Zcrate-attr=feature(stmt_expr_attributes)")
            .arg("-Zcrate-attr=feature(negative_impls)")
            .arg("-Zcrate-attr=feature(rustc_attrs)")
            .arg("-Zcrate-attr=feature(unboxed_closures)")
            .arg("-Zcrate-attr=feature(register_tool)")
            .arg("-Zcrate-attr=register_tool(verus)")
            .arg("-Zcrate-attr=register_tool(verifier)")
            .arg("-Zcrate-attr=register_tool(verusfmt)")
            .arg("-Zcrate-attr=allow(internal_features)")
            .arg("-Zcrate-attr=allow(unused_braces)")
            .arg(format!("--crate-type={}", crate_type))
            .arg(target_file)
            .stdout(Stdio::inherit());
        println!("> {:?}", cmd);
        cmd.status()?;

        let cmd = &mut Command::new(&verus_doc);
        cmd.env("VERUS_PATH", &verus)
            .env("VERUS", &verus_root)
            .stdout(Stdio::inherit());
        println!("> {:?}", cmd);
        cmd.status()?;
    }

    Ok(())
}

#[allow(dead_code)]
//Not required because now we use our own fork
fn is_patch_applied(dir: &Path, patch: &Path) -> bool {
    let status = Command::new("git")
        .current_dir(dir)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .arg("apply")
        .arg("--reverse")
        .arg("--check")
        .arg(patch)
        .status()
        .expect("Failed to check patch");
    status.success()
}

#[allow(dead_code)]
//Not required because now we use our own fork
fn apply_patch(dir: &Path, patch: &Path) -> bool {
    let status = Command::new("git")
        .current_dir(dir)
        .arg("apply")
        .arg(patch)
        .status()
        .expect("Failed to apply patch");
    status.success()
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
            let mut cmd = get_powershell_command()?;
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

fn compile_verus() -> Result<(), DynError> {
    println!("Start to build the Verus compiler");
    #[cfg(target_os = "windows")]
    {
        let cmd = &mut get_powershell_command()?;
        cmd.current_dir(Path::new("tools").join("verus").join("source"))
            .arg("/c")
            //.arg("& '..\\tools\\activate.ps1' ; vargo build --release --features singular");
            .arg("& '..\\tools\\activate.ps1' ; vargo build --release");
        println!("{:?}", cmd);
        cmd.status()?;
    }
    #[cfg(not(target_os = "windows"))]
    {
        let cmd = &mut Command::new("bash");
        cmd.current_dir(Path::new("tools").join("verus").join("source"))
            .arg("-c")
            // We do not use the integer_ring feature yet
            //.arg("source ../tools/activate && vargo build --release --features singular");
            .arg("source ../tools/activate && vargo build --release");
        println!("{:?}", cmd);
        cmd.status()?;
    }
    Ok(())
}

fn exec_bootstrap(args: &BootstrapArgs) -> Result<(), DynError> {
    let verus_dir = Path::new("tools").join("verus");

    // Not required if the project includes fixed Verus code
    if args.restart && verus_dir.exists() {
        std::fs::remove_dir_all(&verus_dir)?;
    }

    if !verus_dir.exists() {
        println!(
            "Start to clone the Verus repository to {}",
            verus_dir.display()
        );
        let mut builder = RepoBuilder::new();
        if let Err(e) = builder
            .branch(&args.rust_version)
            .clone(VERUS_REPO, &verus_dir)
        {
            eprintln!(
                "Failed to clone the Verus repository, caused by {}.\r 
                Please try to manually clone it to {} and run `cargo xtask bootstrap` again.\r
                The Verus repository is available at {}.",
                e,
                verus_dir.display(),
                VERUS_REPO
            );
            std::process::exit(1);
        }
    }

    #[cfg(target_os = "windows")]
    {
        let z3_path = Path::new("tools")
            .join("verus")
            .join("source")
            .join("z3.exe");
        if !z3_path.exists() {
            println!("Start to download the Z3 solver");
            get_powershell_command()?
                .current_dir(Path::new("tools").join("verus").join("source"))
                .arg("/c")
                .arg(".\\tools\\get-z3.ps1")
                .status()
                .expect("Failed to run get-z3.ps1");
        }
    }
    #[cfg(not(target_os = "windows"))]
    {
        let z3_path = Path::new("tools").join("verus").join("source").join("z3");
        if !z3_path.exists() {
            println!("Start to download the Z3 solver");
            let get_z3_script_path = Path::new("tools")
                .join("verus")
                .join("source")
                .join("tools")
                .join("get-z3.sh");
            let permissions = fs::Permissions::from_mode(0o755);
            fs::set_permissions(&get_z3_script_path, permissions)
                .expect("Failed to set execute permission for get-z3.sh");
            Command::new("bash")
                .current_dir(Path::new("tools").join("verus").join("source"))
                .arg("-c")
                .arg("tools/get-z3.sh")
                .status()
                .expect("Failed to run get-z3.sh");
        }
    }

    /*let verus_path = Path::new("..").join("patches").join("verus-fixes.patch");
    // Not required if the project includes fixed Verus code
    if !is_patch_applied(&verus_dir, &verus_path) {
        println!("Apply the Verus patch");
        apply_patch(&verus_dir, &verus_path);
    }*/

    compile_verus()?;

    if args.restart || !is_verusfmt_installed() {
        install_verusfmt()?;
    }

    Ok(())
}

fn exec_update(args: &UpdateArgs) -> Result<(), DynError> {
    if !args.no_verus {
        let verus_dir = Path::new("tools").join("verus");
        if !verus_dir.exists() {
            println!(
                "The Verus directory does not exist, please run `cargo xtask bootstrap` first."
            );
            std::process::exit(1);
        }
        println!(
            "Start to update the Verus repository at {}",
            verus_dir.display()
        );
        let repo = Repository::open(&verus_dir)?;
        let branch = if args.test {
            println!("Using the test branch of Verus");
            "update-test"
        } else {
            &args.rust_version
        };
        repo.find_remote("origin")?
            .fetch(&[branch.to_string()], None, None)?;
        let mut checkout_builder = CheckoutBuilder::new();
        checkout_builder.force();

        let obj = repo.revparse_single(&format!("origin/{}", branch))?;
        println!("Resolved origin/{} to commit {}", branch, obj.id());
        repo.reset(&obj, ResetType::Hard, Some(&mut checkout_builder))?;

        let head = repo.head().ok().and_then(|h| h.target());
        println!("Current HEAD: {:?}", head);

        compile_verus()?;

        install_verusfmt()?;
    }
    Ok(())
}

fn exec_fmt(args: &FmtArgs) -> Result<(), DynError> {
    // do `cargo fmt` befor verusfmt
    let mut cmd = Command::new("cargo");
    cmd.arg("fmt");

    if !args.targets.is_empty() {
        for target in &args.targets {
            cmd.arg("--package").arg(target);
        }
    }

    cmd.status().expect("Failed to run cargo fmt");

    // format the xtask build script
    let xtask = Path::new("xtask").join("src").join("main.rs");
    let status = Command::new("rustfmt")
        .arg(&xtask)
        .status()
        .expect("Failed to run rustfmt");
    if !status.success() {
        eprintln!("Failed to format xtask build script");
        std::process::exit(1);
    }

    let verusfmt = locate(
        get_platform_specific_binary_name("verusfmt"),
        None,
        Vec::<PathBuf>::new(),
    )
    .unwrap_or_else(|| {
        eprintln!(
            "Cannot find the Verusfmt binary, please install it by running `cargo xtask bootstrap`"
        );
        std::process::exit(1);
    });

    // Read the cargo metadata for all files
    let metadata = MetadataCommand::new()
        .no_deps()
        .exec()
        .expect("Failed to get cargo metadata");

    // Filter packages based on the provided targets
    let fmt_packages = if args.targets.is_empty() {
        metadata.packages
    } else {
        metadata
            .packages
            .into_iter()
            .filter(|p| args.targets.contains(&p.name))
            .collect::<Vec<_>>()
    };

    for package in fmt_packages {
        for target in package.targets {
            let path = target.src_path;
            let src_dir = path.parent().unwrap();
            // Just search for all `.rs` files in the src directory instead of chasing them
            WalkDir::new(src_dir)
                .into_iter()
                .filter_map(|entry| {
                    let path = entry.ok()?.path().to_path_buf();
                    if path.is_file() && path.extension().map_or(false, |ext| ext == "rs") {
                        Some(path)
                    } else {
                        None
                    }
                })
                .par_bridge()
                .for_each(|file| {
                    println!("Formatting file: {}", &file.display());
                    let status = Command::new(&verusfmt)
                        .arg(&file)
                        .status()
                        .expect("Failed to run verusfmt");
                    if !status.success() {
                        eprintln!("Failed to format file: {}, skipping", &file.display());
                    }
                });
        }
    }
    Ok(())
}

fn main() {
    let mut all_targets = get_all_targets();
    all_targets.remove("xtask");

    let cli = Cli::parse();
    if let Err(e) = match &cli.command {
        Commands::Verify(args) => exec_verify(args),
        Commands::Doc(args) => exec_doc(args),
        Commands::Bootstrap(args) => exec_bootstrap(args),
        Commands::Compile(args) => exec_compile(args),
        Commands::Fmt(args) => exec_fmt(args),
        Commands::Update(args) => exec_update(args),
    } {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}
