use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::verus::{self, get_target_dir, get_workspace_root, DynError, VerusTarget};

fn dep_info_dirs(target_dir: &Path, rust_target: &str) -> Vec<PathBuf> {
    [target_dir.join("verus-partial"), target_dir.to_path_buf()]
        .into_iter()
        .flat_map(|base| {
            ["debug", "release"]
                .into_iter()
                .map(move |profile| base.join(rust_target).join(profile).join("deps"))
        })
        .collect()
}

fn dep_info_source_root(
    dep_info: &Path,
    target: &VerusTarget,
    workspace_root: &Path,
) -> Option<PathBuf> {
    let first_line = BufReader::new(File::open(dep_info).ok()?)
        .lines()
        .next()?
        .ok()?;
    let target_file = target.file.canonicalize().ok()?;

    for root in [workspace_root, target.dir.as_path()] {
        if first_line
            .split_whitespace()
            .skip(1)
            .map(|dependency| dependency.trim_end_matches('\\'))
            .map(Path::new)
            .map(|dependency| {
                if dependency.is_absolute() {
                    dependency.to_path_buf()
                } else {
                    root.join(dependency)
                }
            })
            .filter_map(|dependency| dependency.canonicalize().ok())
            .any(|dependency| dependency == target_file)
        {
            return Some(root.to_path_buf());
        }
    }

    None
}

fn find_dep_info(target: &VerusTarget, rust_target: &str) -> Option<(PathBuf, PathBuf)> {
    let target_dir = get_target_dir();
    let workspace_root = get_workspace_root();

    dep_info_dirs(&target_dir, rust_target)
        .into_iter()
        .filter_map(|dir| fs::read_dir(dir).ok())
        .flatten()
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| path.extension() == Some(OsStr::new("d")))
        .filter_map(|path| {
            let source_root = dep_info_source_root(&path, target, &workspace_root)?;
            let modified = path.metadata().ok()?.modified().ok()?;
            Some((modified, path, source_root))
        })
        .max_by_key(|(modified, _, _)| *modified)
        .map(|(_, path, source_root)| (path, source_root))
}

struct TemporaryDepInfo {
    path: PathBuf,
}

impl TemporaryDepInfo {
    fn copy_into(source: &Path, root: &Path, crate_name: &str) -> Result<Self, DynError> {
        for suffix in 0..100 {
            let path = root.join(format!(
                ".dv-line-count-{}-{}-{}.d",
                crate_name,
                std::process::id(),
                suffix
            ));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(mut destination) => {
                    let temporary_dep_info = Self { path };
                    let mut source = File::open(source)?;
                    std::io::copy(&mut source, &mut destination)?;
                    return Ok(temporary_dep_info);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }

        Err(format!(
            "failed to create a temporary dep-info file in {}",
            root.display()
        )
        .into())
    }
}

impl Drop for TemporaryDepInfo {
    fn drop(&mut self) {
        if let Err(error) = fs::remove_file(&self.path) {
            warn!(
                "Failed to remove temporary dep-info file {}: {}",
                self.path.display(),
                error
            );
        }
    }
}

fn line_count_command(print_all: bool) -> Command {
    let mut command = Command::new("cargo");
    command
        .current_dir(verus::install::verus_dir().join("source/tools/line_count"))
        .arg("run")
        .arg("--release")
        .arg("--");
    if print_all {
        command.arg("--print-all");
    }
    command
}

fn run_line_count(
    target: &VerusTarget,
    print_all: bool,
    rust_target: &str,
) -> Result<(), DynError> {
    let (dep_info, source_root) = find_dep_info(target, rust_target).ok_or_else(|| {
        format!(
            "could not find cargo-verus dep-info for target {} under {}; run `cargo dv verify --package {}` first",
            target.name,
            get_target_dir().display(),
            target.name
        )
    })?;
    let temporary_dep_info = TemporaryDepInfo::copy_into(&dep_info, &source_root, &target.name)?;
    println!("Counting lines for {}", target.name);
    let status = line_count_command(print_all)
        .arg("--deps")
        .arg(&temporary_dep_info.path)
        .status()?;
    if !status.success() {
        return Err(format!("line_count failed for target {}", target.name).into());
    }

    Ok(())
}

fn available_child_modules(source: &str) -> Vec<String> {
    let Ok(file) = syn::parse_file(source) else {
        return Vec::new();
    };
    let mut modules = file
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Mod(module) if module.content.is_none() => Some(module.ident.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>();
    modules.sort();
    modules.dedup();
    modules
}

fn available_modules_message(source: &str, resolved: &[&str]) -> String {
    let modules = available_child_modules(source);
    if modules.is_empty() {
        return String::new();
    }

    let prefix = if resolved.is_empty() {
        String::new()
    } else {
        format!("{}::", resolved.join("::"))
    };
    format!(
        "; available modules:\n{}",
        modules
            .iter()
            .map(|module| format!("  {prefix}{module}"))
            .collect::<Vec<_>>()
            .join("\n")
    )
}

/// The `target_arch` cfg value that `ostd` uses to select an architecture module
/// for a Rust target triple. Mirrors the `cfg(target_arch = ...)` mounts in
/// `ostd/src/lib.rs`.
fn target_arch_for(rust_target: &str) -> &'static str {
    match rust_target.split('-').next().unwrap_or_default() {
        "riscv64imac" | "riscv64gc" => "riscv64",
        "loongarch64" => "loongarch64",
        _ => "x86_64",
    }
}

/// Find the `#[path]` attribute that declares `mod <segment>` for `rust_target`.
///
/// A module may be declared several times under different `cfg`s, as the arch
/// mounts in `ostd/src/lib.rs` are. The declaration whose `cfg(target_arch)`
/// matches the target wins; a declaration without a `cfg` is the fallback.
fn path_attribute_for(
    source: &str,
    segment: &str,
    rust_target: &str,
) -> Result<Option<String>, DynError> {
    let declaration = regex::Regex::new(&format!(
        r#"(?s)((?:#\s*\[[^\]]*\]\s*)*)#\s*\[\s*path\s*=\s*"([^"]+)"\s*\](?:\s*#\s*\[[^\]]*\])*\s*(?:pub(?:\s*\([^)]*\))?\s+)?mod\s+{}\s*;"#,
        regex::escape(segment)
    ))?;
    let arch = target_arch_for(rust_target);
    let mut fallback = None;
    for captures in declaration.captures_iter(source) {
        let attributes = captures.get(1).map_or("", |m| m.as_str());
        let path = captures[2].to_string();
        match cfg_target_arch(attributes) {
            Some(cfg_arch) if cfg_arch == arch => return Ok(Some(path)),
            Some(_) => {}
            None => fallback = fallback.or(Some(path)),
        }
    }
    Ok(fallback)
}

/// The `target_arch` named by the last `cfg(target_arch = "...")` in `attributes`,
/// if any. Only the attributes immediately preceding a declaration are passed in.
fn cfg_target_arch(attributes: &str) -> Option<String> {
    let cfg =
        regex::Regex::new(r#"#\s*\[\s*cfg\s*\(\s*target_arch\s*=\s*"([^"]+)"\s*\)\s*\]"#).ok()?;
    cfg.captures_iter(attributes)
        .last()
        .map(|captures| captures[1].to_string())
}

fn module_source_paths(
    crate_root: &Path,
    module: &str,
    rust_target: &str,
) -> Result<Vec<PathBuf>, DynError> {
    let segments = module
        .split("::")
        .map(|segment| segment.strip_prefix("r#").unwrap_or(segment))
        .collect::<Vec<_>>();
    if segments.is_empty()
        || segments.iter().any(|segment| {
            segment.is_empty()
                || !segment
                    .chars()
                    .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
        })
    {
        return Err(format!("invalid Rust module path `{module}`").into());
    }

    let mut current = crate_root.canonicalize()?;
    for (index, segment) in segments.iter().enumerate() {
        let parent = current
            .parent()
            .ok_or_else(|| format!("crate root {} has no parent", current.display()))?;
        let source = fs::read_to_string(&current)?;
        if let Some(path) = path_attribute_for(&source, segment, rust_target)? {
            let path = parent.join(path);
            if !path.is_file() {
                return Err(format!(
                    "module `{module}` has #[path = {:?}], but {} is not a file",
                    path.as_os_str(),
                    path.display()
                )
                .into());
            }
            current = path.canonicalize()?;
            continue;
        }
        let file_name = current
            .file_name()
            .and_then(OsStr::to_str)
            .unwrap_or_default();
        let base = if matches!(file_name, "lib.rs" | "main.rs" | "mod.rs") {
            parent.to_path_buf()
        } else {
            parent.join(current.file_stem().unwrap_or_default())
        };
        let file_candidate = base.join(segment).with_extension("rs");
        let mod_candidate = base.join(segment).join("mod.rs");
        current = match (file_candidate.is_file(), mod_candidate.is_file()) {
            (true, false) => file_candidate,
            (false, true) => mod_candidate,
            (false, false) => {
                return Err(format!(
                    "could not resolve module `{module}`: expected {} or {}{}",
                    file_candidate.display(),
                    mod_candidate.display(),
                    available_modules_message(&source, &segments[..index])
                )
                .into());
            }
            (true, true) => {
                return Err(format!(
                    "module `{module}` is ambiguous: both {} and {} exist",
                    file_candidate.display(),
                    mod_candidate.display()
                )
                .into());
            }
        };
    }

    if current.file_name() == Some(OsStr::new("mod.rs")) {
        return Ok(vec![current.parent().unwrap().to_path_buf()]);
    }

    let mut paths = vec![current.clone()];
    let child_modules = current
        .parent()
        .unwrap()
        .join(current.file_stem().unwrap_or_default());
    if child_modules.is_dir() {
        paths.push(child_modules);
    }
    Ok(paths)
}

fn run_module_line_count(
    target: &VerusTarget,
    module: &str,
    print_all: bool,
    rust_target: &str,
) -> Result<(), DynError> {
    let module = module
        .strip_prefix(&format!("{}::", target.crate_name))
        .or_else(|| module.strip_prefix(&format!("{}::", target.name)))
        .unwrap_or(module);
    let paths = module_source_paths(&target.file, module, rust_target)?;

    println!("Counting lines for {} module {}", target.name, module);
    let status = line_count_command(print_all).args(&paths).status()?;
    if !status.success() {
        return Err(format!("line_count failed for {} module {}", target.name, module).into());
    }
    Ok(())
}

pub fn exec_count(
    targets: &[VerusTarget],
    module: Option<&str>,
    print_all: bool,
    rust_target: &str,
) -> Result<(), DynError> {
    if module.is_some() && targets.len() != 1 {
        return Err("--module requires exactly one --package value".into());
    }

    let mut count_targets = if targets.is_empty() {
        verus::verus_targets().into_values().collect::<Vec<_>>()
    } else {
        targets.to_vec()
    };
    count_targets.sort_by(|left, right| left.name.cmp(&right.name));

    for target in &count_targets {
        if let Some(module) = module {
            run_module_line_count(target, module, print_all, rust_target)?;
        } else {
            run_line_count(target, print_all, rust_target)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_a_leaf_module_to_its_source_file() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("sync")).unwrap();
        fs::write(src.join("lib.rs"), "mod sync;\n").unwrap();
        fs::write(src.join("sync/mod.rs"), "mod rwlock;\n").unwrap();
        fs::write(src.join("sync/rwlock.rs"), "struct RwLock;\n").unwrap();

        let paths = module_source_paths(&src.join("lib.rs"), "sync::rwlock", "x86_64-unknown-none")
            .unwrap();
        assert_eq!(paths, [src.join("sync/rwlock.rs")]);
    }

    #[test]
    fn resolves_a_parent_module_to_its_source_tree() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("sync")).unwrap();
        fs::write(src.join("lib.rs"), "mod sync;\n").unwrap();
        fs::write(src.join("sync/mod.rs"), "mod rwlock;\n").unwrap();
        fs::write(src.join("sync/rwlock.rs"), "struct RwLock;\n").unwrap();

        let paths =
            module_source_paths(&src.join("lib.rs"), "sync", "x86_64-unknown-none").unwrap();
        assert_eq!(paths, [src.join("sync")]);
    }

    #[test]
    fn resolves_a_module_with_a_path_attribute() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("arch/x86")).unwrap();
        fs::write(
            src.join("lib.rs"),
            "#[path = \"arch/x86/mod.rs\"]\npub mod arch;\n",
        )
        .unwrap();
        fs::write(src.join("arch/x86/mod.rs"), "mod irq;\n").unwrap();
        fs::write(src.join("arch/x86/irq.rs"), "fn enable() {}\n").unwrap();

        let paths =
            module_source_paths(&src.join("lib.rs"), "arch::irq", "x86_64-unknown-none").unwrap();
        assert_eq!(paths, [src.join("arch/x86/irq.rs")]);
    }

    #[test]
    fn selects_the_path_attribute_matching_the_rust_target() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("arch/x86")).unwrap();
        fs::create_dir_all(src.join("arch/riscv")).unwrap();
        fs::write(
            src.join("lib.rs"),
            "#[cfg(target_arch = \"x86_64\")]\n#[path = \"arch/x86/mod.rs\"]\npub mod arch;\n\
             #[cfg(target_arch = \"riscv64\")]\n#[path = \"arch/riscv/mod.rs\"]\npub mod arch;\n",
        )
        .unwrap();
        fs::write(src.join("arch/x86/mod.rs"), "mod irq;\n").unwrap();
        fs::write(src.join("arch/x86/irq.rs"), "fn enable() {}\n").unwrap();
        fs::write(src.join("arch/riscv/mod.rs"), "mod irq;\n").unwrap();
        fs::write(src.join("arch/riscv/irq.rs"), "fn enable() {}\n").unwrap();

        let riscv = module_source_paths(
            &src.join("lib.rs"),
            "arch::irq",
            "riscv64imac-unknown-none-elf",
        )
        .unwrap();
        assert_eq!(riscv, [src.join("arch/riscv/irq.rs")]);

        let x86 =
            module_source_paths(&src.join("lib.rs"), "arch::irq", "x86_64-unknown-none").unwrap();
        assert_eq!(x86, [src.join("arch/x86/irq.rs")]);
    }

    #[test]
    fn unresolved_module_lists_available_module_paths() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("sync")).unwrap();
        fs::write(
            src.join("lib.rs"),
            "mod sync;\n// mod commented_out;\nmod task;\n",
        )
        .unwrap();
        fs::write(src.join("sync/mod.rs"), "mod rwlock;\n").unwrap();

        let error = module_source_paths(&src.join("lib.rs"), "sy", "x86_64-unknown-none")
            .unwrap_err()
            .to_string();
        assert!(error.contains("available modules:\n  sync\n  task"));
        assert!(!error.contains("commented_out"));
    }

    #[test]
    fn unresolved_nested_module_lists_qualified_paths() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        fs::create_dir_all(src.join("sync")).unwrap();
        fs::write(src.join("lib.rs"), "mod sync;\n").unwrap();
        fs::write(src.join("sync/mod.rs"), "mod mutex;\nmod rwlock;\n").unwrap();

        let error = module_source_paths(&src.join("lib.rs"), "sync::rw", "x86_64-unknown-none")
            .unwrap_err()
            .to_string();
        assert!(error.contains("available modules:\n  sync::mutex\n  sync::rwlock"));
    }
}
