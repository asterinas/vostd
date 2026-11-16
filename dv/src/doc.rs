use crate::verus::{self, DynError, VerusTarget};
use cargo_metadata::MetadataCommand;
use colored::Colorize;
use indexmap::IndexMap;
use std::collections::HashSet;
use std::env::consts::{DLL_PREFIX, DLL_SUFFIX};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Generate documentation for verification targets
pub fn exec_doc(
    target: &str,
    verus_conds: bool,
    verus_conds_debug: bool,
    json_output: bool,
    rust_target: &str,
) -> Result<(), DynError> {
    let target_to_use = verus::find_target(target)?;
    generate_docs(
        &target_to_use,
        verus_conds,
        verus_conds_debug,
        json_output,
        rust_target,
    )?;
    Ok(())
}

/// Generate documentation for the target including all its dependencies
fn generate_docs(
    target: &VerusTarget,
    verus_conds: bool,
    verus_conds_debug: bool,
    json_output: bool,
    rust_target: &str,
) -> Result<(), DynError> {
    info!(
        "Generating documentation for {} with all dependencies...",
        target.name
    );

    let root_dir = verus::get_workspace_root();
    let doc_output_dir = root_dir.join("doc");

    std::fs::create_dir_all(&doc_output_dir)?;

    let deps = verus::get_local_dependency(target);

    for (_name, dep_target) in deps.iter() {
        if dep_target.name != target.name {
            generate_single_target_doc(
                dep_target,
                verus_conds,
                verus_conds_debug,
                json_output,
                &doc_output_dir,
                rust_target,
            )?;
        }
    }

    generate_single_target_doc(
        target,
        verus_conds,
        verus_conds_debug,
        json_output,
        &doc_output_dir,
        rust_target,
    )?;

    if verus_conds && !verus_conds_debug {
        run_verusdoc_postprocessor()?;
    }

    info!("{}", "Generation Complete!".bold().green(),);

    Ok(())
}

/// Generate documentation for a single target using rustdoc
fn generate_single_target_doc(
    target: &VerusTarget,
    verus_conds: bool,
    verus_conds_debug: bool,
    json_output: bool,
    doc_output_dir: &Path,
    rust_target: &str,
) -> Result<(), DynError> {
    info!(
        "{} {}",
        "Generating docs".bold().blue(),
        target.name.white()
    );

    let verus_target_dir = verus::get_verus_target_dir();
    let target_dir = verus::get_target_dir();
    let rustdoc = verus::get_rustdoc();

    let mut cmd = Command::new(&rustdoc);

    // Set VERUSDOC environment variable based on verus_conds flags
    let verus_doc_value = if verus_conds || verus_conds_debug {
        "1"
    } else {
        "0"
    };
    cmd.env("VERUSDOC", verus_doc_value);
    cmd.env("RUSTC_BOOTSTRAP", "1");

    // `cargo dv build` builds with `--target <rust_target>`, so the documentation
    // must be generated for the same target triple to use those artifacts as
    // externs. Regular libraries are resolved from the triple-prefixed target
    // directory (falling back to the verus target directory), while proc-macro
    // crates must remain at the host triple since they run during compilation.
    cmd.arg("--target").arg(rust_target);

    // Add extern dependencies for verus_builtin (regular library -> target triple)
    let builtin_path = find_dependency_artifact(&target_dir, "verus_builtin", rust_target)
        .unwrap_or_else(|| verus_target_dir.join("libverus_builtin.rlib"));
    cmd.arg("--extern")
        .arg(format!("verus_builtin={}", builtin_path.display()));

    // Add extern dependencies for verus_builtin_macros (proc-macro -> host triple)
    let builtin_macros_path =
        verus_target_dir.join(format!("{DLL_PREFIX}verus_builtin_macros{DLL_SUFFIX}"));
    cmd.arg("--extern").arg(format!(
        "verus_builtin_macros={}",
        builtin_macros_path.display()
    ));

    // Add extern dependencies for verus_state_machines_macros
    let state_machine_macros_path = verus_target_dir.join(format!(
        "{DLL_PREFIX}verus_state_machines_macros{DLL_SUFFIX}"
    ));
    cmd.arg("--extern").arg(format!(
        "verus_state_machines_macros={}",
        state_machine_macros_path.display()
    ));

    // Prefer the Cargo-built vstd when available so rustdoc uses the same crate
    // instance as built local dependencies.
    let vstd_path = find_dependency_artifact(&target_dir, "vstd", rust_target)
        .unwrap_or_else(|| verus_target_dir.join("libvstd.rlib"));
    cmd.arg("--extern")
        .arg(format!("vstd={}", vstd_path.display()));

    // Add dependencies that this target actually needs
    let deps = verus::get_local_dependency(target);
    for (_name, dep_target) in deps.iter() {
        if dep_target.crate_name != target.crate_name {
            if let Some(rlib_path) =
                find_local_dependency_rlib(&target_dir, &dep_target.crate_name, rust_target)
            {
                cmd.arg("--extern").arg(format!(
                    "{}={}",
                    dep_target.crate_name,
                    rlib_path.display()
                ));
            } else {
                return Err(format!(
                    "Missing built dependency '{}' for target '{}'.\n\nPlease run:\n  cargo dv build --package {} --target {}",
                    dep_target.name, target.name, dep_target.name, rust_target
                ).into());
            }
        }
    }

    let remote_deps = verus::get_remote_dependency(target, false, rust_target)
        .into_iter()
        .map(|(name, path)| {
            if let Some(base) = path.strip_suffix(".rmeta") {
                let rlib_path = format!("{base}.rlib");
                if Path::new(&rlib_path).exists() {
                    return (name, rlib_path);
                }
            }
            (name, path)
        })
        .collect::<IndexMap<_, _>>();
    verus::check_externs(&remote_deps)?;
    verus::cmd_push_externs(&mut cmd, &remote_deps);
    let mut pushed_externs = remote_deps.keys().cloned().collect::<HashSet<_>>();

    for (extern_name, artifact_name) in direct_cargo_dependencies(&target.name)? {
        if pushed_externs.contains(&extern_name) {
            continue;
        }
        if let Some(path) = find_dependency_artifact(&target_dir, &artifact_name, rust_target) {
            cmd.arg("--extern")
                .arg(format!("{}={}", extern_name, path.display()));
            pushed_externs.insert(extern_name);
        }
    }

    // `cargo dv build` passes `--target <rust_target>`, so the built artifacts
    // live under the triple-prefixed directories. Search those first and keep
    // the bare `target/release` and `target/debug` directories as a fallback for
    // artifacts built without an explicit target (e.g. the `dv` crate's own
    // dependencies).
    for deps_dir in [
        target_dir.join(rust_target).join("release").join("deps"),
        target_dir.join(rust_target).join("debug").join("deps"),
        target_dir.join("release").join("deps"),
        target_dir.join("debug").join("deps"),
    ] {
        cmd.arg("-L")
            .arg(format!("dependency={}", deps_dir.display()));
    }
    cmd.arg("-L").arg(format!("{}", verus_target_dir.display()));
    cmd.arg("-L").arg(format!("{}", target_dir.display()));
    cmd.arg("--edition=2021")
        .arg("--cfg")
        .arg("verus_keep_ghost")
        .arg("--cfg")
        .arg("verus_keep_ghost_body")
        .arg("--cfg")
        .arg("feature=\"std\"")
        .arg("--cfg")
        .arg("feature=\"alloc\"")
        .arg("-Zcrate-attr=feature(stmt_expr_attributes)")
        .arg("-Zcrate-attr=feature(register_tool)")
        .arg("-Zcrate-attr=register_tool(verus)")
        .arg("-Zcrate-attr=register_tool(verifier)")
        .arg("-Zcrate-attr=register_tool(verusfmt)")
        .arg("-Zcrate-attr=feature(rustc_attrs)")
        .arg("-Zcrate-attr=feature(portable_simd)")
        .arg("-Zcrate-attr=feature(negative_impls)")
        .arg("--enable-index-page")
        .arg("-Zunstable-options");

    // Set crate type and name
    cmd.arg("--crate-type=lib")
        .arg(format!("--crate-name={}", target.crate_name));

    if json_output {
        cmd.arg("--output-format").arg("json");
    }

    // Set output directory
    cmd.arg("-o").arg(&doc_output_dir);

    // Add the source file
    let source_file = target.root_file();
    cmd.arg(&source_file);

    debug!("Running rustdoc for {}: {:?}", target.name, cmd);

    let status = verus::run_filtered_command(&mut cmd)?;
    if !status.success() {
        return Err(format!("rustdoc failed for target: {}", target.name).into());
    }

    info!(
        "{} {} {}",
        "Generated docs for".bold().green(),
        target.name.white(),
        "successfully".green()
    );

    Ok(())
}

fn direct_cargo_dependencies(package_name: &str) -> Result<Vec<(String, String)>, DynError> {
    let metadata = MetadataCommand::new().exec()?;
    let workspace_packages = metadata
        .workspace_members
        .iter()
        .filter_map(|id| metadata.packages.iter().find(|package| package.id == *id))
        .map(|package| package.name.replace('-', "_"))
        .collect::<HashSet<_>>();

    let Some(package) = metadata
        .packages
        .iter()
        .find(|package| package.name == package_name)
    else {
        return Ok(Vec::new());
    };

    Ok(package
        .dependencies
        .iter()
        .filter(|dep| matches!(dep.kind, cargo_metadata::DependencyKind::Normal))
        .filter_map(|dep| {
            let extern_name = dep.rename.as_ref().unwrap_or(&dep.name).replace('-', "_");
            let artifact_name = dep.name.replace('-', "_");
            if workspace_packages.contains(&artifact_name)
                || verus::system_crates().contains(extern_name.as_str())
            {
                None
            } else {
                Some((extern_name, artifact_name))
            }
        })
        .collect())
}

fn find_local_dependency_rlib(target_dir: &Path, dep_name: &str, triple: &str) -> Option<PathBuf> {
    let extern_name = dep_name.replace('-', "_");
    let unversioned = format!("lib{extern_name}.rlib");
    let hashed_prefix = format!("lib{extern_name}-");

    let exact_candidates = [
        target_dir.join(triple).join("release").join(&unversioned),
        target_dir.join(triple).join("debug").join(&unversioned),
        target_dir.join(&unversioned),
        target_dir.join("release").join(&unversioned),
        target_dir.join("debug").join(&unversioned),
    ];
    for candidate in exact_candidates {
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let deps_dirs = [
        target_dir.join(triple).join("release").join("deps"),
        target_dir.join(triple).join("debug").join("deps"),
        target_dir.join("release").join("deps"),
        target_dir.join("debug").join("deps"),
    ];
    for deps_dir in deps_dirs {
        if let Some(path) = newest_matching_artifact(&deps_dir, &hashed_prefix, ".rlib") {
            return Some(path);
        }
    }

    None
}

fn find_dependency_artifact(target_dir: &Path, crate_name: &str, triple: &str) -> Option<PathBuf> {
    find_hashed_artifact(target_dir, crate_name, "rlib", triple)
        .or_else(|| find_hashed_artifact(target_dir, crate_name, "rmeta", triple))
}

fn find_hashed_artifact(
    target_dir: &Path,
    crate_name: &str,
    extension: &str,
    triple: &str,
) -> Option<PathBuf> {
    let prefix = format!("lib{}-", crate_name.replace('-', "_"));
    let suffix = format!(".{extension}");
    for deps_dir in [
        target_dir.join(triple).join("release").join("deps"),
        target_dir.join(triple).join("debug").join("deps"),
        target_dir.join("release").join("deps"),
        target_dir.join("debug").join("deps"),
    ] {
        if let Some(path) = newest_matching_artifact(&deps_dir, &prefix, &suffix) {
            return Some(path);
        }
    }

    None
}

fn newest_matching_artifact(dir: &Path, prefix: &str, suffix: &str) -> Option<PathBuf> {
    std::fs::read_dir(dir)
        .ok()?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .map(|name| name.starts_with(prefix) && name.ends_with(suffix))
                .unwrap_or(false)
        })
        .max_by_key(|path| {
            path.metadata()
                .and_then(|metadata| metadata.modified())
                .ok()
        })
}

fn run_verusdoc_postprocessor() -> Result<(), DynError> {
    let verusdoc = verus::get_verusdoc();

    info!("Running verusdoc post-processor...");
    let status = Command::new(&verusdoc).status()?;

    if !status.success() {
        warn!("verusdoc post-processor failed");
    } else {
        info!("verusdoc post-processor completed successfully");
    }

    Ok(())
}
