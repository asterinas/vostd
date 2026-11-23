use crate::verus::{self, DynError, VerusTarget};
use cargo_metadata::{Artifact, DependencyKind, Message, Metadata, MetadataCommand, PackageId};
use colored::Colorize;
use indexmap::IndexMap;
use std::collections::HashSet;
use std::env::consts::DLL_EXTENSION;
use std::io::{BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

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

    let artifacts = build_doc_dependencies(target, rust_target)?;
    let metadata = MetadataCommand::new()
        .other_options(vec!["--filter-platform".into(), rust_target.into()])
        .exec()?;
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
                &artifacts,
                &metadata,
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
        &artifacts,
        &metadata,
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
    artifacts: &[Artifact],
    metadata: &Metadata,
) -> Result<(), DynError> {
    info!(
        "{} {}",
        "Generating docs".bold().blue(),
        target.name.white()
    );

    let mut cmd = Command::new(verus::get_rustdoc());
    cmd.env(
        "VERUSDOC",
        if verus_conds || verus_conds_debug {
            "1"
        } else {
            "0"
        },
    );
    cmd.env("RUSTC_BOOTSTRAP", "1");
    // Proc macros such as Pod use the documented package's identity.
    cmd.env("CARGO_PKG_NAME", &target.name);
    cmd.arg("--target").arg(rust_target);

    let package = metadata
        .packages
        .iter()
        .find(|p| p.name == target.name)
        .ok_or_else(|| format!("Missing Cargo metadata for {}", target.name))?;
    let node = metadata
        .resolve
        .as_ref()
        .and_then(|resolve| resolve.nodes.iter().find(|node| node.id == package.id))
        .ok_or_else(|| format!("Missing dependency graph for {}", target.name))?;
    let mut externs = IndexMap::new();
    for dep in &node.deps {
        if dep
            .dep_kinds
            .iter()
            .any(|kind| kind.kind == DependencyKind::Normal)
        {
            let path = library_for_package(artifacts, &dep.pkg)?;
            externs.insert(dep.name.clone(), path);
        }
    }
    // Verus expands references to these crates even when the source package
    // only declares a dependency on vstd. Use the instances from this build.
    for name in [
        "vstd",
        "verus_builtin",
        "verus_builtin_macros",
        "verus_state_machines_macros",
    ] {
        if !externs.contains_key(name) {
            let artifact = artifacts
                .iter()
                .find(|artifact| artifact.target.name == name)
                .ok_or_else(|| format!("Missing Cargo artifact for {name}"))?;
            externs.insert(
                name.to_owned(),
                library_for_package(artifacts, &artifact.package_id)?,
            );
        }
    }
    for (name, path) in externs {
        cmd.arg("--extern")
            .arg(format!("{name}={}", path.display()));
    }
    let dirs = artifacts
        .iter()
        .filter_map(library_artifact)
        .filter_map(|path| path.parent().map(Path::to_path_buf))
        .collect::<HashSet<_>>();
    let mut dirs = dirs.into_iter().collect::<Vec<_>>();
    dirs.sort();
    for dir in dirs {
        cmd.arg("-L").arg(format!("dependency={}", dir.display()));
    }
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

    // Per-crate dependency paths can exceed Windows' command-line limit.
    // rustdoc accepts one argument per line in an @response file.
    let mut args_file = tempfile::NamedTempFile::new()?;
    for arg in cmd.get_args() {
        writeln!(args_file, "{}", arg.to_string_lossy())?;
    }
    args_file.flush()?;
    let mut invocation = Command::new(cmd.get_program());
    for (key, value) in cmd.get_envs() {
        if let Some(value) = value {
            invocation.env(key, value);
        } else {
            invocation.env_remove(key);
        }
    }
    invocation.arg(format!("@{}", args_file.path().display()));
    let status = verus::run_filtered_command(&mut invocation)?;
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

/// Ask Cargo for this build's artifacts, including cached results.
fn build_doc_dependencies(
    target: &VerusTarget,
    rust_target: &str,
) -> Result<Vec<Artifact>, DynError> {
    let mut cmd = Command::new(verus::get_cargo_verus(true));
    cmd.env("RUSTC_BOOTSTRAP", "1")
        .env("VERUS_Z3_PATH", verus::get_z3())
        .args([
            "build",
            "-p",
            &target.name,
            "--release",
            "--target",
            rust_target,
            "--message-format=json-render-diagnostics",
            "--",
            "--multiple-errors=5",
            "--no-verify",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    info!(
        "Resolving documentation artifacts with Cargo for {}...",
        target.name
    );
    let mut child = cmd.spawn()?;
    let mut artifacts = Vec::new();
    let mut parse_error = None;
    for message in Message::parse_stream(BufReader::new(child.stdout.take().unwrap())) {
        match message {
            Ok(Message::CompilerArtifact(artifact)) => artifacts.push(artifact),
            Ok(Message::CompilerMessage(message)) => {
                if let Some(rendered) = message.message.rendered {
                    eprint!("{rendered}");
                }
            }
            Ok(Message::TextLine(line)) => println!("{line}"),
            Err(err) => {
                parse_error = Some(err);
            }
            _ => {}
        }
    }
    let status = child.wait()?;
    if !status.success() {
        return Err(format!("Documentation dependency build failed for {}", target.name).into());
    }
    if let Some(err) = parse_error {
        return Err(err.into());
    }
    Ok(artifacts)
}

fn library_artifact(artifact: &Artifact) -> Option<PathBuf> {
    if artifact.target.is_proc_macro() {
        artifact
            .filenames
            .iter()
            .find(|path| path.extension() == Some(DLL_EXTENSION))
    } else if artifact.target.is_lib() || artifact.target.is_rlib() {
        artifact
            .filenames
            .iter()
            .find(|path| path.extension() == Some("rlib"))
            .or_else(|| {
                artifact
                    .filenames
                    .iter()
                    .find(|path| path.extension() == Some("rmeta"))
            })
    } else {
        None
    }
    .map(|path| path.clone().into_std_path_buf())
}

fn library_for_package(
    artifacts: &[Artifact],
    package_id: &PackageId,
) -> Result<PathBuf, DynError> {
    let paths = artifacts
        .iter()
        .filter(|artifact| artifact.package_id == *package_id)
        .filter_map(library_artifact)
        .collect::<HashSet<_>>();
    if paths.len() != 1 {
        return Err(format!(
            "Expected one Cargo library artifact for {package_id}, found {}",
            paths.len()
        )
        .into());
    }
    Ok(paths.into_iter().next().unwrap())
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
