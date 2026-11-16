use crate::{executable, projects};
use colored::Colorize;
use indexmap::IndexMap;
use memoize::memoize;
use serde_json::Value;
use std::collections::HashMap;
use std::env::consts::DLL_SUFFIX;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;

use regex::Regex;

pub fn cargo_install(package: &str) {
    Command::new("cargo")
        .arg("install")
        .arg(package)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .expect("Failed to install package")
        .wait()
        .expect("Failed to wait for command");
}

#[derive(Clone, Debug)]
pub struct ExecutionResult {
    pub status: std::process::ExitStatus,
    pub stdout: String,
    pub stderr: String,
}

pub fn run_capture(cmd: &mut Command) -> ExecutionResult {
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());
    debug!(">> {:?}", cmd);
    let result = cmd.spawn().unwrap_or_else(|e| {
        fatal!("Unable to spawn command {:?}: {}", cmd, e);
    });
    let output = result.wait_with_output().unwrap_or_else(|e| {
        fatal!("Unable to wait for command {:?}: {}", cmd, e);
    });
    let status = output.status;
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    ExecutionResult {
        status,
        stdout,
        stderr,
    }
}

pub fn run_panic(cmd: &mut Command) {
    cmd.stdout(Stdio::inherit()).stderr(Stdio::inherit());

    debug!(">> {:?}", cmd);
    cmd.spawn()
        .unwrap_or_else(|e| {
            fatal!("Unable to spawn command {:?}: {}", cmd, e);
        })
        .wait()
        .unwrap_or_else(|e| {
            fatal!("Unable to wait for command {:?}: {}", cmd, e);
        });
}

pub fn run_status(cmd: &mut Command) -> i32 {
    cmd.stdout(Stdio::inherit()).stderr(Stdio::inherit());
    debug!(">> {:?}", cmd);
    cmd.spawn()
        .unwrap_or_else(|e| {
            error!("Unable to spawn command {:?}: {}", cmd, e);
        })
        .wait()
        .unwrap_or_else(|e| {
            error!("Unable to wait for command {:?}: {}", cmd, e);
        })
        .code()
        .unwrap_or_else(|| {
            warn!("Command {:?} failed to return a status code", cmd);
            -1
        })
}

#[derive(Debug, Clone, Copy)]
pub enum StreamType {
    Stdout,
    Stderr,
}

pub fn run_process_capture<F>(cmd: &mut Command, processor: F) -> ExecutionResult
where
    F: Fn(&str, StreamType) + Send + Sync + 'static,
{
    let mut child = cmd
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| {
            fatal!("Unable to spawn command {:?}: {}", cmd, e);
        });

    debug!(">> {:?}", cmd);

    // Take ownership of the child's stdout and stderr pipes
    let child_stdout = child
        .stdout
        .take()
        .expect("Internal error, could not take stdout");
    let child_stderr = child
        .stderr
        .take()
        .expect("Internal error, could not take stderr");

    // Create channels to collect output from threads
    let (stdout_tx, stdout_rx) = mpsc::channel();
    let (stderr_tx, stderr_rx) = mpsc::channel();

    // Wrap the processor in Arc to share between threads
    let processor = Arc::new(processor);
    let stdout_processor = Arc::clone(&processor);
    let stderr_processor = Arc::clone(&processor);

    // Spawn thread to handle stdout
    let stdout_thread = thread::spawn(move || {
        let stdout_reader = BufReader::new(child_stdout);
        for line in stdout_reader.lines() {
            match line {
                Ok(line) => {
                    stdout_processor(&line, StreamType::Stdout); // Process with custom function
                    if stdout_tx.send(line).is_err() {
                        break; // Channel closed
                    }
                }
                Err(_) => break,
            }
        }
    });

    // Spawn thread to handle stderr
    let stderr_thread = thread::spawn(move || {
        let stderr_reader = BufReader::new(child_stderr);
        for line in stderr_reader.lines() {
            match line {
                Ok(line) => {
                    stderr_processor(&line, StreamType::Stderr); // Process with custom function
                    if stderr_tx.send(line).is_err() {
                        break; // Channel closed
                    }
                }
                Err(_) => break,
            }
        }
    });

    // Wait for the child process to complete
    let status = child.wait().unwrap_or_else(|e| {
        fatal!("Unable to wait for command {:?}: {}", cmd, e);
    });

    // Wait for threads to finish
    stdout_thread.join().unwrap();
    stderr_thread.join().unwrap();

    println!("");
    // Collect all captured output
    let stdout = stdout_rx.into_iter().collect::<Vec<String>>().join("\n");
    let stderr = stderr_rx.into_iter().collect::<Vec<String>>().join("\n");

    ExecutionResult {
        status,
        stdout,
        stderr,
    }
}

pub fn run_show_capture(cmd: &mut Command) -> ExecutionResult {
    run_process_capture(cmd, |line, st| match st {
        StreamType::Stdout => {
            println!("{}", line);
            std::io::stdout().flush().unwrap();
        }
        StreamType::Stderr => {
            eprintln!("{}", line);
            std::io::stderr().flush().unwrap();
        }
    })
}

pub fn run_dots_capture(cmd: &mut Command) -> ExecutionResult {
    run_process_capture(cmd, |_line, _st| {
        print!(".");
        std::io::stdout().flush().unwrap();
    })
}

pub fn run_build_log_capture(cmd: &mut Command) -> ExecutionResult {
    run_process_capture(cmd, |line, st| {
        match st {
            StreamType::Stdout => {
                let msg = serde_json::from_str::<Value>(line);
                if let Ok(msg) = msg {
                    if msg["reason"] == "compiler-artifact" {
                        let name = msg["target"]["name"].as_str().unwrap_or("unknown");
                        // extract version from `package_id` if available, e.g., xxx@1.0.0
                        let version = msg["package_id"]
                            .as_str()
                            .and_then(|id| id.split('@').nth(1))
                            .unwrap_or("0.0.0");
                        println!(
                            "  {} {} {}",
                            "Compiling".bright_green(),
                            name.bright_black(),
                            version.bright_black()
                        );
                    }
                }
            }
            _ => {}
        }
    })
}

#[derive(Clone, Debug)]
pub struct DependentLibrary {
    pub id: String,
    pub kind: String,
    pub name: String,
    pub release: bool,
    pub lib_path: String,
}

#[derive(Clone, Debug)]
pub struct CargoBuildExterns {
    pub deps_ready: bool,
    /// package_id ==> dependent_library
    pub libraries: IndexMap<String, DependentLibrary>,
    /// package name ==> library file path
    pub last_level: IndexMap<String, String>,
}

impl Default for CargoBuildExterns {
    fn default() -> Self {
        CargoBuildExterns {
            deps_ready: true,
            libraries: IndexMap::new(),
            last_level: IndexMap::new(),
        }
    }
}

impl CargoBuildExterns {
    pub fn new(deps_ready: bool) -> Self {
        CargoBuildExterns {
            deps_ready,
            libraries: IndexMap::new(),
            last_level: IndexMap::new(),
        }
    }

    pub fn full(&self) -> IndexMap<String, String> {
        let mut full = IndexMap::new();
        for (_, dep) in self.libraries.iter() {
            full.insert(dep.name.clone(), dep.lib_path.clone());
        }
        full.extend(self.last_level.clone());
        full
    }

    pub fn parse_from_build_log(crate_name: &str, stdout: &str, stderr: &str) -> Self {
        let mut cargo_build = CargoBuildExterns::new(true);
        cargo_build.parse_library(stdout);
        cargo_build.parse_last_level(crate_name, stderr);
        cargo_build
    }

    pub fn parse_last_level(&mut self, crate_name: &str, stderr: &str) {
        let rustc_regex =
            Regex::new(r"^\s+Running\s+`.*rustc\s+.*--crate-name\s+(\S+)\s+.*$").unwrap();
        let extern_regex = Regex::new(r"--extern\s+([^=\s]+)=([^\s]+)").unwrap();

        for line in stderr.lines() {
            if let Some(caps) = rustc_regex.captures(line) {
                let line_crate = caps.get(1).unwrap().as_str();
                if line_crate != crate_name {
                    continue;
                }
            }

            for cap in extern_regex.captures_iter(line) {
                let name = cap.get(1).unwrap().as_str();
                let path = cap.get(2).unwrap().as_str();
                self.last_level.insert(name.to_string(), path.to_string());
            }
        }
    }

    pub fn parse_library(&mut self, stdout: &str) {
        for msg in stdout
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        {
            let reason = msg["reason"].as_str();
            match &reason {
                Some("compiler-artifact") => {
                    let package_id = msg["package_id"].as_str().unwrap_or_default();
                    let target = &msg["target"];
                    let kind: &str = if target["kind"].as_array().map_or(false, |arr| {
                        arr.iter().filter_map(|k| k.as_str()).any(|s| s == "bin")
                    }) {
                        "bin"
                    } else {
                        "lib"
                    };
                    let name = target["name"].as_str().unwrap();
                    let release = !msg["profile"]["opt_level"]
                        .as_str()
                        .map_or(false, |s| s == "0");
                    let files = msg["filenames"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .filter_map(|f| f.as_str())
                        .collect::<Vec<_>>();
                    let lib_path = files
                        .iter()
                        .find(|f| f.ends_with(".rmeta"))
                        .or_else(|| files.iter().find(|f| f.ends_with(".rlib")))
                        .or_else(|| files.iter().find(|f| f.ends_with(".cdylib")))
                        .or_else(|| files.iter().find(|f| f.ends_with(DLL_SUFFIX)))
                        .unwrap_or(&files[0])
                        .to_string();
                    let dep = DependentLibrary {
                        id: package_id.to_string(),
                        kind: kind.to_string(),
                        name: name.to_string(),
                        release,
                        lib_path: lib_path.to_owned(),
                    };
                    self.libraries.insert(lib_path, dep);
                }
                _ => continue,
            }
        }
    }
}

/// Run `cargo build` for the given package to resolve dependencies.
/// The dependencies are required to be successfully built.
/// But the package itself is not required to be built.
pub fn cargo_build_resolve_deps(
    package: &str,
    crate_name: &str,
    env: &HashMap<String, String>,
    release: bool,
    rust_target: &str,
) -> CargoBuildExterns {
    let mut cmd = Command::new("cargo");
    for (env_key, env_value) in env {
        cmd.env(env_key, env_value);
    }

    cmd.arg("build")
        .arg("--verbose")
        .arg("--keep-going")
        .arg("--package")
        .arg(package)
        .arg("--message-format")
        .arg("json-render-diagnostics");
    if release {
        cmd.arg("--release");
    }
    // Resolve dependencies for the same Rust target triple that
    // `cargo dv build`/`cargo dv verify` use, so the recorded extern paths are
    // compatible with rustdoc when generating docs for that target.
    cmd.arg("--target").arg(rust_target);

    let res = run_build_log_capture(&mut cmd);
    CargoBuildExterns::parse_from_build_log(crate_name, res.stdout.as_str(), res.stderr.as_str())
}

pub fn cargo_build(package: &str, env: &HashMap<String, String>, release: bool) {
    let mut cmd = Command::new("cargo");
    for (env_key, env_value) in env {
        cmd.env(env_key, env_value);
    }

    cmd.arg("build").arg("--package").arg(package);
    if release {
        cmd.arg("--release");
    }

    run_panic(&mut cmd);
}

pub fn cargo_build_with_manifest(package: &str, manifest: &str, bin: &[&str], release: bool) {
    let mut cmd = Command::new("cargo");
    cmd.arg("build")
        .arg("--manifest-path")
        .arg(manifest)
        .arg("--package")
        .arg(package);

    if release {
        cmd.arg("--release");
    }

    if bin.is_empty() {
        cmd.arg("--all");
    } else {
        for b in bin {
            cmd.arg("--bin").arg(b);
        }
    }
    run_panic(&mut cmd);
}

#[cfg(target_os = "windows")]
const RUSTFILT_BIN: &str = "rustfilt.exe";
#[cfg(not(target_os = "windows"))]
const RUSTFILT_BIN: &str = "rustfilt";

#[memoize]
pub fn get_rustfilt() -> PathBuf {
    let rustfilt = executable::locate(RUSTFILT_BIN, None, &[] as &[&str]);
    match rustfilt {
        Some(path) => path,
        None => {
            cargo_install("rustfilt");
            executable::locate(
                    RUSTFILT_BIN,
                    None,
                    &[] as &[&str]
                ).unwrap_or_else(|| {
                    error!("Cannot find the rustfilt binary, please install it using `cargo install rustfilt`");
                })
        }
    }
}

#[cfg(target_os = "windows")]
const OBJDUMP_BIN: &str = "objdump.exe";
#[cfg(not(target_os = "windows"))]
const OBJDUMP_BIN: &str = "llvm-objdump";

#[memoize]
pub fn get_objdump() -> PathBuf {
    let objdump = executable::locate(OBJDUMP_BIN, None, &[] as &[&str]);
    match objdump {
        Some(path) => path,
        None => {
            cargo_install("cargo-binutils");
            executable::locate(
                    OBJDUMP_BIN,
                    None,
                    &[] as &[&str]
                ).unwrap_or_else(|| {
                    error!("Cannot find the objdump binary, please install it using `cargo install cargo-binutils`");
                })
        }
    }
}

pub fn is_patch_applied(dir: &Path, patch: &Path) -> bool {
    let cmd = &mut Command::new("git");
    cmd.current_dir(dir)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .arg("apply")
        .arg("--reverse")
        .arg("--check")
        .arg(patch);
    let status = cmd.status().unwrap_or_else(|e| {
        fatal!(
            "Unable to check if patch {} is applied to {}: {}",
            patch.display(),
            dir.display(),
            e
        );
    });
    status.success()
}

pub fn apply_patch(dir: &Path, patch: &Path) {
    let cmd = &mut Command::new("git");
    cmd.current_dir(dir).arg("apply").arg(patch);
    let status = cmd.status().unwrap_or_else(|e| {
        fatal!(
            "Unable to apply patch {} to {}: {}",
            patch.display(),
            dir.display(),
            e
        );
    });
    if !status.success() {
        fatal!(
            "Unable to apply patch {} to {}",
            patch.display(),
            dir.display()
        );
    }
}

#[memoize]
pub fn get_dummy_rustc(release: bool) -> PathBuf {
    let dummy = projects::get_dummy_rustc(release);
    let dummy_dir = dummy.parent().unwrap();
    let dummy_rustc = executable::locate("dummy-rustc", None, &[dummy_dir]);

    let manifest = projects::get_root().join("xtask").join("Cargo.toml");

    if dummy_rustc.is_none() {
        cargo_build_with_manifest(
            "xtask",
            manifest.to_str().unwrap(),
            &["dummy-rustc"],
            release,
        );
    }

    executable::locate(
        "dummy-rustc",
        None,
        &[dummy_dir]
    ).unwrap_or_else(|| {
        error!("Cannot find the dummy-rustc binary, please build it using `cargo build {} --manifest-path xtask/Cargo.toml --package xtask --bin dummy-rustc`",
            if release { "--release" } else { "" }
        );
    })
}
