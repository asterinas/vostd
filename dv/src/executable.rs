use crate::files;

use std::env;
use std::path::{Path, PathBuf};

#[cfg(target_os = "windows")]
const EXE_SUFFIX: &str = ".exe";
#[cfg(not(target_os = "windows"))]
const EXE_SUFFIX: &str = "";

fn bin_name(binary: &Path) -> PathBuf {
    PathBuf::from(format!("{}{}", binary.display(), EXE_SUFFIX))
}

pub fn locate_from_path<P>(binary: &P) -> Option<PathBuf>
where
    P: AsRef<Path> + ?Sized,
{
    let binary = bin_name(binary.as_ref());
    let path = env::var("PATH").ok()?;
    let paths = env::split_paths(&path);
    paths
        .filter_map(|dir| {
            let full = dir.join(&binary);
            if full.is_file() {
                Some(full)
            } else {
                None
            }
        })
        .next()
}

pub fn locate_from_hints<P, D>(binary: &P, hints: &[D]) -> Option<PathBuf>
where
    P: AsRef<Path> + ?Sized,
    D: AsRef<Path>,
{
    let binary = bin_name(binary.as_ref());
    hints
        .iter()
        .filter_map(|hint| {
            let full = hint.as_ref().join(&binary);
            if full.is_file() {
                Some(full)
            } else {
                None
            }
        })
        .next()
}

pub fn locate_from_env<P>(binary: &P, env_var: &str) -> Option<PathBuf>
where
    P: AsRef<Path> + ?Sized,
{
    let binary = bin_name(binary.as_ref());
    let env_path = env::var(env_var).ok()?;
    let paths = env::split_paths(&env_path);
    paths
        .filter_map(|dir| {
            let full = dir.join(&binary);
            if full.is_file() {
                Some(full)
            } else {
                None
            }
        })
        .next()
}

pub fn locate<P, D>(binary: &P, env_var: Option<&str>, hints: &[D]) -> Option<PathBuf>
where
    P: AsRef<Path> + ?Sized,
    D: AsRef<Path>,
{
    let path = locate_from_hints(binary, hints)
        .or_else(|| env_var.and_then(|e| locate_from_env(binary, e)))
        .or_else(|| locate_from_path(binary));

    path.map(|path| files::absolutize(&path))
}

// On Windows, prefer pwsh if available, otherwise fall back to powershell.
#[cfg(target_os = "windows")]
pub fn get_powershell_command() -> std::io::Result<std::process::Command> {
    use colored::Colorize;
    use std::process::Command;

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
            "Warning: Using powershell.exe (Windows PowerShell 5.x).".yellow()
        );
        eprintln!(
            "{}",
            "If you encounter errors related to `Get‑ExecutionPolicy` or \
            failure loading the `Microsoft.PowerShell.Security` module, please \
            try using `pwsh` (PowerShell 7 or later) instead."
                .yellow()
        );
        return Ok(Command::new("powershell"));
    }

    Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "No working PowerShell version found",
    ))
}
