use crate::helper::{error, fatal};
use std::fs;
use std::path::{Path, PathBuf};
use std::{env, path};
use touch::file;

pub fn absolutize<P: AsRef<Path>>(path: &P) -> PathBuf {
    if path.as_ref().is_absolute() {
        path.as_ref().to_path_buf()
    } else {
        let current_dir = env::current_dir().unwrap();
        current_dir.join(path)
    }
}

pub fn dir_as_package(dir: &str) -> String {
    dir.trim_start_matches(".\\")
        .trim_start_matches("./")
        .trim_start_matches("/")
        .trim_end_matches(path::MAIN_SEPARATOR)
        .to_string()
}

pub fn touch(path: &str) {
    file::write(path, "", false).unwrap_or_else(|e| {
        error!("Unable to create file {:?}: {}", path, e);
    });
}

pub fn modify_time<P>(path: P) -> std::time::SystemTime
where
    P: AsRef<Path>,
{
    fs::metadata(&path)
        .unwrap_or_else(|e| {
            fatal!(
                "Unable to get metadata for file {:?}: {}",
                path.as_ref().display(),
                e
            );
        })
        .modified()
        .unwrap_or_else(|e| {
            fatal!(
                "Unable to get modified time for file {:?}: {}",
                path.as_ref().display(),
                e
            );
        })
}

pub fn newer<P, Q>(a: P, b: Q) -> bool
where
    P: AsRef<Path>,
    Q: AsRef<Path>,
{
    let ma = modify_time(a);
    let mb = modify_time(b);

    ma > mb
}

pub fn make_relative(path: &Path, base: &Path) -> PathBuf {
    path.strip_prefix(base)
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|_| path.to_path_buf())
}
