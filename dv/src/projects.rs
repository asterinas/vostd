use std::env;
use std::path::PathBuf;

use project_root::get_project_root;

pub fn get_root() -> PathBuf {
    match get_project_root() {
        Ok(path) => path,
        Err(_) => env::current_dir().expect("Failed to find the project root!"),
    }
}

pub fn get_build_dir(release: bool) -> &'static str {
    if release {
        "release"
    } else {
        "debug"
    }
}

pub fn get_dummy_rustc(release: bool) -> PathBuf {
    get_root()
        .join("target")
        .join(get_build_dir(release))
        .join("dummy-rustc")
}
