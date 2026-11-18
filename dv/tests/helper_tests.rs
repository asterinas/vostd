use rust_dv::helper::*;

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::fs::File;
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;
    use tempfile::TempDir;

    const T_EXEC: &str = "mock_exec";

    fn create_tmp_exec() -> (TempDir, PathBuf) {
        let tmp_dir = tempfile::tempdir().unwrap();
        let tmp_path = tmp_dir.path();

        // mock exec
        let mock_exec = tmp_path.join(format!("{T_EXEC}{}", env::consts::EXE_SUFFIX));
        File::create(&mock_exec).unwrap();

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mut perms = mock_exec.metadata().unwrap().permissions();
            perms.set_mode(0o755);
            std::fs::set_permissions(&mock_exec, perms).unwrap();
        }

        (tmp_dir, mock_exec)
    }

    static PATH_CTX: Mutex<Vec<Option<String>>> = Mutex::new(vec![]);

    fn push_path(path: &Path) {
        let env_path = env::var("PATH").ok();
        PATH_CTX.lock().unwrap().push(env_path.clone());
        let mut paths = env::split_paths(&env_path.unwrap_or_default()).collect::<Vec<_>>();
        paths.push(PathBuf::from(path));
        let updated_path = env::join_paths(paths).unwrap();
        env::set_var("PATH", &updated_path);
    }

    fn pop_path() {
        let mut path_ctx = PATH_CTX.lock().unwrap();
        if let Some(path) = path_ctx.pop() {
            if let Some(p) = path {
                env::set_var("PATH", p);
            } else {
                env::remove_var("PATH");
            }
        }
    }

    #[test]
    fn test_locate_from_path() {
        let (bin_dir, tmp_exec) = create_tmp_exec();
        push_path(bin_dir.path());

        let res = executable::locate_from_path(&T_EXEC);
        assert!(res.is_some(), "Executable not found in PATH");
        let path: PathBuf = res.unwrap();
        assert_eq!(path, tmp_exec, "Executable path does not match");
        assert!(path.exists(), "Executable path does not exist");
        assert!(path.is_file(), "Executable path is not a file");
        pop_path();
    }

    #[test]
    fn test_locate_from_hints() {
        let (bin_dir, tmp_exec) = create_tmp_exec();
        let paths = vec![bin_dir.path()];

        let res = executable::locate_from_hints(&T_EXEC, paths.as_slice());

        assert!(res.is_some(), "Executable not found in hints");
        let path: PathBuf = res.unwrap();
        assert_eq!(path, tmp_exec, "Executable path does not match");
        assert!(path.exists(), "Executable path does not exist");
        assert!(path.is_file(), "Executable path is not a file");
    }

    #[test]
    fn test_locate_from_env() {
        let (bin_dir, tmp_exec) = create_tmp_exec();
        let env_var = "TEST_ENV_PATH";

        env::set_var(env_var, bin_dir.path());
        let res = executable::locate_from_env(&T_EXEC, env_var);
        assert!(res.is_some(), "Executable not found in env var");
        let path: PathBuf = res.unwrap();
        assert_eq!(path, tmp_exec, "Executable path does not match");
        assert!(path.exists(), "Executable path does not exist");
        assert!(path.is_file(), "Executable path is not a file");
        env::remove_var(env_var);
    }

    #[test]
    fn test_get_dependency() {
        if run_in_test_workspace("test_get_dependency") {
            return;
        }
        let all = verus::verus_targets();
        assert!(!all.is_empty(), "No targets found");

        let x = all.get("empty").unwrap();
        let deps = verus::get_local_dependency(x);
        assert!(deps.contains_key("dependency"));
        let resolved = verus::resolve_deps_cached(x, true, verus::DEFAULT_RUST_TARGET);
        assert!(Path::new(&resolved.full_externs["dependency"]).is_file());
    }

    #[test]
    fn test_new_package() {
        if run_in_test_workspace("test_new_package") {
            return;
        }
        let p = new::create("test-package");
        assert_eq!(p.name, "test-package");
        assert!(Path::new("verification/test-package/src/lib.rs").is_file());
        let metadata = cargo_metadata::MetadataCommand::new()
            .no_deps()
            .exec()
            .unwrap();
        assert!(metadata
            .packages
            .iter()
            .any(|package| package.name == "test-package"));
    }

    // Run tests that discover the workspace or create packages in a subprocess:
    // changing cwd in this test binary would race with parallel tests.
    fn run_in_test_workspace(test: &str) -> bool {
        const FIXTURE_ENV: &str = "RUST_DV_HELPER_TEST_WORKSPACE";
        if env::var(FIXTURE_ENV).as_deref() == Ok(test) {
            return false;
        }
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        std::fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"empty\", \"dependency\"]\nresolver = \"2\"\n",
        )
        .unwrap();
        for (name, dependencies) in [
            ("empty", "dependency = { path = \"../dependency\" }"),
            ("dependency", ""),
        ] {
            let package_dir = root.join(name);
            std::fs::create_dir_all(package_dir.join("src")).unwrap();
            std::fs::write(
                package_dir.join("Cargo.toml"),
                format!(
                    "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
                 [package.metadata.verus]\nverify = true\n[dependencies]\n{dependencies}\n"
                ),
            )
            .unwrap();
            std::fs::write(package_dir.join("src/lib.rs"), "#![no_std]\n").unwrap();
        }
        // The package template references these local toolchain crates.
        for (dir, name) in [
            ("vstd", "vstd"),
            ("builtin", "verus_builtin"),
            ("builtin_macros", "verus_builtin_macros"),
        ] {
            let package_dir = root.join("tools/verus/source").join(dir);
            std::fs::create_dir_all(package_dir.join("src")).unwrap();
            std::fs::write(
                package_dir.join("Cargo.toml"),
                format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n"),
            )
            .unwrap();
            std::fs::write(package_dir.join("src/lib.rs"), "").unwrap();
        }
        let output = std::process::Command::new(env::current_exe().unwrap())
            .args(["--exact", &format!("tests::{test}"), "--nocapture"])
            .current_dir(root)
            .env(FIXTURE_ENV, test)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "fixture test failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        true
    }
}
