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
        let mock_exec = tmp_path.join(T_EXEC);
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
        let all = verus::verus_targets();
        assert!(!all.is_empty(), "No targets found");

        let x = all.get("empty").unwrap();
        verus::resolve_deps_cached(x, true, verus::DEFAULT_RUST_TARGET);
    }

    #[test]
    fn test_new_package() {
        let p = new::create("test-package");
        println!("{:?}", p);
    }
}
