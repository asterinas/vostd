use std::path::Path;
use std::process::{Command, Stdio};

pub fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    let build_file = "src/lib.rs";
    let replace_file = "src/.dummy.rs";

    for arg in args.iter_mut() {
        if arg.ends_with(build_file) && Path::new(arg).exists() {
            // replace src/lib.rs with src/.dummy.rs
            let base_str = &arg[..arg.len() - build_file.len()];
            let replaced_arg = format!("{}{}", base_str, replace_file);
            if Path::new(&replaced_arg).exists() {
                *arg = replaced_arg;
            }
            break;
        }
    }

    let mut cmd = Command::new("rustc");
    cmd.args(args);

    cmd.stdout(Stdio::inherit()).stderr(Stdio::inherit());

    cmd.spawn().unwrap().wait().unwrap();
}
