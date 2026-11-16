use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::{fs, path::PathBuf, process::Command};

use crate::commands;

#[derive(Serialize, Deserialize, Debug)]
struct ToolchainConfig {
    toolchain: Toolchain,
}

#[derive(Serialize, Deserialize, Debug)]
struct Toolchain {
    channel: String,
    components: Option<Vec<String>>,
    targets: Option<Vec<String>>,
}

impl ToolchainConfig {
    pub fn load(toml: &PathBuf) -> Self {
        let contents = fs::read_to_string(toml).unwrap_or_else(|e| {
            panic!("Failed to read toolchain config file `{:?}`: {:?}", toml, e)
        });
        toml::from_str(&contents).unwrap_or_else(|e| {
            panic!(
                "Failed to parse toolchain config file `{:?}`: {:?}",
                toml, e
            )
        })
    }
}

pub fn load_toolchain(toml: &PathBuf) -> String {
    let cfg = ToolchainConfig::load(toml);
    let channel = &cfg.toolchain.channel;
    let components = cfg
        .toolchain
        .components
        .as_ref()
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    install_toolchain(channel);
    install_components(channel, components);
    return channel.to_string();
}

pub fn sync_toolchain(src: &PathBuf, dst: &PathBuf) {
    let src_cfg = ToolchainConfig::load(src);
    let mut dst_cfg = ToolchainConfig::load(dst);
    let mut needs_to_save: bool = false;

    if dst_cfg.toolchain.channel != src_cfg.toolchain.channel {
        dst_cfg.toolchain.channel = src_cfg.toolchain.channel.to_string();
        needs_to_save = true;
    }

    let src_components = src_cfg
        .toolchain
        .components
        .unwrap_or(Vec::new())
        .iter()
        .map(String::to_string)
        .collect::<HashSet<_>>();

    let dst_components = dst_cfg
        .toolchain
        .components
        .as_ref()
        .map(|c| c.iter().map(String::to_string).collect::<HashSet<_>>())
        .unwrap_or(HashSet::new());

    let extra_components: Vec<String> = src_components
        .difference(&dst_components)
        .cloned()
        .collect();

    if !extra_components.is_empty() {
        if dst_cfg.toolchain.components.is_none() {
            dst_cfg.toolchain.components = Some(Vec::new());
        }
        dst_cfg
            .toolchain
            .components
            .as_mut()
            .unwrap()
            .extend(extra_components);
        needs_to_save = true;
    }

    // save the updated configuration to `dst` toml file
    if needs_to_save {
        let dst_updated = toml::to_string_pretty(&dst_cfg)
            .unwrap_or_else(|e| panic!("Failed to serialize toolchain config: {:?}", e));
        fs::write(dst, dst_updated).unwrap_or_else(|e| {
            panic!("Failed to write toolchain config file `{:?}`: {:?}", dst, e)
        });
        info!(
            "{}: {}",
            "Workspace toolchain updated!".green(),
            "You need to run `cargo update` to apply changes.".yellow()
        );
    }
}

pub fn install_toolchain(channel: &str) {
    let cmd = &mut Command::new("rustup");
    cmd.args(["toolchain", "list"]);
    let installed = commands::run_capture(cmd);
    let xs = installed
        .stdout
        .lines()
        .filter(|line| line.contains(channel))
        .collect::<Vec<_>>();
    if xs.is_empty() {
        let cmd = &mut Command::new("rustup");
        cmd.args(["toolchain", "install", channel]);
        commands::run_panic(cmd);
    } else {
        debug!("Toolchain {} is already installed.", channel);
    }
}

pub fn install_components(channel: &str, components: &[String]) {
    if components.is_empty() {
        return;
    }

    let cmd = &mut Command::new("rustup");
    cmd.args(["component", "list", "--installed", "--toolchain", channel]);
    let installed = commands::run_capture(cmd);
    let installed_components: Vec<_> = installed.stdout.lines().collect();
    let mut to_install: Vec<String> = Vec::new();
    for c in components {
        if !installed_components.iter().any(|line| line.starts_with(c)) {
            to_install.push(c.clone());
        }
    }
    if !to_install.is_empty() {
        let cmd = &mut Command::new("rustup");
        cmd.args(["component", "add", "--toolchain", channel])
            .args(&to_install);
        commands::run_panic(cmd);
    }
}
