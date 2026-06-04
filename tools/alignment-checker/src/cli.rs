use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use clap::Parser;
use serde::Deserialize;

#[derive(Parser, Debug)]
pub struct Args {
    /// The path to the input configuration toml file.
    #[arg(short, long)]
    input: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    pub anchor: AnchorConfig,

    #[serde(default)]
    pub modules: Vec<ModuleEntry>,
}

#[derive(Debug, Clone)]
pub struct LoadedConfig {
    pub anchor: AnchorConfig,
    pub modules: Vec<LoadedModule>,
}

#[derive(Debug, Clone)]
pub struct LoadedModule {
    pub name: String,
    pub path: PathBuf,
    pub source: PathBuf,
    pub verification: ModuleVerificationConfig,
}

#[derive(Debug, Clone, Deserialize)]
pub struct AnchorConfig {
    pub git: String,
    pub tag: String,
    #[serde(default)]
    pub path: Option<PathBuf>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ModuleEntry {
    pub name: String,
    pub path: PathBuf,
    #[serde(default)]
    pub source: Option<PathBuf>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ModuleVerificationConfig {
    #[serde(default)]
    pub unsupported: Vec<UnsupportedItem>,

    #[serde(default)]
    pub verified: Vec<VerifiedItem>,

    #[serde(default)]
    pub planned: Vec<PlannedItem>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct UnsupportedItem {
    pub name: String,

    #[serde(default)]
    pub anchor: Option<String>,

    #[serde(rename = "type")]
    pub kind: ItemKind,

    #[allow(dead_code)]
    pub reason: UnsupportedReason,
}

#[derive(Debug, Clone, Deserialize)]
pub struct VerifiedItem {
    pub name: String,

    #[serde(default)]
    pub anchor: Option<String>,

    #[serde(rename = "type")]
    pub kind: ItemKind,

    #[serde(default)]
    #[allow(dead_code)]
    pub how: Option<VerificationMethod>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PlannedItem {
    pub name: String,

    #[serde(rename = "type")]
    pub kind: ItemKind,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ItemKind {
    Function,
    Struct,
    Trait,
    Impl,
    Module,
    Type,
    Const,
    Static,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnsupportedReason {
    LackHardwareSupport,
    UnsafeDependency,
    ExternalDependency,
    UnsupportedAbi,
    UnsupportedArchitecture,
    NotApplicable,
    Other,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum VerificationMethod {
    Rewrite,
    SameSignature,
    Stub,
    SpecOnly,
}

impl Config {
    #[allow(dead_code)]
    pub fn from_args(args: Args) -> Result<Self> {
        Self::from_path(&args.input)
    }

    pub fn from_path(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();

        if !path.exists() {
            anyhow::bail!("input file does not exist: {}", path.display());
        }

        if path.is_dir() {
            anyhow::bail!(
                "input path is a directory, expected a file: {}",
                path.display()
            );
        }

        let file_content = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read input file: {}", path.display()))?;

        let config: Config = toml::from_str(&file_content)
            .with_context(|| format!("failed to parse input file as TOML: {}", path.display()))?;

        Ok(config)
    }
}

impl LoadedConfig {
    pub fn from_args(args: Args) -> Result<Self> {
        let config_path = PathBuf::from(args.input);
        Self::from_path(config_path)
    }

    pub fn from_path(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();

        let config = Config::from_path(path)?;

        let base_dir = path.parent().unwrap_or_else(|| Path::new("."));

        let mut modules = Vec::new();

        for module in config.modules {
            let module_config_path = if module.path.is_absolute() {
                module.path.clone()
            } else {
                base_dir.join(&module.path)
            };
            let module_source_dir = match module.source {
                Some(source) if source.is_absolute() => source,
                Some(source) => base_dir.join(source),
                None => module_config_path
                    .parent()
                    .unwrap_or(base_dir)
                    .to_path_buf(),
            };

            if !module_config_path.exists() {
                anyhow::bail!(
                    "module verification config does not exist for module `{}`: {}",
                    module.name,
                    module_config_path.display()
                );
            }

            if module_config_path.is_dir() {
                anyhow::bail!(
                    "module verification config path is a directory for module `{}`: {}",
                    module.name,
                    module_config_path.display()
                );
            }

            if !module_source_dir.exists() {
                anyhow::bail!(
                    "module source directory does not exist for module `{}`: {}",
                    module.name,
                    module_source_dir.display()
                );
            }

            if !module_source_dir.is_dir() {
                anyhow::bail!(
                    "module source path is not a directory for module `{}`: {}",
                    module.name,
                    module_source_dir.display()
                );
            }

            let module_content =
                std::fs::read_to_string(&module_config_path).with_context(|| {
                    format!(
                        "failed to read verification config for module `{}`: {}",
                        module.name,
                        module_config_path.display()
                    )
                })?;

            let verification: ModuleVerificationConfig = toml::from_str(&module_content)
                .with_context(|| {
                    format!(
                        "failed to parse verification config for module `{}` as TOML: {}",
                        module.name,
                        module_config_path.display()
                    )
                })?;

            modules.push(LoadedModule {
                name: module.name,
                path: module_config_path,
                source: module_source_dir,
                verification,
            });
        }

        Ok(Self {
            anchor: config.anchor,
            modules,
        })
    }
}
