use crate::{generator::Generative, helper::*};
use anyhow::Error;
use askama::Template;
use serde::{de::Error as DeError, Deserialize, Serialize};
use std::collections::HashMap;
use std::ops::Deref;
use toml::Value;

#[derive(Serialize, Deserialize, Debug)]
pub struct VerifyDeps {
    pub dependencies: HashMap<String, String>,
}

#[derive(Clone, Debug)]
pub struct DependencyConfig {
    pub name: String,
    pub config: String,
}

impl VerifyDeps {
    pub fn empty() -> Self {
        VerifyDeps {
            dependencies: HashMap::new(),
        }
    }

    pub fn load() -> Self {
        let path = projects::get_root().join("verify.deps.toml");
        if !path.exists() {
            warn!("No `verify.deps.toml` found in the workspace!");
            return Self::empty();
        }

        let content = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            warn!("Unable to read file {:?}: {}", path.display(), e);
            String::new()
        });

        let deps = VerifyDeps::extract(&content).unwrap_or_else(|e| {
            warn!("Unable to parse `verify.deps.toml`: {}", e);
            HashMap::new()
        });

        Self { dependencies: deps }
    }

    pub fn extract(content: &str) -> Result<HashMap<String, String>, toml::de::Error> {
        let mut deps: HashMap<String, String> = HashMap::new();

        let r: Value = content.parse()?;
        if let Value::Table(t) = r {
            if let Some(Value::Table(d)) = t.get("dependencies") {
                for (name, config) in d.iter() {
                    // Convert the config value to its string representation
                    let config_str = config.to_string();
                    deps.insert(name.clone(), config_str);
                }
            } else {
                return Err(toml::de::Error::custom("Missing 'dependencies' table"));
            }
        }

        Ok(deps)
    }
}

#[derive(Clone, Debug)]
pub struct Package {
    pub name: String,
    pub package_name: String,
    pub dependencies: Vec<DependencyConfig>,
}

#[derive(Template)]
#[template(path = "Cargo.toml.j2")]
pub struct CargoTomlTemplate {
    pub c: Package,
}

impl Deref for CargoTomlTemplate {
    type Target = Package;

    fn deref(&self) -> &Self::Target {
        &self.c
    }
}

impl Generative for CargoTomlTemplate {}

#[derive(Template)]
#[template(path = "lib.rs.j2")]
pub struct LibTemplate {
    pub c: Package,
}

impl Deref for LibTemplate {
    type Target = Package;

    fn deref(&self) -> &Self::Target {
        &self.c
    }
}

impl Generative for LibTemplate {}

#[derive(Template)]
#[template(path = ".dummy.rs.j2")]
pub struct DummyRsTemplate {
    pub c: Package,
}

impl Deref for DummyRsTemplate {
    type Target = Package;

    fn deref(&self) -> &Self::Target {
        &self.c
    }
}

impl Generative for DummyRsTemplate {}

impl Package {
    pub fn new(name: &str) -> Self {
        Package {
            name: name.to_string(),
            package_name: name.replace('-', "_"),
            dependencies: vec![],
        }
    }

    pub fn take_dependencies(&mut self, deps: VerifyDeps) -> &Self {
        let ds: Vec<DependencyConfig> = deps
            .dependencies
            .into_iter()
            .map(|(name, config)| DependencyConfig { name, config })
            .collect();

        self.dependencies = ds;
        self
    }

    pub fn populate(&self) -> Result<(), Error> {
        // Create the package directory
        let p_dir = projects::get_root().join("verification").join(&self.name);
        if p_dir.exists() {
            error!("Package directory {:?} already exists!", p_dir.display());
        }

        std::fs::create_dir_all(&p_dir).map_err(|e| {
            Error::msg(format!(
                "Unable to create package directory {:?}: {}",
                p_dir.display(),
                e
            ))
        })?;

        // Create the Cargo.toml file
        let cargo_tmpl = CargoTomlTemplate { c: self.clone() };
        cargo_tmpl.save_as(&p_dir.join("Cargo.toml"));

        // Create the src directory
        std::fs::create_dir_all(p_dir.join("src")).map_err(|e| {
            Error::msg(format!(
                "Unable to create src directory {:?}: {}",
                p_dir.join("src").display(),
                e
            ))
        })?;

        // Create the src/lib.rs file
        let lib_tmpl = LibTemplate { c: self.clone() };
        lib_tmpl.save_as(&p_dir.join("src").join("lib.rs"));

        // Create the src/.dummy.rs file
        let dummy_tmpl = DummyRsTemplate { c: self.clone() };
        dummy_tmpl.save_as(&p_dir.join("src").join(".dummy.rs"));

        // Update the workspace Cargo.toml to include the new package
        metadata::Workspace.add_member(&p_dir)?;

        Ok(())
    }
}

pub fn create(name: &str) -> Package {
    let mut package = Package::new(name);

    package.take_dependencies(VerifyDeps::load());

    package.populate().unwrap_or_else(|e| {
        error!("Unable to populate package {}: {}", name, e);
    });

    package
}
