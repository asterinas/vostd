use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

use crate::commands::CargoBuildExterns;

pub fn deserialize<P: AsRef<Path>, T>(path: P) -> T
where
    T: serde::de::DeserializeOwned,
{
    let content = fs::read_to_string(&path).unwrap_or_else(|e| {
        fatal!("Unable to read file {:?}: {}", path.as_ref(), e);
    });
    let res: T = toml::from_str(&content).unwrap_or_else(|e| {
        fatal!("Unable to parse file {:?}: {}", path.as_ref(), e);
    });
    res
}

pub fn serialize<P: AsRef<Path>, T>(path: P, data: &T)
where
    T: Serialize,
{
    let content = toml::to_string_pretty(data).unwrap_or_else(|e| {
        fatal!("Unable to serialize data: {}", e);
    });
    fs::write(&path, content).unwrap_or_else(|e| {
        fatal!("Unable to write file {:?}: {}", path.as_ref(), e);
    });
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Dependencies {
    #[serde(with = "indexmap::map::serde_seq")]
    pub externs: IndexMap<String, String>,

    #[serde(with = "indexmap::map::serde_seq")]
    pub full_externs: IndexMap<String, String>,
}

impl From<CargoBuildExterns> for Dependencies {
    fn from(externs: CargoBuildExterns) -> Self {
        let mut full_deps: IndexMap<String, String> = IndexMap::new();

        for (_, dep) in externs.libraries.iter() {
            if full_deps.contains_key(&dep.name) && externs.last_level.contains_key(&dep.name) {
                // If two libraries have the same name, we use the last-level to
                // resolve the dependency.
                full_deps.insert(dep.name.to_owned(), externs.last_level[&dep.name].clone());
                continue;
            }

            full_deps.insert(dep.name.to_owned(), dep.lib_path.to_owned());
        }

        Dependencies {
            externs: externs.last_level,
            full_externs: full_deps,
        }
    }
}

impl Dependencies {
    pub fn renamed_full_externs(&self) -> IndexMap<String, String> {
        let mut renamed = IndexMap::new();

        // path -> alias of the package name
        let reverse_map: HashMap<String, String> = self
            .externs
            .iter()
            .map(|(k, v)| (v.clone(), k.clone()))
            .collect();

        for (name, path) in &self.full_externs {
            if let Some(alias) = reverse_map.get(path) {
                renamed.insert(alias.clone(), path.clone());
            }
            renamed.insert(name.clone(), path.clone());
        }
        renamed
    }
}
