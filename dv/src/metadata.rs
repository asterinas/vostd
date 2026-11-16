use crate::{files, projects};
use cargo_metadata::MetadataCommand;
use std::fs;
use std::path::{Path, PathBuf};
use toml_edit::{Array, DocumentMut};

pub struct Workspace;

impl Workspace {
    pub fn default_path() -> PathBuf {
        projects::get_root().join("Cargo.toml").to_path_buf()
    }

    pub fn add_member(&self, member_path: &Path) -> Result<(), anyhow::Error> {
        let mt = MetadataCommand::new()
            .manifest_path(&Self::default_path())
            .no_deps()
            .exec()?;

        let rel_path = files::make_relative(member_path, &projects::get_root());

        if mt.workspace_members.iter().any(|m| {
            // Manifest path is absolute
            mt[m].manifest_path.parent().unwrap() == member_path
        }) {
            return Ok(());
        }

        let mut doc = fs::read_to_string(&Self::default_path())?.parse::<DocumentMut>()?;

        if let Some(members) = doc["workspace"]["members"].as_array_mut() {
            members.set_trailing_comma(true);
            members.set_trailing("\n");
            members.push(rel_path.to_string_lossy().to_string());
        } else {
            doc["workspace"]["members"] = toml_edit::value(Array::new());
            doc["workspace"]["members"]
                .as_array_mut()
                .unwrap()
                .push(rel_path.to_string_lossy().to_string());
        }

        fs::write(&Self::default_path(), doc.to_string())?;
        Ok(())
    }

    pub fn remove_member(&self, member_path: &Path) -> Result<(), anyhow::Error> {
        let mt = MetadataCommand::new()
            .manifest_path(&Self::default_path())
            .no_deps()
            .exec()?;
        if !mt
            .workspace_members
            .iter()
            .any(|m| mt[m].manifest_path.parent().unwrap() == member_path)
        {
            return Ok(());
        }

        let mut doc = fs::read_to_string(&Self::default_path())?.parse::<DocumentMut>()?;

        if let Some(members) = doc["workspace"]["members"].as_array_mut() {
            members.retain(|m| m.to_string() != member_path.to_string_lossy().to_string());
        }

        fs::write(&Self::default_path(), doc.to_string())?;
        Ok(())
    }
}
