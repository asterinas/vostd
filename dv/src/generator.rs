use crate::files;
use askama::Template;
use std::io::Write;
use std::path::Path;
use std::time::SystemTime;

pub struct CrateInfo {
    pub name: String,
    pub alias: Option<String>,
}

#[derive(Template)]
#[template(path = "extern_crates.rs.j2")]
pub struct ExternCratesTemplate {
    pub crates: Vec<CrateInfo>,
}

impl Generative for ExternCratesTemplate {}

pub trait Generative: Template {
    fn generate(&self) -> String {
        self.render().unwrap_or_else(|e| {
            error!("Unable to render template: {}", e);
        })
    }

    fn save_as(&self, path: &Path) {
        let content = self.generate();
        let path = files::absolutize(&path);
        let mut file = std::fs::File::create(&path).unwrap_or_else(|e| {
            error!("Unable to create file {:?}: {}", path.display(), e);
        });
        file.write_all(content.as_bytes()).unwrap_or_else(|e| {
            error!("Unable to write to file {:?}: {}", path.display(), e);
        });
        file.flush().unwrap_or_else(|e| {
            error!("Unable to flush file {:?}: {}", path.display(), e);
        });

        info!("Generated file: {:?}", path.display());
    }

    fn save_if(&self, path: &Path, threshold: &SystemTime) {
        if path.exists() && files::modify_time(path) > *threshold {
            debug!("File {:?} is newer, skipping generation.", path.display());
            return;
        }

        self.save_as(path);
    }

    fn append_to(&self, path: &Path) {
        if !path.exists() {
            self.save_as(path);
            return;
        }

        let content = self.generate();
        let mut file = std::fs::OpenOptions::new()
            .append(true)
            .open(path)
            .unwrap_or_else(|e| {
                error!(
                    "Unable to open file {:?} for appending: {}",
                    path.display(),
                    e
                );
            });
        file.write_all(content.as_bytes()).unwrap_or_else(|e| {
            error!("Unable to write to file {:?}: {}", path.display(), e);
        });
        file.flush().unwrap_or_else(|e| {
            error!("Unable to flush file {:?}: {}", path.display(), e);
        });
        info!("Appended to file: {:?}", path.display());
    }
}
