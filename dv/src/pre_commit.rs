#[allow(unused_imports)]
use rust_dv::console::*;
use rust_dv::helper::*;
use std::collections::HashMap;

fn main() {
    let targets = verus::verus_targets();
    let metadata = cargo_metadata::MetadataCommand::new()
        .no_deps()
        .exec()
        .unwrap_or_else(|e| {
            fatal!("Unable to get metadata: {}", e);
        });

    let members: HashMap<String, &cargo_metadata::Package> = metadata
        .packages
        .iter()
        .map(|p| (p.name.to_string(), p))
        .collect();

    let mut found_errors = false;
    for (vt, t) in targets.iter() {
        let verus_target = t.root_file();
        // `targets` is keyed by crate identifier; metadata packages are keyed
        // by the manifest package name.
        let package = members.get(&t.name).unwrap_or_else(|| {
            fatal!("Unable to find target {} in metadata", vt);
        });

        let cargo_target = package
            .targets
            .first()
            .unwrap_or_else(|| {
                fatal!("Unable to find target for {} in metadata", vt);
            })
            .src_path
            .clone();
        if verus_target == cargo_target {
            warn!("Target [{}] has cargo target source path `{}` which is the same as the Verus target.\n\
                   Consider change `path=...` in `{}` to `path=src/.dummy.rs` to avoid build errors.",
                   t.name, cargo_target, package.manifest_path);
            found_errors = true;
        }
    }
    if found_errors {
        error!("Please fix the above errors before committing.");
    }
}
