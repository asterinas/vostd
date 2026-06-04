// SPDX-License-Identifier: MPL-2.0

use clap::Parser;

mod check;
mod cli;
mod index;

fn main() -> anyhow::Result<()> {
    let args = cli::Args::parse();
    let loaded_config = cli::LoadedConfig::from_args(args)?;

    match loaded_config.check_consistency() {
        Ok(summary) => {
            println!(
                "Configuration consistency check passed: checked {} module{}, {} declared entr{}, {} actual delta{}",
                summary.modules_checked,
                plural(summary.modules_checked),
                summary.declared_entries,
                entry_plural(summary.declared_entries),
                summary.actual_deltas,
                plural(summary.actual_deltas),
            );
        }
        Err(e) => {
            eprintln!("Configuration consistency check failed: {e:#}");
            std::process::exit(1);
        }
    }

    Ok(())
}

fn plural(count: usize) -> &'static str {
    if count == 1 { "" } else { "s" }
}

fn entry_plural(count: usize) -> &'static str {
    if count == 1 { "y" } else { "ies" }
}
