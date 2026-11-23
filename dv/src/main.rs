use clap::{ArgAction, Parser, Subcommand};
use colored::Colorize;
use rust_dv::helper::*;

#[derive(Parser, Debug)]
#[command(
    name = "cli",
    author = "Hao",
    version = "0.1.0",
    about = "A tool to manage the formal verification targets"
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    #[command(
        name = "verify",
        about = "Verify the verification targets",
        alias = "v"
    )]
    Verify(VerificationArgs),

    #[command(
        name = "focus",
        about = "Verify root targets without re-checking dependency proofs"
    )]
    Focus(VerificationArgs),

    #[command(
        name = "count",
        about = "Count Verus source lines by target or module",
        alias = "cnt"
    )]
    Count(CountArgs),

    #[command(
        name = "doc",
        about = "Generate documentation for the verification targets"
    )]
    Doc(DocArgs),

    #[command(
        name = "bootstrap",
        about = "Bootstrap the Verus toolchain",
        alias = "bs"
    )]
    Bootstrap(BootstrapArgs),

    #[command(name = "build", about = "Build the verification targets", alias = "c")]
    Build(BuildArgs),

    #[command(
        name = "clean",
        about = "Run `cargo clean` for the workspace",
        alias = "cl"
    )]
    Clean(CleanArgs),

    #[command(
        name = "list",
        about = "List all available verification targets",
        alias = "ls"
    )]
    ListTargets(ListTargetsArgs),

    #[command(name = "new", about = "Create a new verification target", alias = "n")]
    NewTarget(NewTargetArgs),

    #[command(
        name = "show",
        about = "Show the details of a syntax item",
        alias = "s"
    )]
    ShowItem(ShowItemArgs),

    #[command(
        name = "fmt",
        about = "Format the source code of a verification target",
        alias = "f"
    )]
    Format(FmtArgs),
}

#[derive(Parser, Debug)]
struct BootstrapArgs {
    #[arg(
        long = "restart", 
        help = "Remove all toolchain and restart the bootstrap",
        default_value = "false", 
        action = ArgAction::SetTrue,
        conflicts_with = "upgrade"
    )]
    restart: bool,

    #[arg(
        long = "upgrade",
        help = "Upgrade the verus toolchain",
        default_value = "false",
        action = ArgAction::SetTrue)]
    upgrade: bool,

    #[arg(
        short = 'd',
        long = "debug",
        help = "Build artifacts in debug mode",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    debug: bool,

    #[arg(
        long = "upstream-verus",
        help = "Pull the upstream verus-lang/verus instead of asterinas/verus",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    upstream_verus: bool,

    #[arg(
        long = "branch",
        help = "The branch name to pull",
        value_name = "BRANCH_NAME"
    )]
    branch: Option<String>,

    #[arg(
        long = "build-arg",
        help = "An extra argument passed to `cargo-verus` when building vstd",
        value_name = "ARG",
        action = ArgAction::Append,
        allow_hyphen_values = true
    )]
    build_args: Vec<String>,
}

#[derive(clap::Args, Debug)]
struct VerificationArgs {
    #[arg(
        short = 'p',
        long = "package", 
        value_parser = verus::find_target,
        help = "The targets to verify", 
        num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<VerusTarget>,

    #[arg(
        long = "target",
        value_name = "TRIPLE",
        default_value = verus::DEFAULT_RUST_TARGET,
        value_parser = verus::parse_rust_target,
        help = "Rust target triple (architecture, OS, and environment)",
        action = ArgAction::Set)]
    rust_target: String,

    #[arg(
        short = 'e',
        long = "max-errors",
        help = "The maximum number of errors to display",
        default_value = "5", 
        action = ArgAction::Set)]
    max_errors: usize,

    #[arg(
        short = 'i',
        long = "import", 
        value_parser = verus::find_target,
        help = "Import verified local crates (they need to be built first)",
        num_args = 0..,
        action = ArgAction::Append)]
    imports: Vec<VerusTarget>,

    #[arg(
        short = 'l',
        long = "log",
        help = "Log the verification process",
        default_value = "false", 
        action = ArgAction::SetTrue)]
    log: bool,

    #[arg(
        short = 'g',
        long = "trace",
        help = "Enable trace logging for the verification process",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    trace: bool,

    #[arg(
        short = 'd',
        long = "debug",
        help = "Build artifacts in debug mode",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    debug: bool,

    #[command(flatten, next_help_heading = "Cargo feature options")]
    cargo_features: clap_cargo::Features,

    #[arg(
        last = true,
        value_name = "VERUS_ARGS",
        help = "Arguments passed to the Verus verifier after `--`",
        help_heading = "Verus options",
        allow_hyphen_values = true
    )]
    verus_args: Vec<String>,
}

#[derive(Parser, Debug)]
struct CountArgs {
    #[arg(
        short = 'p',
        long = "package",
        value_parser = verus::find_target,
        help = "The packages to count",
        num_args = 0..,
        action = ArgAction::Append
    )]
    targets: Vec<VerusTarget>,

    #[arg(
        long = "target",
        value_name = "TRIPLE",
        default_value = verus::DEFAULT_RUST_TARGET,
        value_parser = verus::parse_rust_target,
        help = "Rust target triple (architecture, OS, and environment)",
        action = ArgAction::Set)]
    rust_target: String,

    #[arg(
        short = 'm',
        long = "module",
        value_name = "MODULE_PATH",
        help = "Count only this module and its file-based submodules (for example, sync::rwlock)"
    )]
    module: Option<String>,

    #[arg(
        short = 'a',
        long = "print-all",
        help = "Print every annotated source line",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    print_all: bool,
}

#[derive(Parser, Debug)]
struct DocArgs {
    #[arg(
        short = 'p',
        long = "package",
        help = "The package to generate documentation for (along with its dependencies)"
    )]
    target: String,

    #[arg(
        long = "target",
        value_name = "TRIPLE",
        default_value = verus::DEFAULT_RUST_TARGET,
        value_parser = verus::parse_rust_target,
        help = "Rust target triple (architecture, OS, and environment)",
        action = ArgAction::Set)]
    rust_target: String,

    #[arg(
        long = "no-verus-conds",
        help = "Call normal rustdoc without Verus conditions",
        default_value = "false",
        action = ArgAction::SetTrue,
        conflicts_with = "verus_conds_debug")]
    no_verus_conds: bool,

    #[arg(
        long = "verus-conds-debug",
        help = "Show `verus_doc_special_attr` in generated docs without verusdoc post-processing",
        default_value = "false",
        action = ArgAction::SetTrue,
        conflicts_with = "no_verus_conds")]
    verus_conds_debug: bool,

    #[arg(
        long = "json-output",
        help = "Generate rustdoc output in JSON format",
        default_value = "false",
        action = ArgAction::SetTrue)]
    json_output: bool,
}

#[derive(Parser, Debug)]
struct BuildArgs {
    #[arg(
        short = 'p',
        long = "package",
        value_parser = verus::find_target,
        help = "The targets to build",
        num_args = 0..,
        action = ArgAction::Append)]
    targets: Vec<VerusTarget>,

    #[arg(
        long = "target",
        value_name = "TRIPLE",
        default_value = verus::DEFAULT_RUST_TARGET,
        value_parser = verus::parse_rust_target,
        help = "Rust target triple (architecture, OS, and environment)",
        action = ArgAction::Set)]
    rust_target: String,

    #[arg(
        short = 'i',
        long = "import", 
        value_parser = verus::find_target,
        help = "Import verified local crates (they need to be built first)",
        num_args = 0..,
        action = ArgAction::Append)]
    imports: Vec<VerusTarget>,

    #[arg(
        short = 'e',
        long = "max-errors",
        help = "The maximum number of errors to display",
        default_value = "5", 
        action = ArgAction::Set)]
    max_errors: usize,

    #[arg(
        short = 'l',
        long = "log",
        help = "Log the verification process",
        default_value = "false", 
        action = ArgAction::SetTrue)]
    log: bool,

    #[arg(
        short = 'g',
        long = "trace",
        help = "Enable trace logging for the verification process",
        default_value = "false",
        action = ArgAction::SetTrue
    )]
    trace: bool,

    #[arg(
        short = 'd',
        long = "debug",
        default_value = "false",
        help = "Build artifacts in debug mode",
        action = ArgAction::SetTrue)]
    debug: bool,

    #[arg(
        short = 'a',
        long = "disasm",
        default_value = "false",
        help = "Do not disassemble the built binary",
        action = ArgAction::SetTrue)]
    disasm: bool,

    #[command(flatten, next_help_heading = "Cargo feature options")]
    cargo_features: clap_cargo::Features,

    #[arg(
        last = true,
        value_name = "VERUS_ARGS",
        help = "Arguments passed to the Verus verifier after `--`",
        help_heading = "Verus options",
        allow_hyphen_values = true
    )]
    verus_args: Vec<String>,
}

#[derive(Parser, Debug)]
struct CleanArgs {}

#[derive(Parser, Debug)]
struct ListTargetsArgs {}

#[derive(Parser, Debug)]
struct NewTargetArgs {
    #[arg(
        help = "Name of the new target (created under verification/)",
        allow_hyphen_values = true
    )]
    name: String,
}

#[derive(Debug, Clone, clap::ValueEnum)]
pub enum SupportedShowItem {
    Struct,
    Function,
}

#[derive(Parser, Debug)]
struct ShowItemArgs {
    /// Package name
    #[arg(
        short = 'p',
        long = "package",
        help = "The package to look into",
        action = ArgAction::Set,)]
    package: String,

    #[arg(
        short = 't',
        long = "info",
        help = "The type of information to show",
        value_enum,
        default_value = "struct"
    )]
    info_type: SupportedShowItem,

    #[arg(
        short = 'i',
        long = "id",
        help = "The identifier of the item to show",
        action = ArgAction::Set,
        required = true,
    )]
    id: String,
}

#[derive(Debug, Clone, clap::ValueEnum)]
pub enum TranslateMode {
    Append,
    Overwrite,
}

#[derive(Debug, Clone, clap::ValueEnum)]
pub enum TranslateBlockType {
    #[value(name = "func-context")]
    SolanaPerFunctionContext,
    Other,
}

#[derive(Parser, Debug)]
struct TranslateArgs {
    #[arg(
        short = 'p',
        long = "package",
        help = "The package to translate",
        action = ArgAction::Set,
        required = true,
    )]
    package: String,

    #[arg(
        short = 'i',
        long = "id",
        help = "The original identifier to translate",
        action = ArgAction::Set,
        required = true,
    )]
    id: String,

    #[arg(
        short = 'b',
        long = "block",
        help = "The type of block to translate (e.g., function context)",
        value_enum,
        default_value = "func-context"
    )]
    block_type: TranslateBlockType,
}

#[derive(Parser, Debug)]
struct FmtArgs {
    #[arg(short = 'p', long = "package", value_parser = format::package_parser,
        help = "The packages to format", num_args = 0..,
        action = ArgAction::Append)]
    packages: Vec<String>,
}

fn cargo_feature_args(features: &clap_cargo::Features) -> Vec<String> {
    let mut args = Vec::new();
    if features.all_features {
        args.push("--all-features".to_string());
    }
    if features.no_default_features {
        args.push("--no-default-features".to_string());
    }
    if !features.features.is_empty() {
        args.push("--features".to_string());
        args.push(features.features.join(" "));
    }
    args
}

fn verify(args: &VerificationArgs, mode: verus::VerificationMode) -> Result<(), DynError> {
    let targets = args.targets.clone();
    let options = verus::ExtraOptions {
        max_errors: args.max_errors,
        log: args.log,
        release: !args.debug,
        trace: args.trace,
        disasm: false,
        cargo_args: cargo_feature_args(&args.cargo_features),
        verus_args: args.verus_args.clone(),
        verification_mode: mode,
        rust_target: args.rust_target.clone(),
    };

    verus::exec_verify(&targets, &options)
}

fn count(args: &CountArgs) -> Result<(), DynError> {
    count::exec_count(
        &args.targets,
        args.module.as_deref(),
        args.print_all,
        &args.rust_target,
    )
}

fn doc(args: &DocArgs) -> Result<(), DynError> {
    doc::exec_doc(
        &args.target,
        !args.no_verus_conds,
        args.verus_conds_debug,
        args.json_output,
        &args.rust_target,
    )
}

fn bootstrap(args: &BootstrapArgs) -> Result<(), DynError> {
    let options = verus::install::VerusInstallOpts {
        release: !args.debug,
        restart: args.restart,
        branch: args.branch.clone(),
        build_args: args.build_args.clone(),
        force_reset: args.upgrade,
        upstream_verus: args.upstream_verus,
    };

    if args.upgrade {
        verus::install::exec_upgrade(&options)
    } else {
        verus::install::exec_bootstrap(&options)
    }
}

fn build(args: &BuildArgs) -> Result<(), DynError> {
    let targets = args.targets.clone();
    let options = verus::ExtraOptions {
        max_errors: args.max_errors,
        log: args.log,
        trace: args.trace,
        release: !args.debug,
        disasm: args.disasm,
        cargo_args: cargo_feature_args(&args.cargo_features),
        verus_args: args.verus_args.clone(),
        verification_mode: verus::VerificationMode::Verify,
        rust_target: args.rust_target.clone(),
    };

    verus::exec_build(&targets, &options)
}

fn clean(_args: &CleanArgs) -> Result<(), DynError> {
    verus::exec_clean()
}

fn list_targets(_args: &ListTargetsArgs) -> Result<(), DynError> {
    let targets = verus::verus_targets();
    let width = targets.keys().map(|s| s.len()).max().unwrap_or(0).min(70) + 1;

    for (name, target) in targets {
        println!(
            "{:<width$}: {} {}\n  {}",
            name.blue(),
            target.dir.to_string_lossy().bright_black(),
            target.version.bright_yellow(),
            format!("{:<width$}features = [{}]", "", target.features.join(", ")).bright_black(),
        );
    }
    Ok(())
}

fn new_target(args: &NewTargetArgs) -> Result<(), DynError> {
    if args.name.is_empty() || args.name.trim().is_empty() {
        error!("Please provide a name for the new target.");
    }

    let package = crate::new::create(args.name.trim());
    println!("Created new target: {}", package.name);
    Ok(())
}

fn show_item(args: &ShowItemArgs) -> Result<(), DynError> {
    let package = &args.package;
    let id = &args.id;

    match args.info_type {
        SupportedShowItem::Struct => {
            let struct_info = show::find_struct_in_package(package, id)?;
            struct_info
                .iter()
                .for_each(|s| println!("{}", s.as_string()));
        }
        _ => {
            error!("Unsupported item type: {:?}", args.info_type);
        }
    }

    Ok(())
}

fn format(args: &FmtArgs) -> Result<(), DynError> {
    format::format_packages(&args.packages)
}

fn main() {
    let cli = Cli::parse();
    if let Err(e) = match &cli.command {
        Commands::Verify(args) => verify(args, verus::VerificationMode::Verify),
        Commands::Focus(args) => verify(args, verus::VerificationMode::Focus),
        Commands::Count(args) => count(args),
        Commands::Doc(args) => doc(args),
        Commands::Bootstrap(args) => bootstrap(args),
        Commands::Build(args) => build(args),
        Commands::ListTargets(args) => list_targets(args),
        Commands::NewTarget(args) => new_target(args),
        Commands::ShowItem(args) => show_item(args),
        Commands::Format(args) => format(args),
        Commands::Clean(args) => clean(args),
    } {
        error!("Error: {}", e);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn focus_separates_cargo_features_from_verus_arguments() {
        let cli = Cli::try_parse_from([
            "dv",
            "focus",
            "--features",
            "irc11 alloc",
            "--no-default-features",
            "--",
            "--verify-only-module",
            "sync::rcu",
        ])
        .unwrap();

        let Commands::Focus(args) = cli.command else {
            panic!("expected focus command");
        };
        assert_eq!(args.cargo_features.features, ["irc11", "alloc"]);
        assert!(args.cargo_features.no_default_features);
        assert_eq!(
            cargo_feature_args(&args.cargo_features),
            ["--no-default-features", "--features", "irc11 alloc"]
        );
        assert_eq!(args.verus_args, ["--verify-only-module", "sync::rcu"]);
    }

    #[test]
    fn build_accepts_all_features() {
        let cli = Cli::try_parse_from(["dv", "build", "--all-features"]).unwrap();

        let Commands::Build(args) = cli.command else {
            panic!("expected build command");
        };
        assert!(args.cargo_features.all_features);
        assert_eq!(cargo_feature_args(&args.cargo_features), ["--all-features"]);
        assert!(args.verus_args.is_empty());
    }

    #[test]
    fn rust_target_defaults_to_x86() {
        let cli = Cli::try_parse_from(["dv", "verify"]).unwrap();
        let Commands::Verify(args) = cli.command else {
            panic!("expected verify command");
        };
        assert_eq!(args.rust_target, verus::DEFAULT_RUST_TARGET);
    }

    #[test]
    fn rust_target_rejects_unsupported_triples() {
        let err =
            Cli::try_parse_from(["dv", "build", "--target", "aarch64-unknown-none"]).unwrap_err();
        assert!(err.to_string().contains("unsupported Rust target"));
    }

    #[test]
    fn commands_accept_linux_host_target() {
        let triple = "x86_64-unknown-linux-gnu";
        for command in ["verify", "focus", "build", "count", "doc"] {
            let mut argv = vec!["dv", command, "--target", triple];
            if command == "doc" {
                argv.extend(["--package", "linux-bzimage-builder"]);
            }
            let cli = Cli::try_parse_from(argv).unwrap();
            let rust_target = match cli.command {
                Commands::Verify(args) | Commands::Focus(args) => args.rust_target,
                Commands::Build(args) => args.rust_target,
                Commands::Count(args) => args.rust_target,
                Commands::Doc(args) => args.rust_target,
                _ => panic!("expected a command accepting --target"),
            };
            assert_eq!(rust_target, triple);
        }
    }

    #[test]
    fn count_accepts_a_module_and_print_all() {
        let cli = Cli::try_parse_from(["dv", "count", "--module", "sync::rwlock", "--print-all"])
            .unwrap();

        let Commands::Count(args) = cli.command else {
            panic!("expected count command");
        };
        assert!(args.targets.is_empty());
        assert_eq!(args.module.as_deref(), Some("sync::rwlock"));
        assert!(args.print_all);
    }

    #[test]
    fn bootstrap_accepts_upstream_irc11_build_argument() {
        let cli = Cli::try_parse_from([
            "dv",
            "bootstrap",
            "--upstream-verus",
            "--branch",
            "irc11",
            "--build-arg=--vstd-weak-memory",
        ])
        .unwrap();

        let Commands::Bootstrap(args) = cli.command else {
            panic!("expected bootstrap command");
        };
        assert!(args.upstream_verus);
        assert_eq!(args.branch.as_deref(), Some("irc11"));
        assert_eq!(args.build_args, ["--vstd-weak-memory"]);
    }
}
