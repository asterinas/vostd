use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use git2::{
    FetchOptions, Object, ObjectType, Repository,
    build::{CheckoutBuilder, RepoBuilder},
};

use crate::cli::{
    AnchorConfig, ItemKind, LoadedConfig, LoadedModule, ModuleVerificationConfig,
    VerificationMethod,
};
use crate::index::{FunctionSnapshot, ModuleIndex, index_module};

#[derive(Debug, Default)]
pub struct CheckSummary {
    pub modules_checked: usize,
    pub declared_entries: usize,
    pub actual_deltas: usize,
}

impl LoadedConfig {
    pub fn check_consistency(&self) -> Result<CheckSummary> {
        let anchor_dir = self.check_and_clone_repo()?;
        let mut errors = Vec::new();
        let mut summary = CheckSummary::default();

        for module in &self.modules {
            self.check_module(module, &anchor_dir, &mut errors, &mut summary)?;
        }

        if !errors.is_empty() {
            anyhow::bail!("{}", format_errors(&errors));
        }

        Ok(summary)
    }

    fn check_and_clone_repo(&self) -> Result<PathBuf> {
        let anchor_repo_dir = prepare_anchor_repo(&self.anchor)?;
        let anchor_dir = match self.anchor.path.as_ref() {
            Some(dir) => anchor_repo_dir.join(dir),
            None => anchor_repo_dir,
        };

        if !anchor_dir.exists() {
            anyhow::bail!(
                "anchor path `{}` does not exist in the cloned repository",
                anchor_dir.display()
            );
        }

        Ok(anchor_dir)
    }

    fn check_module(
        &self,
        module: &LoadedModule,
        anchor_dir: &Path,
        errors: &mut Vec<String>,
        summary: &mut CheckSummary,
    ) -> Result<()> {
        summary.modules_checked += 1;

        let current_module_dir = std::fs::canonicalize(&module.source).with_context(|| {
            format!(
                "failed to canonicalize source directory for module `{}`: {}",
                module.name,
                module.source.display()
            )
        })?;
        let repo_dir = std::fs::canonicalize(std::env::current_dir()?)
            .context("failed to canonicalize current working directory")?;
        let module_rel_dir = current_module_dir
            .strip_prefix(&repo_dir)
            .with_context(|| {
                format!(
                    "module `{}` directory `{}` is not under current repository `{}`",
                    module.name,
                    current_module_dir.display(),
                    repo_dir.display()
                )
            })?;
        let anchor_module_dir = anchor_dir.join(module_rel_dir);

        if !anchor_module_dir.exists() {
            errors.push(format!(
                "[module {}] anchor module directory does not exist: {}",
                module.name,
                anchor_module_dir.display()
            ));
            return Ok(());
        }

        let current_index = index_module(&current_module_dir).with_context(|| {
            format!(
                "failed to index current module `{}` at {}",
                module.name,
                current_module_dir.display()
            )
        })?;
        let anchor_index = index_module(&anchor_module_dir).with_context(|| {
            format!(
                "failed to index anchor module `{}` at {}",
                module.name,
                anchor_module_dir.display()
            )
        })?;

        for error in current_index
            .errors
            .iter()
            .chain(anchor_index.errors.iter())
        {
            errors.push(format!("[module {}] {error}", module.name));
        }

        let deltas = diff_indexes(&current_index, &anchor_index);
        summary.actual_deltas += deltas.len();
        summary.declared_entries += declarations(&module.verification).len();
        check_declarations(module, &current_index, &anchor_index, &deltas, errors);

        Ok(())
    }
}

#[derive(Debug, Clone)]
enum FunctionDelta {
    Added {
        current: FunctionSnapshot,
    },
    Removed {
        anchor: FunctionSnapshot,
    },
    SignatureChanged {
        current: FunctionSnapshot,
        anchor: FunctionSnapshot,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FunctionDeltaKind {
    Added,
    Removed,
    SignatureChanged,
}

impl FunctionDelta {
    fn kind(&self) -> FunctionDeltaKind {
        match self {
            FunctionDelta::Added { .. } => FunctionDeltaKind::Added,
            FunctionDelta::Removed { .. } => FunctionDeltaKind::Removed,
            FunctionDelta::SignatureChanged { .. } => FunctionDeltaKind::SignatureChanged,
        }
    }

    fn kind_name(&self) -> &'static str {
        self.kind().name()
    }

    fn describe(&self, module: &str, key: &str, declared: bool) -> String {
        let prefix = if declared { "declared" } else { "undeclared" };

        match self {
            FunctionDelta::Added { current } => format!(
                "[module {module}] {prefix} added exec function `{key}`\n  current: {}\n  signature: {}",
                current.file.display(),
                current.signature
            ),
            FunctionDelta::Removed { anchor } => format!(
                "[module {module}] {prefix} removed exec function `{key}`\n  anchor: {}\n  signature: {}",
                anchor.file.display(),
                anchor.signature
            ),
            FunctionDelta::SignatureChanged { current, anchor } => format!(
                "[module {module}] {prefix} signature-changed exec function `{key}`\n  current: {}\n  anchor: {}\n  current signature: {}\n  anchor signature: {}",
                current.file.display(),
                anchor.file.display(),
                current.signature,
                anchor.signature
            ),
        }
    }
}

impl FunctionDeltaKind {
    fn name(self) -> &'static str {
        match self {
            FunctionDeltaKind::Added => "added",
            FunctionDeltaKind::Removed => "removed",
            FunctionDeltaKind::SignatureChanged => "signature-changed",
        }
    }
}

fn diff_indexes(current: &ModuleIndex, anchor: &ModuleIndex) -> BTreeMap<String, FunctionDelta> {
    let mut keys = BTreeSet::new();
    keys.extend(current.functions.keys().cloned());
    keys.extend(anchor.functions.keys().cloned());

    let mut deltas = BTreeMap::new();
    for key in keys {
        match (current.functions.get(&key), anchor.functions.get(&key)) {
            (Some(current), None) => {
                deltas.insert(
                    key,
                    FunctionDelta::Added {
                        current: current.clone(),
                    },
                );
            }
            (None, Some(anchor)) => {
                deltas.insert(
                    key,
                    FunctionDelta::Removed {
                        anchor: anchor.clone(),
                    },
                );
            }
            (Some(current), Some(anchor)) if current.signature != anchor.signature => {
                deltas.insert(
                    key,
                    FunctionDelta::SignatureChanged {
                        current: current.clone(),
                        anchor: anchor.clone(),
                    },
                );
            }
            _ => {}
        }
    }

    deltas
}

fn check_declarations(
    module: &LoadedModule,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
    deltas: &BTreeMap<String, FunctionDelta>,
    errors: &mut Vec<String>,
) {
    let mut declared = BTreeSet::new();

    for declaration in declarations(&module.verification) {
        if !matches!(declaration.kind, &ItemKind::Function) {
            errors.push(format!(
                "[module {}] unsupported declaration type `{:?}` for `{}` in `{}`",
                module.name,
                declaration.kind,
                declaration.name,
                module.path.display()
            ));
            continue;
        }

        match declaration.section {
            DeclarationSection::Verified { .. } => {
                check_verified_declaration(
                    module,
                    declaration,
                    current_index,
                    anchor_index,
                    deltas,
                    &mut declared,
                    errors,
                );
            }
            DeclarationSection::Unsupported { anchor: Some(_) } => {
                check_mapped_delta_declaration(
                    module,
                    declaration,
                    current_index,
                    anchor_index,
                    deltas,
                    &mut declared,
                    errors,
                );
            }
            DeclarationSection::Unsupported { .. } | DeclarationSection::Planned => {
                check_delta_declaration(module, declaration, deltas, &mut declared, errors);
            }
        }
    }

    for (key, delta) in deltas {
        if !declared.contains(key) {
            errors.push(delta.describe(&module.name, key, false));
        }
    }
}

fn check_delta_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    deltas: &BTreeMap<String, FunctionDelta>,
    declared: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    match resolve_delta_key(declaration.name, deltas) {
        ResolveResult::Found(key) => {
            let delta = deltas
                .get(&key)
                .expect("resolved delta key should exist in delta map");
            if !mark_declared(module, declaration, &key, declared, errors) {
                return;
            }

            if let Err(reason) = declaration.allows_delta(delta.kind()) {
                errors.push(format!(
                    "[module {}] declaration `{}` in `{}` does not match actual {} exec function delta: {}",
                    module.name,
                    declaration.name,
                    module.path.display(),
                    delta.kind_name(),
                    reason
                ));
            }
        }
        ResolveResult::Missing => {
            errors.push(format!(
                "[module {}] stale declaration `{}` in `{}`: no exec function existence/signature delta was found",
                module.name,
                declaration.name,
                module.path.display()
            ));
        }
        ResolveResult::Ambiguous(matches) => {
            errors.push(format!(
                "[module {}] ambiguous declaration `{}` in `{}`; matches: {}",
                module.name,
                declaration.name,
                module.path.display(),
                matches.join(", ")
            ));
        }
    }
}

fn check_verified_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
    deltas: &BTreeMap<String, FunctionDelta>,
    declared: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    if declaration.anchor_name().is_some() {
        check_verified_mapped_declaration(
            module,
            declaration,
            current_index,
            anchor_index,
            deltas,
            declared,
            errors,
        );
        return;
    }

    match resolve_function_key(declaration.name, current_index, anchor_index) {
        ResolveResult::Found(key) => {
            if !mark_declared(module, declaration, &key, declared, errors) {
                return;
            }

            if let Some(delta) = deltas.get(&key) {
                match delta.kind() {
                    FunctionDeltaKind::Added => {
                        check_verified_added_declaration(
                            module,
                            declaration,
                            current_index,
                            &key,
                            errors,
                        );
                        return;
                    }
                    FunctionDeltaKind::Removed => {
                        errors.push(format!(
                            "[module {}] verified declaration `{}` in `{}` does not match actual removed exec function delta: verified APIs must exist in the current repo. Use [[unsupported]] or [[planned]] for removed exec functions.",
                            module.name,
                            declaration.name,
                            module.path.display()
                        ));
                        return;
                    }
                    FunctionDeltaKind::SignatureChanged => {}
                }
            }

            check_verified_existing_declaration(
                module,
                declaration,
                current_index,
                anchor_index,
                &key,
                errors,
            );
        }
        ResolveResult::Ambiguous(matches) => {
            errors.push(format!(
                "[module {}] ambiguous declaration `{}` in `{}`; matches: {}",
                module.name,
                declaration.name,
                module.path.display(),
                matches.join(", ")
            ));
        }
        ResolveResult::Missing => {
            errors.push(format!(
                "[module {}] verified declaration `{}` in `{}` does not match any exec function in current or anchor",
                module.name,
                declaration.name,
                module.path.display()
            ));
        }
    }
}

fn check_verified_mapped_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
    deltas: &BTreeMap<String, FunctionDelta>,
    declared: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    let Some((current_key, anchor_key)) = check_mapped_delta_declaration(
        module,
        declaration,
        current_index,
        anchor_index,
        deltas,
        declared,
        errors,
    ) else {
        return;
    };

    let current = current_index
        .functions
        .get(&current_key)
        .expect("resolved current function key should exist in current index");
    let anchor = anchor_index
        .functions
        .get(&anchor_key)
        .expect("resolved anchor function key should exist in anchor index");

    check_verified_snapshot_pair(module, declaration, current, anchor, errors);
}

fn check_mapped_delta_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
    deltas: &BTreeMap<String, FunctionDelta>,
    declared: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) -> Option<(String, String)> {
    let Some(anchor_name) = declaration.anchor_name() else {
        return None;
    };

    let current_key = match resolve_current_function_key(declaration.name, current_index) {
        ResolveResult::Found(key) => key,
        ResolveResult::Missing => {
            errors.push(format!(
                "[module {}] {} declaration `{}` in `{}` does not match any current exec function",
                module.name,
                declaration.section_name(),
                declaration.name,
                module.path.display()
            ));
            return None;
        }
        ResolveResult::Ambiguous(matches) => {
            errors.push(format!(
                "[module {}] ambiguous current name `{}` in {} declaration in `{}`; matches: {}",
                module.name,
                declaration.name,
                declaration.section_name(),
                module.path.display(),
                matches.join(", ")
            ));
            return None;
        }
    };

    let anchor_key = match resolve_anchor_function_key(anchor_name, anchor_index) {
        ResolveResult::Found(key) => key,
        ResolveResult::Missing => {
            errors.push(format!(
                "[module {}] {} declaration `{}` with anchor `{}` in `{}` does not match any anchor exec function",
                module.name,
                declaration.section_name(),
                declaration.name,
                anchor_name,
                module.path.display()
            ));
            return None;
        }
        ResolveResult::Ambiguous(matches) => {
            errors.push(format!(
                "[module {}] ambiguous anchor name `{}` for {} declaration `{}` in `{}`; matches: {}",
                module.name,
                anchor_name,
                declaration.section_name(),
                declaration.name,
                module.path.display(),
                matches.join(", ")
            ));
            return None;
        }
    };

    if current_key == anchor_key {
        if !mark_declared(module, declaration, &current_key, declared, errors) {
            return None;
        }
        return Some((current_key.clone(), anchor_key));
    }

    let current_declared = mark_declared(module, declaration, &current_key, declared, errors);
    let anchor_declared = mark_declared(module, declaration, &anchor_key, declared, errors);
    if !(current_declared && anchor_declared) {
        return None;
    }

    check_expected_mapped_delta(
        module,
        declaration,
        &current_key,
        FunctionDeltaKind::Added,
        "current",
        deltas,
        errors,
    );
    check_expected_mapped_delta(
        module,
        declaration,
        &anchor_key,
        FunctionDeltaKind::Removed,
        "anchor",
        deltas,
        errors,
    );

    Some((current_key, anchor_key))
}

fn check_verified_added_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current_index: &ModuleIndex,
    key: &str,
    errors: &mut Vec<String>,
) {
    let Some(current) = current_index.functions.get(key) else {
        errors.push(format!(
            "[module {}] verified declaration `{}` in `{}` is missing from current repo",
            module.name,
            declaration.name,
            module.path.display()
        ));
        return;
    };

    if current.has_external_body {
        errors.push(format!(
            "[module {}] verified declaration `{}` in `{}` points to an exec function with #[verifier::external_body]",
            module.name,
            declaration.name,
            module.path.display()
        ));
    }

    match declaration.rewrite_method() {
        Some(VerificationMethod::Rewrite) => {}
        Some(other) => {
            errors.push(format!(
                "[module {}] verified declaration `{}` in `{}` uses unsupported method `{:?}` for an added exec function; use `how = \"rewrite\"` if this current-only API was verified through a rewrite, otherwise use [[planned]]",
                module.name,
                declaration.name,
                module.path.display(),
                other
            ));
        }
        None => {
            errors.push(format!(
                "[module {}] verified declaration `{}` in `{}` matches an added exec function; add `how = \"rewrite\"` if this current-only API was verified through a rewrite, otherwise use [[planned]]",
                module.name,
                declaration.name,
                module.path.display()
            ));
        }
    }
}

fn check_verified_existing_declaration(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
    key: &str,
    errors: &mut Vec<String>,
) {
    let Some(current) = current_index.functions.get(key) else {
        errors.push(format!(
            "[module {}] verified declaration `{}` in `{}` is missing from current repo",
            module.name,
            declaration.name,
            module.path.display()
        ));
        return;
    };
    let Some(anchor) = anchor_index.functions.get(key) else {
        errors.push(format!(
            "[module {}] verified declaration `{}` in `{}` is missing from anchor",
            module.name,
            declaration.name,
            module.path.display()
        ));
        return;
    };

    check_verified_snapshot_pair(module, declaration, current, anchor, errors);
}

fn check_verified_snapshot_pair(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    current: &FunctionSnapshot,
    anchor: &FunctionSnapshot,
    errors: &mut Vec<String>,
) {
    if current.has_external_body {
        errors.push(format!(
            "[module {}] verified declaration `{}` in `{}` points to an exec function with #[verifier::external_body]",
            module.name,
            declaration.name,
            module.path.display()
        ));
    }

    match declaration.rewrite_method() {
        Some(VerificationMethod::Rewrite) => {
            if current.signature == anchor.signature {
                errors.push(format!(
                    "[module {}] verified/rewrite declaration `{}` in `{}` has no exec signature delta",
                    module.name,
                    declaration.name,
                    module.path.display()
                ));
            }
        }
        Some(VerificationMethod::SameSignature) | None => {
            if current.signature != anchor.signature {
                errors.push(format!(
                    "[module {}] verified declaration `{}` in `{}` has an exec signature delta; use `how = \"rewrite\"` if this API was intentionally rewritten",
                    module.name,
                    declaration.name,
                    module.path.display()
                ));
            }
        }
        Some(other) => {
            errors.push(format!(
                "[module {}] verified declaration `{}` in `{}` uses unsupported method `{:?}`; omit `how` or use `how = \"same-signature\"` for matching signatures, or use `how = \"rewrite\"` for signature changes",
                module.name,
                declaration.name,
                module.path.display(),
                other
            ));
        }
    }
}

fn check_expected_mapped_delta(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    key: &str,
    expected: FunctionDeltaKind,
    side: &str,
    deltas: &BTreeMap<String, FunctionDelta>,
    errors: &mut Vec<String>,
) {
    match deltas.get(key) {
        Some(delta) if delta.kind() == expected => {}
        Some(delta) => errors.push(format!(
            "[module {}] {} declaration `{}` in `{}` maps {side} exec function `{key}`, but it has an actual {} delta; expected {}",
            module.name,
            declaration.section_name(),
            declaration.name,
            module.path.display(),
            delta.kind_name(),
            expected.name()
        )),
        None => errors.push(format!(
            "[module {}] {} declaration `{}` in `{}` maps {side} exec function `{key}`, but no existence/signature delta was found; remove `anchor` if this API did not move",
            module.name,
            declaration.section_name(),
            declaration.name,
            module.path.display()
        )),
    }
}

fn mark_declared(
    module: &LoadedModule,
    declaration: Declaration<'_>,
    key: &str,
    declared: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) -> bool {
    if declared.insert(key.to_string()) {
        true
    } else {
        errors.push(format!(
            "[module {}] duplicate declaration for exec function `{}` resolved as `{}` in `{}`",
            module.name,
            declaration.name,
            key,
            module.path.display()
        ));
        false
    }
}

#[derive(Clone, Copy)]
struct Declaration<'a> {
    name: &'a str,
    kind: &'a ItemKind,
    section: DeclarationSection<'a>,
}

#[derive(Clone, Copy)]
enum DeclarationSection<'a> {
    Unsupported {
        anchor: Option<&'a str>,
    },
    Verified {
        how: Option<&'a VerificationMethod>,
        anchor: Option<&'a str>,
    },
    Planned,
}

impl Declaration<'_> {
    fn allows_delta(&self, _delta: FunctionDeltaKind) -> std::result::Result<(), String> {
        match &self.section {
            DeclarationSection::Unsupported { .. } => Ok(()),
            DeclarationSection::Verified { .. } => {
                Err("verified declarations are checked against current and anchor signatures; they are not delta allowlist entries".to_string())
            }
            DeclarationSection::Planned => Ok(()),
        }
    }

    fn rewrite_method(&self) -> Option<&VerificationMethod> {
        match &self.section {
            DeclarationSection::Verified { how, .. } => *how,
            _ => None,
        }
    }

    fn anchor_name(&self) -> Option<&str> {
        match &self.section {
            DeclarationSection::Unsupported { anchor } => *anchor,
            DeclarationSection::Verified { anchor, .. } => *anchor,
            _ => None,
        }
    }

    fn section_name(&self) -> &'static str {
        match &self.section {
            DeclarationSection::Unsupported { .. } => "unsupported",
            DeclarationSection::Verified { .. } => "verified",
            DeclarationSection::Planned => "planned",
        }
    }
}

fn declarations(config: &ModuleVerificationConfig) -> Vec<Declaration<'_>> {
    let mut declarations = Vec::new();

    declarations.extend(config.unsupported.iter().map(|item| Declaration {
        name: item.name.as_str(),
        kind: &item.kind,
        section: DeclarationSection::Unsupported {
            anchor: item.anchor.as_deref(),
        },
    }));
    declarations.extend(config.verified.iter().map(|item| Declaration {
        name: item.name.as_str(),
        kind: &item.kind,
        section: DeclarationSection::Verified {
            how: item.how.as_ref(),
            anchor: item.anchor.as_deref(),
        },
    }));
    declarations.extend(config.planned.iter().map(|item| Declaration {
        name: item.name.as_str(),
        kind: &item.kind,
        section: DeclarationSection::Planned,
    }));

    declarations
}

enum ResolveResult {
    Found(String),
    Missing,
    Ambiguous(Vec<String>),
}

fn resolve_delta_key(name: &str, deltas: &BTreeMap<String, FunctionDelta>) -> ResolveResult {
    resolve_key(name, deltas.keys())
}

fn resolve_current_function_key(name: &str, current_index: &ModuleIndex) -> ResolveResult {
    resolve_key(name, current_index.functions.keys())
}

fn resolve_anchor_function_key(name: &str, anchor_index: &ModuleIndex) -> ResolveResult {
    resolve_key(name, anchor_index.functions.keys())
}

fn resolve_function_key(
    name: &str,
    current_index: &ModuleIndex,
    anchor_index: &ModuleIndex,
) -> ResolveResult {
    let mut keys = BTreeSet::new();
    keys.extend(current_index.functions.keys().cloned());
    keys.extend(anchor_index.functions.keys().cloned());
    resolve_key(name, keys.iter())
}

fn resolve_key<'a>(name: &str, keys: impl Iterator<Item = &'a String>) -> ResolveResult {
    let keys = keys.cloned().collect::<Vec<_>>();
    if keys.iter().any(|key| key == name) {
        return ResolveResult::Found(name.to_string());
    }

    let matches = keys
        .iter()
        .filter(|key| declaration_matches_suffix(name, key))
        .cloned()
        .collect::<Vec<_>>();

    match matches.as_slice() {
        [key] => ResolveResult::Found(key.clone()),
        [] => ResolveResult::Missing,
        _ => ResolveResult::Ambiguous(matches),
    }
}

fn declaration_matches_suffix(name: &str, key: &str) -> bool {
    key.ends_with(&format!("::{name}")) || {
        let stripped = strip_type_generics(key);
        stripped.ends_with(&format!("::{name}"))
    }
}

fn strip_type_generics(key: &str) -> String {
    let mut out = String::new();
    let mut chars = key.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == '<'
            && out
                .chars()
                .last()
                .is_some_and(|prev| prev == '_' || prev.is_ascii_alphanumeric())
        {
            let mut depth = 1usize;
            for next in chars.by_ref() {
                match next {
                    '<' => depth += 1,
                    '>' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
            }
        } else {
            out.push(ch);
        }
    }

    out
}

fn format_errors(errors: &[String]) -> String {
    let mut report = format!(
        "found {} alignment consistency error{}",
        errors.len(),
        if errors.len() == 1 { "" } else { "s" }
    );

    for error in errors {
        report.push_str("\n\n");
        report.push_str(error);
    }

    report
}

fn prepare_anchor_repo(anchor: &AnchorConfig) -> Result<PathBuf> {
    let repo_dir = anchor_checkout_dir(anchor)?;

    if repo_dir.exists() {
        std::fs::remove_dir_all(&repo_dir).with_context(|| {
            format!(
                "failed to remove existing anchor checkout directory: {}",
                repo_dir.display()
            )
        })?;
    }

    let parent = repo_dir
        .parent()
        .context("anchor checkout directory has no parent")?;

    std::fs::create_dir_all(parent).with_context(|| {
        format!(
            "failed to create anchor checkout parent directory: {}",
            parent.display()
        )
    })?;

    clone_anchor_repo(anchor, &repo_dir)?;

    Ok(repo_dir)
}

fn clone_anchor_repo(anchor: &AnchorConfig, repo_dir: &Path) -> Result<Repository> {
    let mut fetch_options = FetchOptions::new();
    if !is_local_git_url(&anchor.git) {
        fetch_options.depth(1);
    }

    let mut builder = RepoBuilder::new();
    builder.fetch_options(fetch_options);

    let repo = builder.clone(&anchor.git, repo_dir).with_context(|| {
        format!(
            "failed to clone anchor git repository `{}` into `{}`",
            anchor.git,
            repo_dir.display()
        )
    })?;

    checkout_tag(&repo, &anchor.tag).with_context(|| {
        format!(
            "failed to checkout anchor tag `{}` in repository `{}`",
            anchor.tag,
            repo_dir.display()
        )
    })?;

    Ok(repo)
}

fn is_local_git_url(git: &str) -> bool {
    git.starts_with("file://") || Path::new(git).exists()
}

fn checkout_tag(repo: &Repository, tag: &str) -> Result<()> {
    let object = resolve_git_object(repo, tag).or_else(|_| {
        fetch_git_tag(repo, tag)?;
        resolve_git_object(repo, tag)
    })?;
    let object = object
        .peel(ObjectType::Commit)
        .or_else(|_| object.peel(ObjectType::Tree))
        .with_context(|| format!("failed to peel git tag `{tag}` to a commit or tree"))?;

    repo.checkout_tree(
        &object,
        Some(
            CheckoutBuilder::new()
                .force()
                .remove_untracked(true)
                .remove_ignored(true),
        ),
    )
    .with_context(|| format!("failed to checkout git tag `{tag}`"))?;

    repo.set_head_detached(object.id())
        .with_context(|| format!("failed to detach HEAD at git tag `{tag}`"))?;

    Ok(())
}

fn resolve_git_object<'repo>(repo: &'repo Repository, tag: &str) -> Result<Object<'repo>> {
    repo.revparse_single(&format!("refs/tags/{tag}"))
        .or_else(|_| repo.revparse_single(tag))
        .with_context(|| format!("failed to resolve git tag `{tag}`"))
}

fn fetch_git_tag(repo: &Repository, tag: &str) -> Result<()> {
    let mut remote = repo
        .find_remote("origin")
        .context("failed to find origin remote for anchor repository")?;
    let refspec = format!("+refs/tags/{tag}:refs/tags/{tag}");
    let mut fetch_options = FetchOptions::new();
    fetch_options.depth(1);
    remote
        .fetch(&[refspec.as_str()], Some(&mut fetch_options), None)
        .with_context(|| format!("failed to fetch git tag `{tag}` from origin"))?;

    Ok(())
}

fn anchor_checkout_dir(anchor: &AnchorConfig) -> Result<PathBuf> {
    let repo_name = repo_name_from_git_url(&anchor.git)
        .context("failed to derive repository name from anchor git URL")?;

    Ok(PathBuf::from("/tmp")
        .join("verification-anchor")
        .join(format!(
            "{}-{}",
            sanitize_path_component(&repo_name),
            sanitize_path_component(&anchor.tag)
        )))
}

fn repo_name_from_git_url(git: &str) -> Option<String> {
    let last = git.rsplit('/').next()?;
    let name = last.strip_suffix(".git").unwrap_or(last);

    if name.is_empty() {
        None
    } else {
        Some(name.to_string())
    }
}

fn sanitize_path_component(s: &str) -> String {
    s.chars()
        .map(|c| match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' | '.' => c,
            _ => '_',
        })
        .collect()
}
