use std::collections::BTreeMap;
use std::path::{Component, Path, PathBuf};

use anyhow::{Context, Result};
use quote::{ToTokens, quote};
use verus_syn::punctuated::Punctuated;
use verus_syn::{
    Attribute, File, FnArg, FnArgKind, FnMode, GenericArgument, ImplItem, Item, Pat,
    Path as SynPath, PathArguments, Signature, TraitItem, Type, Visibility,
};

#[derive(Debug, Clone)]
pub struct FunctionSnapshot {
    pub signature: String,
    pub file: PathBuf,
    pub has_external_body: bool,
}

#[derive(Debug, Default)]
pub struct ModuleIndex {
    pub functions: BTreeMap<String, FunctionSnapshot>,
    pub errors: Vec<String>,
}

pub fn index_module(module_dir: &Path) -> Result<ModuleIndex> {
    let mut files = Vec::new();
    collect_rs_files(module_dir, &mut files)?;
    files.sort();

    let mut index = ModuleIndex::default();
    for file in files {
        let source = std::fs::read_to_string(&file)
            .with_context(|| format!("failed to read Rust source file: {}", file.display()))?;
        match verus_syn::parse_file(&source) {
            Ok(parsed) => {
                let module_path = file_module_path(module_dir, &file);
                collect_file_items(&mut index, &file, module_path, &parsed);
            }
            Err(err) => {
                index.errors.push(format!(
                    "failed to parse Rust source file `{}`: {err}",
                    file.display()
                ));
            }
        }
    }

    Ok(index)
}

fn collect_rs_files(dir: &Path, files: &mut Vec<PathBuf>) -> Result<()> {
    for entry in std::fs::read_dir(dir)
        .with_context(|| format!("failed to read module directory: {}", dir.display()))?
    {
        let entry =
            entry.with_context(|| format!("failed to read entry under: {}", dir.display()))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .with_context(|| format!("failed to read file type: {}", path.display()))?;

        if file_type.is_dir() {
            collect_rs_files(&path, files)?;
        } else if file_type.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }

    Ok(())
}

fn file_module_path(module_dir: &Path, file: &Path) -> Vec<String> {
    let rel = file.strip_prefix(module_dir).unwrap_or(file);
    let mut components = Vec::new();
    let file_name = rel.file_name().and_then(|name| name.to_str()).unwrap_or("");

    for component in rel.components() {
        let Component::Normal(raw) = component else {
            continue;
        };
        let component = raw.to_string_lossy();

        if component == file_name {
            match file.file_stem().and_then(|stem| stem.to_str()) {
                Some("mod") | Some("lib") | Some("main") => {}
                Some(stem) => components.push(stem.to_string()),
                None => {}
            }
        } else {
            components.push(component.to_string());
        }
    }

    components
}

fn collect_file_items(
    index: &mut ModuleIndex,
    file: &Path,
    module_path: Vec<String>,
    file_ast: &File,
) {
    collect_items(index, file, &module_path, &file_ast.items);
}

fn collect_items(index: &mut ModuleIndex, file: &Path, module_path: &[String], items: &[Item]) {
    for item in items {
        match item {
            Item::Fn(item_fn) => {
                collect_function(
                    index,
                    file,
                    module_path,
                    None,
                    Some(&item_fn.vis),
                    &item_fn.attrs,
                    &item_fn.sig,
                );
            }
            Item::Impl(item_impl) => {
                let owner = impl_owner_name(item_impl);
                for impl_item in &item_impl.items {
                    if let ImplItem::Fn(item_fn) = impl_item {
                        collect_function(
                            index,
                            file,
                            module_path,
                            Some(&owner),
                            Some(&item_fn.vis),
                            &item_fn.attrs,
                            &item_fn.sig,
                        );
                    }
                }
            }
            Item::Trait(item_trait) => {
                let owner = item_trait.ident.to_string();
                for trait_item in &item_trait.items {
                    if let TraitItem::Fn(item_fn) = trait_item {
                        collect_function(
                            index,
                            file,
                            module_path,
                            Some(&owner),
                            None,
                            &item_fn.attrs,
                            &item_fn.sig,
                        );
                    }
                }
            }
            Item::Mod(item_mod) => {
                if let Some((_, nested_items)) = &item_mod.content {
                    let mut nested_path = module_path.to_vec();
                    nested_path.push(item_mod.ident.to_string());
                    collect_items(index, file, &nested_path, nested_items);
                }
            }
            Item::Macro(item_macro) if is_verus_macro(&item_macro.mac.path) => {
                match verus_syn::parse2::<File>(item_macro.mac.tokens.clone()) {
                    Ok(file_ast) => collect_items(index, file, module_path, &file_ast.items),
                    Err(err) => index.errors.push(format!(
                        "failed to parse verus! block in `{}`: {err}",
                        file.display()
                    )),
                }
            }
            _ => {}
        }
    }
}

fn collect_function(
    index: &mut ModuleIndex,
    file: &Path,
    module_path: &[String],
    owner: Option<&str>,
    vis: Option<&Visibility>,
    attrs: &[Attribute],
    sig: &Signature,
) {
    if !is_exec_signature(sig) {
        return;
    }

    let key = function_key(module_path, owner, &sig.ident.to_string());
    let signature = canonical_signature(vis, sig);
    let snapshot = FunctionSnapshot {
        signature,
        file: file.to_path_buf(),
        has_external_body: has_external_body(attrs),
    };

    if let Some(existing) = index.functions.insert(key.clone(), snapshot) {
        index.errors.push(format!(
            "duplicate exec function key `{key}` in `{}` and `{}`",
            existing.file.display(),
            file.display()
        ));
    }
}

fn is_exec_signature(sig: &Signature) -> bool {
    matches!(sig.mode, FnMode::Default | FnMode::Exec(_))
}

fn canonical_signature(vis: Option<&Visibility>, sig: &Signature) -> String {
    let mut sig = sig.clone();
    sig.erase_spec_fields();
    sig.mode = FnMode::Default;
    sig.inputs = sig
        .inputs
        .iter()
        .filter(|arg| !is_ghost_or_tracked_arg(arg))
        .cloned()
        .collect::<Punctuated<FnArg, verus_syn::Token![,]>>();

    let tokens = match vis {
        Some(vis) => quote! { #vis #sig },
        None => quote! { #sig },
    };
    tokens.to_string()
}

fn has_external_body(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let attr = normalize_tokens(attr);
        attr.contains("verifier :: external_body")
            || attr.contains("verifier::external_body")
            || attr.contains("external_body")
    })
}

fn is_ghost_or_tracked_arg(arg: &FnArg) -> bool {
    if arg.tracked.is_some() {
        return true;
    }

    let FnArgKind::Typed(pat_type) = &arg.kind else {
        return false;
    };

    is_wrapper_type(&pat_type.ty, "Tracked")
        || is_wrapper_type(&pat_type.ty, "Ghost")
        || is_wrapper_pat(&pat_type.pat, "Tracked")
        || is_wrapper_pat(&pat_type.pat, "Ghost")
}

fn is_wrapper_type(ty: &Type, wrapper: &str) -> bool {
    match ty {
        Type::Path(type_path) => type_path
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == wrapper),
        Type::Paren(type_paren) => is_wrapper_type(&type_paren.elem, wrapper),
        Type::Group(type_group) => is_wrapper_type(&type_group.elem, wrapper),
        _ => false,
    }
}

fn is_wrapper_pat(pat: &Pat, wrapper: &str) -> bool {
    match pat {
        Pat::TupleStruct(tuple) => tuple
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == wrapper),
        Pat::Paren(paren) => is_wrapper_pat(&paren.pat, wrapper),
        _ => false,
    }
}

fn function_key(module_path: &[String], owner: Option<&str>, name: &str) -> String {
    let mut parts = module_path.to_vec();
    if let Some(owner) = owner {
        parts.push(owner.to_string());
    }
    parts.push(name.to_string());
    parts.join("::")
}

fn impl_owner_name(item_impl: &verus_syn::ItemImpl) -> String {
    let self_ty = simplify_type_name(&item_impl.self_ty);
    match &item_impl.trait_ {
        Some((_, trait_path, _)) => {
            format!("<{} as {}>", self_ty, simplify_path_name(trait_path))
        }
        None => self_ty,
    }
}

fn simplify_type_name(ty: &Type) -> String {
    match ty {
        Type::Path(type_path) => simplify_path_name(&type_path.path),
        Type::Reference(type_ref) => simplify_type_name(&type_ref.elem),
        Type::Paren(type_paren) => simplify_type_name(&type_paren.elem),
        Type::Group(type_group) => simplify_type_name(&type_group.elem),
        _ => normalize_tokens(ty),
    }
}

fn simplify_path_name(path: &SynPath) -> String {
    let Some(segment) = path.segments.last() else {
        return normalize_tokens(path);
    };

    let ident = segment.ident.to_string();
    let PathArguments::AngleBracketed(args) = &segment.arguments else {
        return ident;
    };

    let args = args
        .args
        .iter()
        .filter_map(|arg| match arg {
            GenericArgument::Lifetime(_) => None,
            _ => Some(normalize_tokens(arg)),
        })
        .collect::<Vec<_>>();

    if args.is_empty() {
        ident
    } else {
        format!("{}<{}>", ident, args.join(","))
    }
}

fn is_verus_macro(path: &SynPath) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "verus")
}

fn normalize_tokens<T: ToTokens>(value: &T) -> String {
    value.to_token_stream().to_string()
}
