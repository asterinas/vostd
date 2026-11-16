use anyhow::{anyhow, Result};
use cargo_metadata::MetadataCommand;
use proc_macro2::{Delimiter, TokenTree};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use syn::{Attribute, Field, Fields, File, GenericArgument, Item, ItemStruct, Type, Visibility};
use walkdir::WalkDir;

#[derive(Debug, Clone)]
pub struct StructInfo {
    pub module_path: String,
    pub name: String,
    pub attributes: Vec<String>,
    pub fields: Vec<FieldInfo>,
}

impl StructInfo {
    pub fn as_string(&self) -> String {
        let mut result = String::new();
        result.push_str(&format!("Struct: {}\n", self.name));
        result.push_str(&format!("Module Path: {}\n", self.module_path));

        if !self.attributes.is_empty() {
            result.push_str("Attributes:\n");
            for (i, attr) in self.attributes.iter().enumerate() {
                result.push_str(&format!("  [{}]: {}\n", i, attr));
            }
        }

        result.push_str("Fields:\n");
        for (i, field) in self.fields.iter().enumerate() {
            result.push_str(&format!("Field[{}] {{\n", i));
            result.push_str(&format!("  name: \"{}\",\n", field.name));
            result.push_str("  type: Type {\n");
            result.push_str(&format!("    raw: \"{}\",\n", field.field_type.raw));
            result.push_str(&format!("    ty: \"{}\",\n", field.field_type.ty));
            result.push_str(&format!(
                "    lifetimes: {:?},\n",
                field.field_type.lifetimes
            ));
            result.push_str(&format!("    generics: {:?},\n", field.field_type.generics));
            result.push_str(&format!(
                "    is_reference: {},\n",
                field.field_type.is_reference
            ));
            result.push_str(&format!(
                "    is_mutable: {},\n",
                field.field_type.is_mutable
            ));
            result.push_str(&format!("    is_array: {},\n", field.field_type.is_array));
            if let Some(size) = &field.field_type.array_size {
                result.push_str(&format!("    array_size: Some(\"{}\"),\n", size));
            } else {
                result.push_str("    array_size: None,\n");
            }
            result.push_str("  },\n");
            result.push_str(&format!("  visibility: \"{}\",\n", field.visibility));
            if !field.attributes.is_empty() {
                result.push_str("  attributes: [\n");
                for attr in &field.attributes {
                    result.push_str(&format!("    \"{}\",\n", attr));
                }
                result.push_str("  ],\n");
            } else {
                result.push_str("  attributes: [],\n");
            }
            result.push_str("}\n");
        }

        result
    }
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub name: String,
    pub field_type: TypeInfo,
    pub attributes: Vec<String>,
    pub visibility: String,
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub raw: String,
    pub ty: String,
    pub lifetimes: Vec<String>,
    pub generics: Vec<String>,
    pub is_reference: bool,
    pub is_mutable: bool,
    pub is_array: bool,
    pub array_size: Option<String>,
}

pub fn find_package(name: &str) -> Result<PathBuf> {
    match MetadataCommand::new().exec() {
        Ok(metadata) => {
            for package in metadata.packages {
                if package.name.as_str() == name {
                    let manifest_dir = package
                        .manifest_path
                        .parent()
                        .ok_or_else(|| anyhow!("Could not get parent directory of manifest"))?;
                    return Ok(manifest_dir.into());
                }
            }
            Err(anyhow!("Package '{}' not found in workspace", name))
        }
        Err(_) => {
            let current_dir = std::env::current_dir()?;
            let package_dir = current_dir.join(name);

            if package_dir.exists() && package_dir.join("Cargo.toml").exists() {
                Ok(package_dir)
            } else {
                Err(anyhow!(
                    "Package '{}' not found. Make sure you're in a cargo workspace or the package directory exists.", 
                    name
                ))
            }
        }
    }
}

pub struct Rule {
    pub data: Box<dyn std::any::Any>,
    pub trigger: fn(&Box<dyn std::any::Any>, &str, &Item) -> bool,
    pub parse: fn(&Box<dyn std::any::Any>, &str, &Item) -> Option<Box<dyn std::any::Any>>,
    pub multiple: bool,
}

impl Rule {
    pub fn rule_process_struct(struct_name: &str) -> Rule {
        Rule {
            data: Box::new(struct_name.to_owned()),
            trigger: |data, _, item| {
                if let Item::Struct(item_struct) = item {
                    item_struct.ident == data.downcast_ref::<String>().unwrap().as_str()
                } else {
                    false
                }
            },
            parse: |_, module_path, item| {
                if let Item::Struct(item_struct) = item {
                    Some(Parser::parse_struct(module_path, item_struct))
                } else {
                    None
                }
            },
            multiple: false,
        }
    }

    pub fn rule_process_structs(structs: &[String]) -> Rule {
        Rule {
            data: Box::new(structs.iter().map(|s| s.to_string()).collect::<Vec<_>>()),
            trigger: |data, _, item| {
                if let Item::Struct(item_struct) = item {
                    data.downcast_ref::<Vec<String>>()
                        .unwrap()
                        .contains(&item_struct.ident.to_string())
                } else {
                    false
                }
            },
            parse: |_, _, item| {
                if let Item::Struct(item_struct) = item {
                    Some(Box::new(item_struct.ident.to_string()))
                } else {
                    None
                }
            },
            multiple: true,
        }
    }
}

pub struct Parser {
    pub package_path: PathBuf,
    pub asts: HashMap<PathBuf, File>,
    pub rules: Vec<Rule>,
    pub output: Vec<Box<dyn std::any::Any>>,
}

impl Parser {
    pub fn new(package_name: &str) -> Self {
        let package_path = find_package(package_name).expect("Failed to find package");
        Parser {
            package_path,
            asts: HashMap::new(),
            rules: Vec::new(),
            output: Vec::new(),
        }
    }

    pub fn register(&mut self, rule: Rule) -> &mut Parser {
        self.rules.push(rule);
        self
    }

    pub fn clear_rules(&mut self) -> &mut Parser {
        self.rules.clear();
        self
    }

    pub fn load(&mut self) -> &mut Parser {
        let dir = self.package_path.join("src");
        if !dir.exists() {
            fatal!("Source directory does not exist: {:?}", dir);
        }

        for entry in WalkDir::new(&dir)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().map_or(false, |ext| ext == "rs"))
        {
            let path = entry.path();
            match fs::read_to_string(path) {
                Ok(content) => {
                    if let Ok(ast) = syn::parse_file(&content) {
                        self.asts.insert(path.to_path_buf(), ast);
                    }
                }
                Err(e) => {
                    eprintln!("Warning: cannot read file {:?}: {}", path, e);
                    continue;
                }
            }
        }
        self
    }

    pub fn parse(&mut self) -> &Self {
        for (path, ast) in self.asts.clone() {
            let mut module_path = path.to_str().unwrap_or("").to_string();
            let src_path = self
                .package_path
                .join("src")
                .to_str()
                .unwrap_or("")
                .to_string();
            module_path = module_path.replace(&src_path, "");
            module_path = module_path.trim_start_matches('/').replace('/', "::");
            // Remove .rs extension
            if module_path.ends_with(".rs") {
                module_path = module_path[..module_path.len() - 3].to_string();
            }

            self.parse_items(module_path, &ast.items);
        }
        self
    }

    /// Return true if stopped
    pub fn apply_rules(&mut self, module_path: &str, item: &Item) -> bool {
        for rule in &self.rules {
            if (rule.trigger)(&rule.data, module_path, item) {
                let output = (rule.parse)(&rule.data, module_path, item);
                if let Some(o) = output {
                    self.output.push(o);
                    if !rule.multiple {
                        return true;
                    }
                }
            }
        }
        false
    }

    // Helper method to expand verus macro
    fn expand_verus_macro(
        &self,
        tokens: &proc_macro2::TokenStream,
    ) -> Option<proc_macro2::TokenStream> {
        // Extract only the struct definitions and convert them to standard Rust syntax
        let mut expanded = Vec::new();
        let mut token_iter = tokens.clone().into_iter().peekable();

        while let Some(token) = token_iter.next() {
            match &token {
                TokenTree::Ident(ident) => {
                    let ident_str = ident.to_string();
                    match ident_str.as_str() {
                        // Keep struct definitions
                        "struct" => {
                            expanded.push(token);
                        }
                        "pub" => {
                            expanded.push(token);
                        }
                        // Skip Verus-specific keywords
                        "spec" | "open" | "recommends" | "requires" | "ensures" => {
                            // Skip these keywords and their associated content
                            self.skip_spec_content(&mut token_iter);
                            continue;
                        }
                        // Skip impl blocks with spec functions
                        "impl" => {
                            // Look ahead to see if this is a spec impl block
                            if self.is_spec_impl_block(&mut token_iter.clone()) {
                                self.skip_impl_block(&mut token_iter);
                                continue;
                            }
                            expanded.push(token);
                        }
                        // Skip macro calls that aren't standard Rust
                        name if name.starts_with("impl_") || name.ends_with("_abstract") => {
                            // Skip these macro calls
                            self.skip_macro_call(&mut token_iter);
                            continue;
                        }
                        "assume_specification" => {
                            // Skip assume_specification calls
                            self.skip_until_semicolon(&mut token_iter);
                            continue;
                        }
                        // Keep regular identifiers
                        _ => {
                            expanded.push(token);
                        }
                    }
                }
                TokenTree::Punct(punct) => {
                    // Keep punctuation except for Verus-specific operators
                    if punct.as_char() == '#' {
                        // Handle attributes - check if it's a verifier attribute
                        if let Some(TokenTree::Group(group)) = token_iter.peek() {
                            if group.delimiter() == Delimiter::Bracket {
                                let attr_content = group.stream().to_string();
                                if attr_content.contains("verifier::") {
                                    // Skip verifier attributes
                                    token_iter.next(); // consume the group
                                    continue;
                                }
                            }
                        }
                    }
                    expanded.push(token);
                }
                TokenTree::Group(group) => {
                    // Recursively process group contents
                    if let Some(processed_stream) = self.expand_verus_macro(&group.stream()) {
                        let new_group =
                            proc_macro2::Group::new(group.delimiter(), processed_stream);
                        expanded.push(TokenTree::Group(new_group));
                    } else {
                        expanded.push(token);
                    }
                }
                _ => {
                    expanded.push(token);
                }
            }
        }

        Some(proc_macro2::TokenStream::from_iter(expanded))
    }

    // Helper method to skip spec content (functions, blocks, etc.)
    fn skip_spec_content(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) {
        let mut depth = 0;
        while let Some(token) = token_iter.next() {
            match token {
                TokenTree::Group(_) => {
                    depth += 1;
                    if depth == 1 {
                        // We've found the main content block, skip it entirely
                        break;
                    }
                }
                TokenTree::Punct(punct) => {
                    if punct.as_char() == ';' && depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
        }
    }

    // Helper method to check if an impl block contains spec functions
    fn is_spec_impl_block(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) -> bool {
        let mut temp_iter = token_iter.clone();

        // Skip to the opening brace
        while let Some(token) = temp_iter.next() {
            if let TokenTree::Group(group) = token {
                if group.delimiter() == Delimiter::Brace {
                    // Check if the content contains spec functions
                    let content = group.stream().to_string();
                    return content.contains("spec")
                        || content.contains("open")
                        || content.contains("recommends");
                }
            }
        }

        false
    }

    // Helper method to skip an entire impl block
    fn skip_impl_block(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) {
        let mut depth = 0;
        while let Some(token) = token_iter.next() {
            match token {
                TokenTree::Group(group) => {
                    if group.delimiter() == Delimiter::Brace {
                        depth += 1;
                        if depth == 1 {
                            // We've found the impl block body, skip it
                            break;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Helper method to skip macro calls
    fn skip_macro_call(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) {
        while let Some(token) = token_iter.next() {
            match token {
                TokenTree::Group(_) => {
                    // Found the macro arguments, skip them
                    break;
                }
                TokenTree::Punct(punct) if punct.as_char() == ';' => {
                    // Found semicolon, end of macro call
                    break;
                }
                _ => {}
            }
        }
    }

    // Helper method to skip until semicolon
    fn skip_until_semicolon(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) {
        while let Some(token) = token_iter.next() {
            if let TokenTree::Punct(punct) = token {
                if punct.as_char() == ';' {
                    break;
                }
            }
        }
    }

    // Helper method to parse individual items when full file parsing fails
    fn parse_individual_items(&self, tokens: &proc_macro2::TokenStream) -> Option<Vec<Item>> {
        let mut items = Vec::new();
        let mut token_iter = tokens.clone().into_iter().peekable();

        while let Some(token) = token_iter.peek() {
            match token {
                TokenTree::Ident(ident) => {
                    let ident_str = ident.to_string();
                    match ident_str.as_str() {
                        "struct" => {
                            // Try to parse a struct definition
                            if let Some(struct_tokens) = self.extract_struct_tokens(&mut token_iter)
                            {
                                match syn::parse2::<syn::ItemStruct>(struct_tokens) {
                                    Ok(item_struct) => {
                                        items.push(Item::Struct(item_struct));
                                    }
                                    Err(e) => {
                                        println!("Failed to parse struct: {}", e);
                                    }
                                }
                            }
                        }
                        "enum" => {
                            // Try to parse an enum definition
                            if let Some(enum_tokens) = self.extract_enum_tokens(&mut token_iter) {
                                match syn::parse2::<syn::ItemEnum>(enum_tokens) {
                                    Ok(item_enum) => {
                                        items.push(Item::Enum(item_enum));
                                    }
                                    Err(e) => {
                                        println!("Failed to parse enum: {}", e);
                                    }
                                }
                            }
                        }
                        "pub" => {
                            // Look ahead to see what comes after pub
                            let mut temp_iter = token_iter.clone();
                            temp_iter.next(); // consume "pub"

                            if let Some(TokenTree::Ident(next_ident)) = temp_iter.peek() {
                                let next_str = next_ident.to_string();
                                match next_str.as_str() {
                                    "struct" => {
                                        if let Some(struct_tokens) =
                                            self.extract_struct_tokens(&mut token_iter)
                                        {
                                            match syn::parse2::<syn::ItemStruct>(struct_tokens) {
                                                Ok(item_struct) => {
                                                    items.push(Item::Struct(item_struct));
                                                }
                                                Err(e) => {
                                                    println!("Failed to parse pub struct: {}", e);
                                                }
                                            }
                                        }
                                    }
                                    "enum" => {
                                        if let Some(enum_tokens) =
                                            self.extract_enum_tokens(&mut token_iter)
                                        {
                                            match syn::parse2::<syn::ItemEnum>(enum_tokens) {
                                                Ok(item_enum) => {
                                                    items.push(Item::Enum(item_enum));
                                                }
                                                Err(e) => {
                                                    println!("Failed to parse pub enum: {}", e);
                                                }
                                            }
                                        }
                                    }
                                    _ => {
                                        // Skip other pub items for now
                                        token_iter.next();
                                    }
                                }
                            } else {
                                token_iter.next();
                            }
                        }
                        _ => {
                            // Skip other tokens
                            token_iter.next();
                        }
                    }
                }
                _ => {
                    // Skip non-identifier tokens
                    token_iter.next();
                }
            }
        }

        if items.is_empty() {
            None
        } else {
            Some(items)
        }
    }

    // Helper method to extract struct tokens
    fn extract_struct_tokens(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) -> Option<proc_macro2::TokenStream> {
        let mut struct_tokens = Vec::new();
        let mut found_struct = false;

        while let Some(token) = token_iter.next() {
            struct_tokens.push(token.clone());

            match &token {
                TokenTree::Ident(ident) if ident.to_string() == "struct" => {
                    found_struct = true;
                }
                TokenTree::Group(group) if found_struct => {
                    if group.delimiter() == Delimiter::Brace {
                        // Found struct body, we're done
                        break;
                    }
                }
                TokenTree::Punct(punct) if found_struct && punct.as_char() == ';' => {
                    // Found unit struct or tuple struct ending
                    break;
                }
                _ => {}
            }
        }

        if found_struct {
            Some(proc_macro2::TokenStream::from_iter(struct_tokens))
        } else {
            None
        }
    }

    // Helper method to extract enum tokens
    fn extract_enum_tokens(
        &self,
        token_iter: &mut std::iter::Peekable<proc_macro2::token_stream::IntoIter>,
    ) -> Option<proc_macro2::TokenStream> {
        let mut enum_tokens = Vec::new();
        let mut found_enum = false;

        while let Some(token) = token_iter.next() {
            enum_tokens.push(token.clone());

            match &token {
                TokenTree::Ident(ident) if ident.to_string() == "enum" => {
                    found_enum = true;
                }
                TokenTree::Group(group) if found_enum => {
                    if group.delimiter() == Delimiter::Brace {
                        // Found enum body, we're done
                        break;
                    }
                }
                _ => {}
            }
        }

        if found_enum {
            Some(proc_macro2::TokenStream::from_iter(enum_tokens))
        } else {
            None
        }
    }

    pub fn parse_items(&mut self, module_path: String, items: &[Item]) -> bool {
        for item in items {
            let stop = self.apply_rules(&module_path, item);
            if stop {
                return true;
            }
            match item {
                Item::Mod(m) => {
                    if let Some((_, items)) = &m.content {
                        let stop = self.parse_items(format!("{}::{}", module_path, m.ident), items);
                        if stop {
                            return true;
                        }
                    }
                }
                Item::Macro(m) => {
                    if m.mac.path.segments.len() > 0 && m.mac.path.segments[0].ident == "verus" {
                        if let Some(expanded_tokens) = self.expand_verus_macro(&m.mac.tokens) {
                            // Try to parse as a complete file first
                            match syn::parse2::<File>(expanded_tokens.clone()) {
                                Ok(file) => {
                                    let stop =
                                        self.parse_items(module_path.to_string(), &file.items);
                                    if stop {
                                        return true;
                                    }
                                }
                                Err(_) => {
                                    // Try to parse individual items from the token stream
                                    if let Some(parsed_items) =
                                        self.parse_individual_items(&expanded_tokens)
                                    {
                                        let stop = self
                                            .parse_items(module_path.to_string(), &parsed_items);
                                        if stop {
                                            return true;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    pub fn parse_struct(module: &str, item: &ItemStruct) -> Box<StructInfo> {
        let name = item.ident.to_string();
        let attributes = Self::parse_attributes(&item.attrs);
        let fields = Self::parse_fields(&item.fields);

        Box::new(StructInfo {
            module_path: module.to_string(),
            name,
            attributes,
            fields,
        })
    }

    pub fn parse_attributes(attrs: &[Attribute]) -> Vec<String> {
        attrs
            .iter()
            .map(|attr| quote::quote! { #attr }.to_string())
            .collect()
    }

    pub fn parse_fields(fields: &Fields) -> Vec<FieldInfo> {
        match fields {
            Fields::Named(fields_named) => fields_named
                .named
                .iter()
                .map(|field| Self::parse_field_info(field, None))
                .collect(),
            Fields::Unnamed(fields_unnamed) => fields_unnamed
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, field)| Self::parse_field_info(field, Some(i)))
                .collect(),
            Fields::Unit => vec![],
        }
    }

    pub fn parse_field_info(field: &Field, index: Option<usize>) -> FieldInfo {
        let name = if let Some(ident) = &field.ident {
            ident.to_string()
        } else if let Some(i) = index {
            i.to_string()
        } else {
            "unknown".to_string()
        };

        let field_type = Self::parse_type_info(&field.ty);
        let attributes = Self::parse_attributes(&field.attrs);
        let visibility = Self::parse_visibility(&field.vis);

        FieldInfo {
            name,
            field_type,
            attributes,
            visibility,
        }
    }

    fn parse_type_info(ty: &Type) -> TypeInfo {
        let raw = quote::quote! { #ty }.to_string();

        match ty {
            Type::Path(type_path) => {
                let mut ty_name = String::new();
                let mut lifetimes = Vec::new();
                let mut generics = Vec::new();

                // Get the type name from the path
                if let Some(segment) = type_path.path.segments.last() {
                    ty_name = segment.ident.to_string();

                    // Parse generic arguments
                    if let syn::PathArguments::AngleBracketed(args) = &segment.arguments {
                        for arg in &args.args {
                            match arg {
                                GenericArgument::Lifetime(lifetime) => {
                                    lifetimes.push(lifetime.ident.to_string());
                                }
                                GenericArgument::Type(inner_type) => {
                                    generics.push(quote::quote! { #inner_type }.to_string());
                                }
                                GenericArgument::Const(const_expr) => {
                                    generics.push(quote::quote! { #const_expr }.to_string());
                                }
                                GenericArgument::AssocType(assoc_type) => {
                                    generics.push(quote::quote! { #assoc_type }.to_string());
                                }
                                GenericArgument::AssocConst(assoc_const) => {
                                    generics.push(quote::quote! { #assoc_const }.to_string());
                                }
                                GenericArgument::Constraint(constraint) => {
                                    generics.push(quote::quote! { #constraint }.to_string());
                                }
                                _ => {}
                            }
                        }
                    }
                }

                TypeInfo {
                    raw,
                    ty: ty_name,
                    lifetimes,
                    generics,
                    is_reference: false,
                    is_mutable: false,
                    is_array: false,
                    array_size: None,
                }
            }
            Type::Reference(type_ref) => {
                let inner_type = Self::parse_type_info(&type_ref.elem);
                TypeInfo {
                    raw,
                    ty: format!("&{}", inner_type.ty),
                    lifetimes: inner_type.lifetimes,
                    generics: inner_type.generics,
                    is_reference: true,
                    is_mutable: type_ref.mutability.is_some(),
                    is_array: false,
                    array_size: None,
                }
            }
            Type::Array(type_array) => {
                let inner_type = Self::parse_type_info(&type_array.elem);
                let array_size = quote::quote! { #type_array.len }.to_string();
                TypeInfo {
                    raw,
                    ty: format!("[{}]", inner_type.ty),
                    lifetimes: inner_type.lifetimes,
                    generics: inner_type.generics,
                    is_reference: false,
                    is_mutable: false,
                    is_array: true,
                    array_size: Some(array_size),
                }
            }
            Type::Slice(type_slice) => {
                let inner_type = Self::parse_type_info(&type_slice.elem);
                TypeInfo {
                    raw,
                    ty: format!("[{}]", inner_type.ty),
                    lifetimes: inner_type.lifetimes,
                    generics: inner_type.generics,
                    is_reference: false,
                    is_mutable: false,
                    is_array: false,
                    array_size: None,
                }
            }
            Type::Tuple(type_tuple) => {
                let mut tuple_types = Vec::new();
                for elem in &type_tuple.elems {
                    tuple_types.push(quote::quote! { #elem }.to_string());
                }
                TypeInfo {
                    raw,
                    ty: "tuple".to_string(),
                    lifetimes: Vec::new(),
                    generics: tuple_types,
                    is_reference: false,
                    is_mutable: false,
                    is_array: false,
                    array_size: None,
                }
            }
            _ => {
                // Fallback for other types
                TypeInfo {
                    raw,
                    ty: "unknown".to_string(),
                    lifetimes: Vec::new(),
                    generics: Vec::new(),
                    is_reference: false,
                    is_mutable: false,
                    is_array: false,
                    array_size: None,
                }
            }
        }
    }

    fn parse_visibility(vis: &Visibility) -> String {
        match vis {
            Visibility::Public(_) => "pub".to_string(),
            Visibility::Restricted(restricted) => {
                if restricted.path.is_ident("crate") {
                    "pub(crate)".to_string()
                } else if restricted.path.is_ident("super") {
                    "pub(super)".to_string()
                } else if restricted.path.is_ident("self") {
                    "pub(self)".to_string()
                } else {
                    format!("pub({})", quote::quote! { #restricted.path })
                }
            }
            Visibility::Inherited => "private".to_string(),
        }
    }
}
