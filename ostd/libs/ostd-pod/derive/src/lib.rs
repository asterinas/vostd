//! This crate provides a procedural macro for deriving the `Pod` trait defined in `pod-rs`.

use proc_macro2::{Ident, TokenStream};
use quote::quote;
use syn::{
    parse_macro_input, Attribute, Data, DataStruct, DataUnion, DeriveInput, Fields,
    Generics,
};

/// Deriving [`Pod`] trait for a struct or union. 
///
/// When deriving the `Pod` trait,
/// this macro performs a safety check because the `Pod` trait is marked as unsafe.
/// For structs and unions, 
/// the macro checks that the struct has a valid repr attribute (e.g., `repr(C)`, `repr(u8)`),
/// and each field is of `Pod` type.
/// Enums cannot implement the `Pod` trait.
/// 
/// If you want to implement `Pod` 
/// for a struct or union with fields that are not of Pod type,
/// you can implement it unsafely and perform the necessary checks manually.
/// 
/// [`Pod`]: https://docs.rs/pod-rs/latest/ostd_pod/trait.Pod.html
#[proc_macro_derive(Pod)]
pub fn derive_pod(input_token: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input_token as DeriveInput);
    expand_derive_pod(input).into()
}

const ALLOWED_REPRS: [&'static str; 11] = [
    "C", "u8", "i8", "u16", "i16", "u32", "i32", "u64", "i64", "usize", "isize",
];

fn expand_derive_pod(input: DeriveInput) -> TokenStream {
    let attrs = input.attrs;
    let ident = input.ident;
    let generics = input.generics;
    match input.data {
        Data::Struct(data_struct) => impl_pod_for_struct(data_struct, generics, ident, attrs),
        Data::Union(data_union) => impl_pod_for_union(data_union, generics, ident, attrs),
        Data::Enum(_) => panic!("Trying to derive `Pod` trait for enum may be unsound. Use `TryFromInt` instead."),
    }
}

fn impl_pod_for_struct(
    data_struct: DataStruct,
    generics: Generics,
    ident: Ident,
    attrs: Vec<Attribute>,
) -> TokenStream {
    if !has_valid_repr(attrs) {
        panic!("{} has invalid repr to implement Pod", ident.to_string());
    }
    let DataStruct { fields, .. } = data_struct;
    let fields = match fields {
        Fields::Named(fields_named) => fields_named.named,
        Fields::Unnamed(fields_unnamed) => fields_unnamed.unnamed,
        Fields::Unit => panic!("derive pod does not work for struct with unit field"),
    };

    // deal with generics
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    let trait_tokens = pod_trait_tokens();

    let pod_where_predicates = fields
        .into_iter()
        .map(|field| {
            let field_ty = field.ty;
            quote! {
                #field_ty: #trait_tokens
            }
        })
        .collect::<Vec<_>>();

    // if where_clause is none, we should add a `where` word manually.
    if where_clause.is_none() {
        quote! {
            #[automatically_derived]
            unsafe impl #impl_generics #trait_tokens for #ident #type_generics where #(#pod_where_predicates),* {}
        }
    } else {
        quote! {
            #[automatically_derived]
            unsafe impl #impl_generics #trait_tokens for #ident #type_generics #where_clause, #(#pod_where_predicates),* {}
        }
    }
}

fn impl_pod_for_union(
    data_union: DataUnion,
    generics: Generics,
    ident: Ident,
    attrs: Vec<Attribute>,
) -> TokenStream {
    if !has_valid_repr(attrs) {
        panic!("{} has invalid repr to implement Pod", ident.to_string());
    }
    let fields = data_union.fields.named;
    // deal with generics
    let (impl_generics, type_generics, where_clause) = generics.split_for_impl();

    let trait_tokens = pod_trait_tokens();
    let pod_where_predicates = fields
        .into_iter()
        .map(|field| {
            let field_ty = field.ty;
            quote! {
                #field_ty: #trait_tokens
            }
        })
        .collect::<Vec<_>>();

    // if where_clause is none, we should add a `where` word manually.
    if where_clause.is_none() {
        quote! {
            #[automatically_derived]
            unsafe impl #impl_generics #trait_tokens for #ident #type_generics where #(#pod_where_predicates),* {}
        }
    } else {
        quote! {
            #[automatically_derived]
            unsafe impl #impl_generics #trait_tokens for #ident #type_generics #where_clause, #(#pod_where_predicates),* {}
        }
    }
}

fn has_valid_repr(attrs: Vec<Attribute>) -> bool {
    for attr in attrs {
        if let Some(ident) = attr.path.get_ident() {
            if "repr" == ident.to_string().as_str() {
                let repr = attr.tokens.to_string();
                let repr = repr.replace("(", "").replace(")", "");
                let reprs = repr
                    .split(",")
                    .map(|one_repr| one_repr.trim())
                    .collect::<Vec<_>>();
                if let Some(_) = ALLOWED_REPRS.iter().position(|allowed_repr| {
                    reprs
                        .iter()
                        .position(|one_repr| one_repr == allowed_repr)
                        .is_some()
                }) {
                    return true;
                }
            }
        }
    }
    false
}

fn pod_trait_tokens() -> TokenStream {
    let package_name = std::env::var("CARGO_PKG_NAME").unwrap();

    // Only `ostd` and the unit test in `ostd-pod` depend on `Pod` fro `ostd-pod`,
    // other crates depend on `Pod` re-exported from ostd.
    if package_name.as_str() == "ostd" || package_name.as_str() == "ostd-pod" {
        quote! {
            ::ostd_pod::Pod
        }
    } else {
        quote! {
            ::ostd::Pod
        }
    }
}
