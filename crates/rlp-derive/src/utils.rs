use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, Attribute, DataEnum, DataStruct, Error, Field, GenericParam, Generics, Meta,
    Result, Type, TypePath,
};

pub(crate) const EMPTY_STRING_CODE: u8 = 0x80;

pub(crate) fn parse_struct<'a>(
    ast: &'a syn::DeriveInput,
    derive_attr: &str,
) -> Result<&'a DataStruct> {
    if let syn::Data::Struct(s) = &ast.data {
        Ok(s)
    } else {
        Err(Error::new_spanned(
            ast,
            format!("#[derive({derive_attr})] is only defined for structs."),
        ))
    }
}

pub(crate) fn parse_enum<'a>(ast: &'a syn::DeriveInput, derive_attr: &str) -> Result<&'a DataEnum> {
    if let syn::Data::Enum(e) = &ast.data {
        Ok(e)
    } else {
        Err(Error::new_spanned(
            ast,
            format!("#[derive({derive_attr})] with `#[rlp(tagged)]` is only defined for enums."),
        ))
    }
}

pub(crate) fn attributes_include(attrs: &[Attribute], attr_name: &str) -> bool {
    for attr in attrs {
        if attr.path().is_ident("rlp") {
            if let Meta::List(meta) = &attr.meta {
                let mut found = false;
                let _ = meta.parse_nested_meta(|meta| {
                    if meta.path.is_ident(attr_name) {
                        found = true;
                    }
                    Ok(())
                });
                if found {
                    return true;
                }
            }
        }
    }
    false
}

pub(crate) fn get_tag_value(attrs: &[Attribute]) -> Result<Option<syn::Expr>> {
    let mut value = None;
    for attr in attrs {
        if attr.path().is_ident("rlp") {
            if let Meta::List(meta) = &attr.meta {
                meta.parse_nested_meta(|meta| {
                    if meta.path.is_ident("tag") {
                        value = Some(meta.value()?.parse()?);
                    }
                    Ok(())
                })?;
            }
        }
    }
    Ok(value)
}

pub(crate) fn is_optional(field: &Field) -> bool {
    if let Type::Path(TypePath { qself, path }) = &field.ty {
        qself.is_none()
            && path.leading_colon.is_none()
            && path.segments.len() == 1
            && path.segments.first().unwrap().ident == "Option"
    } else {
        false
    }
}

pub(crate) fn field_ident(index: usize, field: &syn::Field) -> TokenStream {
    field.ident.as_ref().map_or_else(
        || {
            let index = syn::Index::from(index);
            quote! { #index }
        },
        |ident| quote! { #ident },
    )
}

pub(crate) fn make_generics(generics: &Generics, trait_name: TokenStream) -> Generics {
    let mut generics = generics.clone();
    generics.make_where_clause();
    let mut where_clause = generics.where_clause.take().unwrap();

    for generic in &generics.params {
        if let GenericParam::Type(ty) = &generic {
            let t = &ty.ident;
            let pred = parse_quote!(#t: #trait_name);
            where_clause.predicates.push(pred);
        }
    }
    generics.where_clause = Some(where_clause);
    generics
}
