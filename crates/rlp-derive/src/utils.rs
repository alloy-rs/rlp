use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    parse_quote, Attribute, DataStruct, Error, Field, GenericParam, Generics, Meta, Result, Type,
    TypePath,
};

/// How a struct encodes and decodes its trailing `Option` fields, from its `#[rlp(trailing)]`
/// attribute.
#[derive(Default, Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TrailingOpts {
    /// No `trailing` attribute: `Option` fields are rejected.
    #[default]
    Disabled,
    /// `#[rlp(trailing)]`: an interior `None` is encoded as a `0x80` placeholder, and `0x80`
    /// always decodes as `None`.
    Placeholders,
    /// `#[rlp(trailing(canonical))]`: like [`Self::Placeholders`], but `0x80` only decodes as
    /// `None` when more payload follows it, so trailing `None`s must be omitted.
    Canonical,
    /// `#[rlp(trailing(no_gaps))]`: every `None` is omitted and no placeholder is written or
    /// read.
    NoGaps {
        /// `canonical` was also given. It changes nothing in the encoding, but keeps the
        /// debug assertion that the inner types never decode from `0x80`.
        canonical: bool,
    },
}

impl TrailingOpts {
    /// Returns `true` if `Option` fields are allowed.
    pub(crate) const fn enabled(self) -> bool {
        !matches!(self, Self::Disabled)
    }

    /// Returns `true` if the decoder asserts that the inner types of `Option` fields never
    /// decode from `0x80`.
    pub(crate) const fn asserts_canonical_inner_types(self) -> bool {
        matches!(self, Self::Canonical | Self::NoGaps { canonical: true })
    }
}

pub(crate) fn parse_trailing_opts(attrs: &[Attribute]) -> Result<TrailingOpts> {
    let mut enabled = false;
    let mut no_gaps = false;
    let mut canonical = false;
    let mut error = None;
    for attr in attrs {
        if attr.path().is_ident("rlp") {
            if let Meta::List(meta) = &attr.meta {
                let _ = meta.parse_nested_meta(|meta| {
                    if meta.path.is_ident("trailing") {
                        enabled = true;
                        if meta.input.peek(syn::token::Paren) {
                            // An option this parser doesn't know would silently select another
                            // wire format, so it is an error rather than ignored.
                            let parsed = meta.parse_nested_meta(|inner| {
                                if inner.path.is_ident("no_gaps") {
                                    no_gaps = true;
                                } else if inner.path.is_ident("canonical") {
                                    canonical = true;
                                } else {
                                    return Err(inner.error(
                                        "unknown `trailing` option, expected `no_gaps` or `canonical`",
                                    ));
                                }
                                Ok(())
                            });
                            if let Err(err) = parsed {
                                error.get_or_insert(err);
                            }
                        }
                    }
                    Ok(())
                });
            }
        }
    }
    if let Some(err) = error {
        return Err(err);
    }
    Ok(match (enabled, no_gaps, canonical) {
        (false, ..) => TrailingOpts::Disabled,
        (true, true, canonical) => TrailingOpts::NoGaps { canonical },
        (true, false, true) => TrailingOpts::Canonical,
        (true, false, false) => TrailingOpts::Placeholders,
    })
}

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

pub(crate) fn is_optional(field: &Field) -> bool {
    option_inner_type(field).is_some()
}

/// Extracts the inner type `T` from an `Option<T>` field, or returns `None` if the field is not
/// an `Option`.
pub(crate) fn option_inner_type(field: &Field) -> Option<&syn::Type> {
    if let Type::Path(TypePath { qself, path }) = &field.ty {
        if qself.is_none()
            && path.leading_colon.is_none()
            && path.segments.len() == 1
            && path.segments.first().unwrap().ident == "Option"
        {
            if let syn::PathArguments::AngleBracketed(args) =
                &path.segments.first().unwrap().arguments
            {
                if let Some(syn::GenericArgument::Type(inner)) = args.args.first() {
                    return Some(inner);
                }
            }
        }
    }
    None
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

#[cfg(test)]
mod tests {
    use super::*;
    use syn::parse_quote;

    #[test]
    fn unknown_trailing_option_is_not_ignored() {
        // A misspelled option used to fall back to the placeholder mode silently, which accepts
        // non-canonical encodings the struct asked to reject.
        let attrs: [Attribute; 1] = [parse_quote!(#[rlp(trailing(cannonical))])];
        assert_eq!(
            parse_trailing_opts(&attrs).unwrap_err().to_string(),
            "unknown `trailing` option, expected `no_gaps` or `canonical`"
        );

        let attrs: [Attribute; 1] = [parse_quote!(#[rlp(trailing(no_gaps, canonical))])];
        assert_eq!(parse_trailing_opts(&attrs).unwrap(), TrailingOpts::NoGaps { canonical: true });
        let attrs: [Attribute; 1] = [parse_quote!(#[rlp(trailing)])];
        assert_eq!(parse_trailing_opts(&attrs).unwrap(), TrailingOpts::Placeholders);
    }
}
