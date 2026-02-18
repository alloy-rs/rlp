use crate::utils::{
    attributes_include, field_ident, get_tag_value, is_optional, make_generics, parse_enum,
    parse_struct, EMPTY_STRING_CODE,
};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Result};

pub(crate) fn impl_decodable(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_struct(ast, "RlpDecodable")?;

    if attributes_include(&ast.attrs, "transparent") {
        return impl_decodable_transparent(ast, body);
    }

    let all_fields: Vec<_> = body.fields.iter().enumerate().collect();

    let supports_trailing_opt = attributes_include(&ast.attrs, "trailing");

    let last_consuming_idx = all_fields
        .iter()
        .rev()
        .find(|(_, f)| {
            !attributes_include(&f.attrs, "skip") && !attributes_include(&f.attrs, "default")
        })
        .map(|(i, _)| *i);

    let mut encountered_opt_item = false;
    let mut decode_stmts = Vec::with_capacity(body.fields.len());
    let mut decode_stmts_raw = Vec::with_capacity(body.fields.len());
    for &(i, field) in &all_fields {
        let is_flatten = attributes_include(&field.attrs, "flatten");
        if is_flatten && is_optional(field) {
            let msg = "`#[rlp(flatten)]` cannot be used on `Option<T>` fields";
            return Err(Error::new_spanned(field, msg));
        }

        let is_opt = is_optional(field);
        if is_opt {
            if !supports_trailing_opt {
                let msg = "optional fields are disabled.\nAdd the `#[rlp(trailing)]` attribute to the struct in order to enable optional fields";
                return Err(Error::new_spanned(field, msg));
            }
            encountered_opt_item = true;
        } else if encountered_opt_item && !attributes_include(&field.attrs, "default") {
            let msg =
                "all the fields after the first optional field must be either optional or default";
            return Err(Error::new_spanned(field, msg));
        }

        let is_last_consuming = last_consuming_idx == Some(i);
        decode_stmts.push(decodable_field(i, field, is_opt, is_last_consuming));
        decode_stmts_raw.push(decodable_field_raw(i, field));
    }

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpDecodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_decode(b: &mut &[u8]) -> alloy_rlp::Result<Self> {
                    let alloy_rlp::Header { list, payload_length } = alloy_rlp::Header::decode(b)?;
                    if !list {
                        return Err(alloy_rlp::ErrorKind::UnexpectedString.into());
                    }

                    let started_len = b.len();
                    if started_len < payload_length {
                        return Err(alloy_rlp::ErrorKind::InputTooShort.into());
                    }

                    let this = Self {
                        #(#decode_stmts)*
                    };

                    let consumed = started_len - b.len();
                    if consumed != payload_length {
                        return Err(alloy_rlp::ErrorKind::ListLengthMismatch {
                            expected: payload_length,
                            got: consumed,
                        }.into());
                    }

                    Ok(this)
                }

                #[inline]
                fn rlp_decode_raw(b: &mut &[u8]) -> alloy_rlp::Result<Self> {
                    Ok(Self {
                        #(#decode_stmts_raw)*
                    })
                }
            }
        };
    })
}

fn impl_decodable_transparent(
    ast: &syn::DeriveInput,
    body: &syn::DataStruct,
) -> Result<TokenStream> {
    let non_skipped: Vec<_> = body
        .fields
        .iter()
        .enumerate()
        .filter(|(_, field)| {
            !attributes_include(&field.attrs, "skip")
                && !attributes_include(&field.attrs, "default")
        })
        .collect();

    if non_skipped.len() != 1 {
        let msg = "`#[rlp(transparent)]` requires exactly one non-skipped, non-default field";
        return Err(Error::new(ast.ident.span(), msg));
    }

    let field_inits: Vec<_> = body
        .fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let ident = field_ident(i, field);
            if attributes_include(&field.attrs, "skip")
                || attributes_include(&field.attrs, "default")
            {
                quote! { #ident: alloy_rlp::private::Default::default(), }
            } else {
                quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(buf)?, }
            }
        })
        .collect();

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpDecodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::Ok(Self {
                        #(#field_inits)*
                    })
                }
            }
        };
    })
}

pub(crate) fn impl_decodable_wrapper(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_struct(ast, "RlpEncodableWrapper")?;

    if body.fields.iter().count() != 1 {
        let msg = "`RlpEncodableWrapper` is only defined for structs with one field.";
        return Err(Error::new(ast.ident.span(), msg));
    }

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpDecodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::map(alloy_rlp::RlpDecodable::rlp_decode(buf), Self)
                }
            }
        };
    })
}

fn decodable_field(
    index: usize,
    field: &syn::Field,
    is_opt: bool,
    is_last_consuming: bool,
) -> TokenStream {
    let ident = field_ident(index, field);

    if attributes_include(&field.attrs, "default") {
        quote! { #ident: alloy_rlp::private::Default::default(), }
    } else if is_opt {
        if is_last_consuming {
            // Last field: None = exhausted payload, no 0x80 sentinel check.
            quote! {
                #ident: if started_len - b.len() < payload_length {
                    Some(alloy_rlp::RlpDecodable::rlp_decode(b)?)
                } else {
                    None
                },
            }
        } else {
            // Middle field: 0x80 sentinel distinguishes None from subsequent Some values.
            quote! {
                #ident: if started_len - b.len() < payload_length {
                    if alloy_rlp::private::Option::map_or(b.first(), false, |b| *b == #EMPTY_STRING_CODE) {
                        alloy_rlp::Buf::advance(b, 1);
                        None
                    } else {
                        Some(alloy_rlp::RlpDecodable::rlp_decode(b)?)
                    }
                } else {
                    None
                },
            }
        }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode_raw(b)?, }
    } else {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(b)?, }
    }
}

fn decodable_field_raw(index: usize, field: &syn::Field) -> TokenStream {
    let ident = field_ident(index, field);

    if attributes_include(&field.attrs, "default") || attributes_include(&field.attrs, "skip") {
        quote! { #ident: alloy_rlp::private::Default::default(), }
    } else if is_optional(field) {
        // Raw mode has no framing; default to None to avoid consuming outer bytes.
        quote! { #ident: alloy_rlp::private::None, }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode_raw(b)?, }
    } else {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(b)?, }
    }
}

pub(crate) fn impl_decodable_tagged(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_enum(ast, "RlpDecodable")?;

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpDecodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let mut match_arms = Vec::new();

    for (i, variant) in body.variants.iter().enumerate() {
        let var_ident = &variant.ident;

        let tag_expr: TokenStream = get_tag_value(&variant.attrs).map_or_else(
            || {
                variant.discriminant.as_ref().map_or_else(
                    || {
                        let idx = i as u8;
                        quote! { #idx }
                    },
                    |(_, expr)| quote! { #expr },
                )
            },
            |expr| quote! { #expr },
        );

        let construct = match &variant.fields {
            syn::Fields::Named(fields) => {
                let field_decodes: Vec<_> = fields
                    .named
                    .iter()
                    .map(|f| {
                        let fname = f.ident.as_ref().unwrap();
                        quote! { #fname: alloy_rlp::RlpDecodable::rlp_decode(&mut payload)? }
                    })
                    .collect();
                quote! { #name::#var_ident { #(#field_decodes),* } }
            }
            syn::Fields::Unnamed(fields) => {
                let field_decodes: Vec<_> = (0..fields.unnamed.len())
                    .map(|_| {
                        quote! { alloy_rlp::RlpDecodable::rlp_decode(&mut payload)? }
                    })
                    .collect();
                quote! { #name::#var_ident(#(#field_decodes),*) }
            }
            syn::Fields::Unit => {
                quote! { #name::#var_ident }
            }
        };

        match_arms.push(quote! {
            #tag_expr => Ok(#construct),
        });
    }

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_decode(b: &mut &[u8]) -> alloy_rlp::Result<Self> {
                    let mut payload = alloy_rlp::Header::decode_bytes(b, true)?;
                    let tag = <u8 as alloy_rlp::RlpDecodable>::rlp_decode(&mut payload)?;
                    let result: alloy_rlp::Result<Self> = match tag {
                        #(#match_arms)*
                        _ => Err(alloy_rlp::ErrorKind::Custom("unknown variant tag").into()),
                    };
                    let value = result?;
                    if !payload.is_empty() {
                        return Err(alloy_rlp::ErrorKind::ListLengthMismatch {
                            expected: 0,
                            got: payload.len(),
                        }.into());
                    }
                    Ok(value)
                }
            }
        };
    })
}
