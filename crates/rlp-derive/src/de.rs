use crate::utils::{
    attributes_include, field_ident, get_tag_value, is_optional, make_generics, option_inner_type,
    parse_enum, parse_struct, EMPTY_STRING_CODE,
};
use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Result};

pub(crate) fn impl_decodable(ast: &syn::DeriveInput) -> Result<TokenStream> {
    if attributes_include(&ast.attrs, "tagged") {
        return impl_decodable_tagged(ast);
    }
    if matches!(ast.data, syn::Data::Enum(_)) {
        let msg = "RLP enum derives require `#[rlp(tagged)]`";
        return Err(Error::new_spanned(ast, msg));
    }

    let body = parse_struct(ast, "RlpDecodable")?;

    if attributes_include(&ast.attrs, "transparent") {
        return impl_decodable_transparent(ast, body);
    }

    let all_fields: Vec<_> = body.fields.iter().enumerate().collect();

    let supports_trailing_opt = attributes_include(&ast.attrs, "trailing");

    let last_consuming_idx = all_fields
        .iter()
        .rev()
        .find(|(_, field)| {
            !attributes_include(&field.attrs, "skip")
                && !attributes_include(&field.attrs, "default")
        })
        .map(|(i, _)| *i);

    let mut encountered_opt_item = false;
    let mut decode_stmts = Vec::with_capacity(body.fields.len());
    let mut decode_stmts_raw = Vec::with_capacity(body.fields.len());
    let mut min_raw_item_exprs = Vec::with_capacity(body.fields.len());
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

        let tail_items = min_raw_items_from(all_fields.iter().copied().filter(|(j, _)| *j > i));
        let is_last_consuming = last_consuming_idx == Some(i);
        decode_stmts.push(decodable_field(i, field, is_opt, is_last_consuming, &tail_items));
        decode_stmts_raw.push(decodable_field_raw(i, field, &tail_items));
        if let Some(expr) = min_raw_items_field(field) {
            min_raw_item_exprs.push(expr);
        }
    }

    let name = &ast.ident;
    let generics = make_decode_generics(&ast.generics);
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = ast.generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable<'__alloy_rlp_de> for #name #ty_generics #where_clause {
                const MIN_RAW_ITEMS: usize = 0usize #( + #min_raw_item_exprs)*;

                #[inline]
                fn rlp_decode(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    let mut b = decoder.decode_payload(true)?;
                    let started_len = b.len();

                    let this = Self {
                        #(#decode_stmts)*
                    };

                    let consumed = started_len.saturating_sub(b.len());
                    if consumed != started_len {
                        return Err(b.error(alloy_rlp::ErrorKind::ListLengthMismatch {
                            expected: started_len,
                            got: consumed,
                        }));
                    }

                    Ok(this)
                }

                #[inline]
                fn rlp_decode_raw(b: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
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
        .filter(|(_, field)| !attributes_include(&field.attrs, "skip"))
        .collect();

    if non_skipped.len() != 1 {
        let msg = "`#[rlp(transparent)]` requires exactly one non-skipped field";
        return Err(Error::new(ast.ident.span(), msg));
    }

    let (_, non_skipped_field) = non_skipped[0];
    let non_skipped_ty = &non_skipped_field.ty;

    let field_inits: Vec<_> = body
        .fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let ident = field_ident(i, field);
            if attributes_include(&field.attrs, "skip") {
                quote! { #ident: alloy_rlp::private::Default::default(), }
            } else {
                quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(decoder)?, }
            }
        })
        .collect();

    let field_inits_raw: Vec<_> = body
        .fields
        .iter()
        .enumerate()
        .map(|(i, field)| {
            let ident = field_ident(i, field);
            if attributes_include(&field.attrs, "skip") {
                quote! { #ident: alloy_rlp::private::Default::default(), }
            } else {
                quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode_raw(decoder)?, }
            }
        })
        .collect();

    let name = &ast.ident;
    let generics = make_decode_generics(&ast.generics);
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = ast.generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable<'__alloy_rlp_de> for #name #ty_generics #where_clause {
                const MIN_RAW_ITEMS: usize = <#non_skipped_ty as alloy_rlp::RlpDecodable<'__alloy_rlp_de>>::MIN_RAW_ITEMS;

                #[inline]
                fn rlp_decode(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::Ok(Self {
                        #(#field_inits)*
                    })
                }

                #[inline]
                fn rlp_decode_raw(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::Ok(Self {
                        #(#field_inits_raw)*
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
    let field_ty = body.fields.iter().next().map(|field| &field.ty).unwrap();
    let generics = make_decode_generics(&ast.generics);
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = ast.generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable<'__alloy_rlp_de> for #name #ty_generics #where_clause {
                const MIN_RAW_ITEMS: usize = <#field_ty as alloy_rlp::RlpDecodable<'__alloy_rlp_de>>::MIN_RAW_ITEMS;

                #[inline]
                fn rlp_decode(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::map(alloy_rlp::RlpDecodable::rlp_decode(decoder), Self)
                }

                #[inline]
                fn rlp_decode_raw(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    alloy_rlp::private::Result::map(alloy_rlp::RlpDecodable::rlp_decode_raw(decoder), Self)
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
    tail_items: &TokenStream,
) -> TokenStream {
    let ident = field_ident(index, field);

    if attributes_include(&field.attrs, "default") || attributes_include(&field.attrs, "skip") {
        quote! { #ident: alloy_rlp::private::Default::default(), }
    } else if is_opt {
        if is_last_consuming {
            quote! {
                #ident: if !b.is_empty() {
                    Some(alloy_rlp::RlpDecodable::rlp_decode(&mut b)?)
                } else {
                    None
                },
            }
        } else {
            quote! {
                #ident: if !b.is_empty() {
                    if b.peek() == Some(#EMPTY_STRING_CODE) {
                        b.advance(1)?;
                        None
                    } else {
                        Some(alloy_rlp::RlpDecodable::rlp_decode(&mut b)?)
                    }
                } else {
                    None
                },
            }
        }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! {
            #ident: {
                let raw_tail_items = b.raw_tail_items().saturating_add(#tail_items);
                b.with_raw_tail_items(raw_tail_items, |b| alloy_rlp::RlpDecodable::rlp_decode_raw(b))?
            },
        }
    } else {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(&mut b)?, }
    }
}

fn decodable_field_raw(index: usize, field: &syn::Field, tail_items: &TokenStream) -> TokenStream {
    let ident = field_ident(index, field);

    if attributes_include(&field.attrs, "default") || attributes_include(&field.attrs, "skip") {
        quote! { #ident: alloy_rlp::private::Default::default(), }
    } else if is_optional(field) {
        let inner_ty = option_inner_type(field).expect("checked optional field");
        quote! { #ident: alloy_rlp::private::decode_optional_raw::<#inner_ty>(b, #tail_items)?, }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! {
            #ident: {
                let raw_tail_items = b.raw_tail_items().saturating_add(#tail_items);
                b.with_raw_tail_items(raw_tail_items, |b| alloy_rlp::RlpDecodable::rlp_decode_raw(b))?
            },
        }
    } else {
        quote! { #ident: alloy_rlp::RlpDecodable::rlp_decode(b)?, }
    }
}

pub(crate) fn impl_decodable_tagged(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_enum(ast, "RlpDecodable")?;

    let name = &ast.ident;
    let generics = make_decode_generics(&ast.generics);
    let (impl_generics, _, where_clause) = generics.split_for_impl();
    let (_, ty_generics, _) = ast.generics.split_for_impl();

    let mut match_arms = Vec::new();

    for (i, variant) in body.variants.iter().enumerate() {
        let var_ident = &variant.ident;
        let tag_expr = variant_tag_expr(i, variant)?;

        let construct = match &variant.fields {
            syn::Fields::Named(fields) => {
                let field_decodes = fields.named.iter().map(|f| {
                    let fname = f.ident.as_ref().unwrap();
                    quote! { #fname: alloy_rlp::RlpDecodable::rlp_decode(&mut payload)? }
                });
                quote! { #name::#var_ident { #(#field_decodes),* } }
            }
            syn::Fields::Unnamed(fields) => {
                let field_decodes = (0..fields.unnamed.len())
                    .map(|_| quote! { alloy_rlp::RlpDecodable::rlp_decode(&mut payload)? });
                quote! { #name::#var_ident(#(#field_decodes),*) }
            }
            syn::Fields::Unit => quote! { #name::#var_ident },
        };

        match_arms.push(quote! {
            tag if tag == (#tag_expr) as u64 => alloy_rlp::private::Ok(#construct),
        });
    }

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpDecodable<'__alloy_rlp_de> for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_decode(decoder: &mut alloy_rlp::Decoder<'__alloy_rlp_de>) -> alloy_rlp::Result<Self> {
                    let mut payload = decoder.decode_payload(true)?;
                    let tag = <u64 as alloy_rlp::RlpDecodable<'__alloy_rlp_de>>::rlp_decode(&mut payload)?;
                    let value = match tag {
                        #(#match_arms)*
                        _ => alloy_rlp::private::Err(alloy_rlp::Error::from(alloy_rlp::ErrorKind::Custom("unknown variant tag"))),
                    }?;
                    if !payload.is_empty() {
                        return alloy_rlp::private::Err(payload.error(alloy_rlp::ErrorKind::ListLengthMismatch {
                            expected: 0,
                            got: payload.len(),
                        }));
                    }
                    alloy_rlp::private::Ok(value)
                }
            }
        };
    })
}

fn variant_tag_expr(index: usize, variant: &syn::Variant) -> Result<TokenStream> {
    Ok(get_tag_value(&variant.attrs)?.map_or_else(
        || {
            variant.discriminant.as_ref().map_or_else(
                || {
                    let index = index as u64;
                    quote! { #index }
                },
                |(_, expr)| quote! { #expr },
            )
        },
        |expr| quote! { #expr },
    ))
}

fn make_decode_generics(generics: &syn::Generics) -> syn::Generics {
    let mut generics = make_generics(generics, quote!(alloy_rlp::RlpDecodable<'__alloy_rlp_de>));
    generics.params.insert(0, syn::parse_quote!('__alloy_rlp_de));
    generics
}

fn min_raw_items_from<'a>(fields: impl Iterator<Item = (usize, &'a syn::Field)>) -> TokenStream {
    let exprs = fields.filter_map(|(_, field)| min_raw_items_field(field));
    quote! { 0usize #( + #exprs)* }
}

fn min_raw_items_field(field: &syn::Field) -> Option<TokenStream> {
    if attributes_include(&field.attrs, "default")
        || attributes_include(&field.attrs, "skip")
        || is_optional(field)
    {
        None
    } else if attributes_include(&field.attrs, "flatten") {
        let ty = &field.ty;
        Some(quote! { <#ty as alloy_rlp::RlpDecodable<'__alloy_rlp_de>>::MIN_RAW_ITEMS })
    } else {
        Some(quote! { 1usize })
    }
}
