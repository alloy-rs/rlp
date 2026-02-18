use crate::utils::{
    attributes_include, field_ident, get_tag_value, is_optional, make_generics, parse_enum,
    parse_struct, EMPTY_STRING_CODE,
};
use proc_macro2::TokenStream;
use quote::quote;
use std::iter::Peekable;
use syn::{Error, Result};

pub(crate) fn impl_encodable(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_struct(ast, "RlpEncodable")?;

    if attributes_include(&ast.attrs, "transparent") {
        return impl_encodable_transparent(ast, body);
    }

    let mut fields = body
        .fields
        .iter()
        .enumerate()
        .filter(|(_, field)| !attributes_include(&field.attrs, "skip"))
        .peekable();

    let supports_trailing_opt = attributes_include(&ast.attrs, "trailing");

    let mut encountered_opt_item = false;
    let mut length_exprs = Vec::with_capacity(body.fields.len());
    let mut encode_exprs = Vec::with_capacity(body.fields.len());
    let mut length_exprs_raw = Vec::with_capacity(body.fields.len());
    let mut encode_exprs_raw = Vec::with_capacity(body.fields.len());

    while let Some((i, field)) = fields.next() {
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
        } else if encountered_opt_item {
            let msg = "all the fields after the first optional field must be optional";
            return Err(Error::new_spanned(field, msg));
        }

        length_exprs.push(encodable_length(i, field, is_opt, fields.clone()));
        encode_exprs.push(encodable_field(i, field, is_opt, fields.clone()));

        // Raw mode skips optional fields (symmetric with rlp_decode_raw).
        if !is_opt {
            length_exprs_raw.push(encodable_length(i, field, false, fields.clone()));
            encode_exprs_raw.push(encodable_field(i, field, false, fields.clone()));
        }
    }

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpEncodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpEncodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_len(&self) -> usize {
                    let payload_length = self._alloy_rlp_payload_length();
                    payload_length + alloy_rlp::length_of_length(payload_length)
                }

                #[inline]
                fn rlp_encode(&self, out: &mut alloy_rlp::Encoder<'_>) {
                    alloy_rlp::Header {
                        list: true,
                        payload_length: self._alloy_rlp_payload_length(),
                    }
                    .encode(out);
                    #(#encode_exprs)*
                }

                #[inline]
                fn rlp_len_raw(&self) -> usize {
                    self._alloy_rlp_payload_length_raw()
                }

                #[inline]
                fn rlp_encode_raw(&self, out: &mut alloy_rlp::Encoder<'_>) {
                    #(#encode_exprs_raw)*
                }
            }

            impl #impl_generics #name #ty_generics #where_clause {
                #[allow(unused_parens)]
                #[inline]
                fn _alloy_rlp_payload_length(&self) -> usize {
                    0usize #( + #length_exprs)*
                }

                #[allow(unused_parens)]
                #[inline]
                fn _alloy_rlp_payload_length_raw(&self) -> usize {
                    0usize #( + #length_exprs_raw)*
                }
            }
        };
    })
}

fn impl_encodable_transparent(
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

    let (index, field) = non_skipped[0];
    let ident = field_ident(index, field);

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpEncodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpEncodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_len(&self) -> usize {
                    alloy_rlp::RlpEncodable::rlp_len(&self.#ident)
                }

                #[inline]
                fn rlp_encode(&self, out: &mut alloy_rlp::Encoder<'_>) {
                    alloy_rlp::RlpEncodable::rlp_encode(&self.#ident, out)
                }
            }
        };
    })
}

pub(crate) fn impl_encodable_wrapper(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_struct(ast, "RlpEncodableWrapper")?;

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpEncodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let ident = {
        let fields: Vec<_> = body.fields.iter().collect();
        if let [field] = fields[..] {
            field_ident(0, field)
        } else {
            let msg = "`RlpEncodableWrapper` is only derivable for structs with one field";
            return Err(Error::new(name.span(), msg));
        }
    };

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpEncodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_len(&self) -> usize {
                    alloy_rlp::RlpEncodable::rlp_len(&self.#ident)
                }

                #[inline]
                fn rlp_encode(&self, out: &mut alloy_rlp::Encoder<'_>) {
                    alloy_rlp::RlpEncodable::rlp_encode(&self.#ident, out)
                }
            }
        };
    })
}

pub(crate) fn impl_max_encoded_len(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_struct(ast, "RlpMaxEncodedLen")?;

    let tys = body
        .fields
        .iter()
        .filter(|field| !attributes_include(&field.attrs, "skip"))
        .map(|field| &field.ty);

    let name = &ast.ident;

    let generics = make_generics(&ast.generics, quote!(alloy_rlp::MaxEncodedLenAssoc));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let imp = quote! {{
        let _sz = 0usize #( + <#tys as alloy_rlp::MaxEncodedLenAssoc>::LEN )*;
        _sz + alloy_rlp::length_of_length(_sz)
    }};

    // can't do operations with const generic params / associated consts in the
    // non-associated impl
    let can_derive_non_assoc = ast
        .generics
        .params
        .iter()
        .all(|g| !matches!(g, syn::GenericParam::Type(_) | syn::GenericParam::Const(_)));
    let non_assoc_impl =  can_derive_non_assoc.then(|| {
        quote! {
            unsafe impl #impl_generics alloy_rlp::MaxEncodedLen<#imp> for #name #ty_generics #where_clause {}
        }
    });

    Ok(quote! {
        #[allow(unsafe_code)]
        const _: () = {
            extern crate alloy_rlp;

            #non_assoc_impl

            unsafe impl #impl_generics alloy_rlp::MaxEncodedLenAssoc for #name #ty_generics #where_clause {
                const LEN: usize = #imp;
            }
        };
    })
}

fn encodable_length<'a>(
    index: usize,
    field: &syn::Field,
    is_opt: bool,
    mut remaining: Peekable<impl Iterator<Item = (usize, &'a syn::Field)>>,
) -> TokenStream {
    let ident = field_ident(index, field);

    if is_opt {
        let default = if remaining.peek().is_some() {
            let condition = remaining_opt_fields_some_condition(remaining);
            quote! { (#condition) as usize }
        } else {
            quote! { 0 }
        };

        quote! { self.#ident.as_ref().map(|val| alloy_rlp::RlpEncodable::rlp_len(val)).unwrap_or(#default) }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! { alloy_rlp::RlpEncodable::rlp_len_raw(&self.#ident) }
    } else {
        quote! { alloy_rlp::RlpEncodable::rlp_len(&self.#ident) }
    }
}

fn encodable_field<'a>(
    index: usize,
    field: &syn::Field,
    is_opt: bool,
    mut remaining: Peekable<impl Iterator<Item = (usize, &'a syn::Field)>>,
) -> TokenStream {
    let ident = field_ident(index, field);

    if is_opt {
        let if_some_encode = quote! {
            if let Some(val) = self.#ident.as_ref() {
                alloy_rlp::RlpEncodable::rlp_encode(val, out)
            }
        };

        if remaining.peek().is_some() {
            let condition = remaining_opt_fields_some_condition(remaining);
            quote! {
                #if_some_encode
                else if #condition {
                    out.put_u8(#EMPTY_STRING_CODE);
                }
            }
        } else {
            quote! { #if_some_encode }
        }
    } else if attributes_include(&field.attrs, "flatten") {
        quote! { alloy_rlp::RlpEncodable::rlp_encode_raw(&self.#ident, out); }
    } else {
        quote! { alloy_rlp::RlpEncodable::rlp_encode(&self.#ident, out); }
    }
}

fn remaining_opt_fields_some_condition<'a>(
    remaining: impl Iterator<Item = (usize, &'a syn::Field)>,
) -> TokenStream {
    let conditions = remaining.map(|(index, field)| {
        let ident = field_ident(index, field);
        quote! { self.#ident.is_some() }
    });
    quote! { #(#conditions)||* }
}

pub(crate) fn impl_encodable_tagged(ast: &syn::DeriveInput) -> Result<TokenStream> {
    let body = parse_enum(ast, "RlpEncodable")?;

    let name = &ast.ident;
    let generics = make_generics(&ast.generics, quote!(alloy_rlp::RlpEncodable));
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let mut length_arms = Vec::new();
    let mut encode_arms = Vec::new();

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

        match &variant.fields {
            syn::Fields::Named(fields) => {
                let field_names: Vec<_> =
                    fields.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();

                let length_fields = field_names.iter().map(|f| {
                    quote! { alloy_rlp::RlpEncodable::rlp_len(#f) }
                });
                let encode_fields = field_names.iter().map(|f| {
                    quote! { alloy_rlp::RlpEncodable::rlp_encode(#f, out); }
                });

                length_arms.push(quote! {
                    #name::#var_ident { #(ref #field_names),* } => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_len(&tag) #(+ #length_fields)*
                    }
                });
                encode_arms.push(quote! {
                    #name::#var_ident { #(ref #field_names),* } => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_encode(&tag, out);
                        #(#encode_fields)*
                    }
                });
            }
            syn::Fields::Unnamed(fields) => {
                let field_names: Vec<_> = (0..fields.unnamed.len())
                    .map(|j| syn::Ident::new(&format!("f{j}"), var_ident.span()))
                    .collect();

                let length_fields = field_names.iter().map(|f| {
                    quote! { alloy_rlp::RlpEncodable::rlp_len(#f) }
                });
                let encode_fields = field_names.iter().map(|f| {
                    quote! { alloy_rlp::RlpEncodable::rlp_encode(#f, out); }
                });

                length_arms.push(quote! {
                    #name::#var_ident(#(ref #field_names),*) => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_len(&tag) #(+ #length_fields)*
                    }
                });
                encode_arms.push(quote! {
                    #name::#var_ident(#(ref #field_names),*) => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_encode(&tag, out);
                        #(#encode_fields)*
                    }
                });
            }
            syn::Fields::Unit => {
                length_arms.push(quote! {
                    #name::#var_ident => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_len(&tag)
                    }
                });
                encode_arms.push(quote! {
                    #name::#var_ident => {
                        let tag: u8 = #tag_expr;
                        alloy_rlp::RlpEncodable::rlp_encode(&tag, out);
                    }
                });
            }
        }
    }

    Ok(quote! {
        const _: () = {
            extern crate alloy_rlp;

            impl #impl_generics alloy_rlp::RlpEncodable for #name #ty_generics #where_clause {
                #[inline]
                fn rlp_len(&self) -> usize {
                    let payload_length = match self {
                        #(#length_arms)*
                    };
                    payload_length + alloy_rlp::length_of_length(payload_length)
                }

                #[inline]
                fn rlp_encode(&self, out: &mut alloy_rlp::Encoder<'_>) {
                    let payload_length = match self {
                        #(#length_arms)*
                    };
                    alloy_rlp::Header {
                        list: true,
                        payload_length,
                    }
                    .encode(out);
                    match self {
                        #(#encode_arms)*
                    }
                }
            }
        };
    })
}
