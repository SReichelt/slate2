use std::fmt::Display;

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields};

#[proc_macro_derive(ContextObject)]
pub fn context_object_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let shift_impl =
        call_for_each_field(&input, |field| quote!(#field.shift_impl(start, end, shift)));

    let shifted_impl = construct_from_fields(
        &input,
        |field| quote!(#field.shifted_impl(start, end, shift)),
    );

    let count_refs_impl = call_for_each_field(
        &input,
        |field| quote!(#field.count_refs_impl(start, ref_counts)),
    );

    let has_refs_impl = for_each_field(
        &input,
        |field| quote!(#field.has_refs_impl(start, end)),
        |values| quote!(false #(|| #values)*),
    );

    let name = input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics slate_kernel_generic::context_object::ContextObject for #name #ty_generics #where_clause {
            fn shift_impl(&mut self, start: VarIndex, end: VarIndex, shift: VarIndex) {
                #shift_impl
            }

            fn shifted_impl(&self, start: VarIndex, end: VarIndex, shift: VarIndex) -> Self {
                #shifted_impl
            }

            fn count_refs_impl(&self, start: VarIndex, ref_counts: &mut [usize]) {
                #count_refs_impl
            }

            fn has_refs_impl(&self, start: VarIndex, end: VarIndex) -> bool {
                #has_refs_impl
            }
        }
    };
    expanded.into()
}

fn call_for_each_field(
    input: &DeriveInput,
    f: impl FnMut(Ident) -> proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    for_each_field(input, f, |calls| quote!(#( #calls; )*))
}

fn for_each_field(
    input: &DeriveInput,
    mut f: impl FnMut(Ident) -> proc_macro2::TokenStream,
    mut combine: impl FnMut(Vec<proc_macro2::TokenStream>) -> proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match &input.data {
        Data::Struct(data) => {
            let params = get_field_params(&data.fields);
            let result = combine(map_fields(&data.fields, f));
            quote! {
                let Self #params = self;
                #result
            }
        }
        Data::Enum(data) => {
            let arms = data.variants.iter().map(|variant| {
                let name = &variant.ident;
                let params = get_field_params(&variant.fields);
                let result = combine(map_fields(&variant.fields, |ident| f(ident)));
                quote!(Self::#name #params => { #result })
            });
            quote! {
                match self {
                    #(#arms)*
                }
            }
        }
        _ => quote!(compile_error!("data type must be struct or enum")),
    }
}

fn construct_from_fields(
    input: &DeriveInput,
    mut f: impl FnMut(Ident) -> proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match &input.data {
        Data::Struct(data) => {
            let params = get_field_params(&data.fields);
            let args = get_field_args(&data.fields, f);
            quote! {
                let Self #params = self;
                Self #args
            }
        }
        Data::Enum(data) => {
            let arms = data.variants.iter().map(|variant| {
                let name = &variant.ident;
                let params = get_field_params(&variant.fields);
                let args = get_field_args(&variant.fields, |ident| f(ident));
                quote!(Self::#name #params => Self::#name #args)
            });
            quote! {
                match self {
                    #(#arms),*
                }
            }
        }
        _ => quote!(compile_error!("data type must be struct or enum")),
    }
}

fn get_field_params(fields: &Fields) -> proc_macro2::TokenStream {
    get_field_args(fields, |ident| quote!(#ident))
}

fn get_field_args(
    fields: &Fields,
    mut f: impl FnMut(Ident) -> proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match fields {
        Fields::Named(fields) => {
            let initializers = fields.named.iter().map(|field| {
                let name = field.ident.as_ref().unwrap();
                let value = f(make_ident(name));
                quote!(#name: #value)
            });
            quote!({ #(#initializers),* })
        }
        Fields::Unnamed(fields) => {
            let values = fields
                .unnamed
                .iter()
                .enumerate()
                .map(|(i, _)| f(make_ident(i)));
            quote!(( #(#values),* ))
        }
        Fields::Unit => proc_macro2::TokenStream::new(),
    }
}

fn map_fields(
    fields: &Fields,
    mut f: impl FnMut(Ident) -> proc_macro2::TokenStream,
) -> Vec<proc_macro2::TokenStream> {
    match fields {
        Fields::Named(fields) => fields
            .named
            .iter()
            .map(|field| f(make_ident(field.ident.as_ref().unwrap())))
            .collect(),
        Fields::Unnamed(fields) => fields
            .unnamed
            .iter()
            .enumerate()
            .map(|(i, _)| f(make_ident(i)))
            .collect(),
        Fields::Unit => Vec::new(),
    }
}

fn make_ident(s: impl Display) -> Ident {
    Ident::new(&format!("_{s}"), Span::call_site())
}
