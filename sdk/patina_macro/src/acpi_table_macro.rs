use quote::{ToTokens, quote};
use syn::{Generics, ItemStruct, parse::Parse};

struct AcpiTable {
    item: ItemStruct,
}

impl AcpiTable {
    /// Returns the name [Ident](syn::Ident) of the struct
    fn ident(&self) -> &syn::Ident {
        &self.item.ident
    }

    /// The generics for the struct
    fn generics(&self) -> Generics {
        self.item.generics.clone()
    }

    /// The left hand side generics for the struct, which can include trait bounds.
    /// Default type parameters are stripped since they are not allowed in impl blocks.
    fn lhs_generics(&self) -> Generics {
        let mut generics = self.generics();
        for param in generics.params.iter_mut() {
            if let syn::GenericParam::Type(param) = param {
                param.default = None;
            }
        }
        generics
    }

    /// The right hand side generics for the struct, which do not include trait bounds or defaults.
    ///
    /// valid: `impl<T: Debug> SomeTrait for MyStruct<T> {}`
    /// invalid: `impl SomeTrait for MyStruct<T: Debug> {}`
    /// invalid: `impl SomeTrait for MyStruct<T = i32> {}`
    fn rhs_generics(&self) -> Generics {
        let mut generics = self.generics();
        for param in generics.params.iter_mut() {
            if let syn::GenericParam::Type(param) = param {
                param.bounds.clear();
                param.default = None;
            }
        }
        generics.where_clause = None;
        generics
    }
}

impl Parse for AcpiTable {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let item = input.parse::<ItemStruct>()?;

        let Some(first_field) = item.fields.iter().next() else {
            return Err(syn::Error::new_spanned(
                item,
                "Struct must have at least one field, the first of which must be an AcpiTableHeader",
            ));
        };

        if !first_field.ty.to_token_stream().to_string().contains("AcpiTableHeader") {
            return Err(syn::Error::new_spanned(
                first_field,
                "The first field of the struct must be an AcpiTableHeader",
            ));
        }

        Ok(AcpiTable { item })
    }
}

pub(crate) fn acpi_table2(item: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let table = match syn::parse2::<AcpiTable>(item) {
        Ok(table) => table,
        Err(e) => return e.to_compile_error(),
    };

    let name = table.ident();
    let lhs = table.lhs_generics();
    let rhs = table.rhs_generics();

    quote! {
        // SAFETY: The struct has an AcpiTableHeader as its first field.
        unsafe impl patina_acpi::service::AcpiTable for #name #lhs #rhs { }
    }
}

#[cfg(test)]
#[coverage(off)]
mod tests {
    use super::*;
    use quote::quote;

    #[test]
    fn test_struct_with_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct {
                header: AcpiTableHeader,
            }
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }

    #[test]
    fn test_struct_with_mod_path_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct {
                header: patina_acpi::service::AcpiTableHeader,
            }
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }

    #[test]
    fn test_struct_with_unnamed_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct(AcpiTableHeader);
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }

    #[test]
    fn test_struct_with_mod_path_unnamed_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct(patina_acpi::service::AcpiTableHeader);
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }

    #[test]
    fn test_struct_with_multiple_named_fields_first_is_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct {
                header: AcpiTableHeader,
                a: u32,
                field2: u64,
            }
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }

    #[test]
    fn test_struct_with_multiple_unnamed_fields_first_is_header() {
        let input = quote! {
            #[derive(AcpiTable)]
            struct TestStruct(AcpiTableHeader, AAAb, u64);
        };

        let expected = quote! {
            // SAFETY: The struct has an AcpiTableHeader as its first field.
            unsafe impl patina_acpi::service::AcpiTable for TestStruct { }
        };

        assert_eq!(expected.to_string(), acpi_table2(input).to_string());
    }
}
