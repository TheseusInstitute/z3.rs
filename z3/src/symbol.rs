use std::ffi::CString;

use z3_sys::*;

use crate::{Context, Symbol};

impl Symbol {
    pub fn as_z3_symbol(&self, ctx: &Context) -> Z3_symbol {
        match self {
            Symbol::Int(i) => unsafe { Z3_mk_int_symbol(ctx.z3_ctx, *i as ::std::os::raw::c_int) },
            Symbol::String(s) => {
                let ss = CString::new(s.clone()).unwrap();
                let p = ss.as_ptr();
                unsafe { Z3_mk_string_symbol(ctx.z3_ctx, p) }
            }
        }
    }

    pub unsafe fn wrap(ctx: &Context, sym: Z3_symbol) -> Symbol {
        assert!(
            !sym.is_null(),
            "Z3_symbol parameter is null while wrapping symbol"
        );
        match Z3_get_symbol_kind(ctx.z3_ctx, sym) {
            SymbolKind::Int => Symbol::Int(Z3_get_symbol_int(ctx.z3_ctx, sym) as u32),
            SymbolKind::String => {
                // Lifetime of the buffer is static to the context, and it is mutated on
                // each call to Z3_get_symbol_string, so we need to make our own copy.
                let sym_str_ref = Z3_get_symbol_string(ctx.z3_ctx, sym);
                assert!(
                    !sym_str_ref.is_null(),
                    "Z3_get_symbol_string returned null on a symbol result"
                );
                let sym_str_ref = ::std::ffi::CStr::from_ptr(sym_str_ref);
                Symbol::String(sym_str_ref.to_string_lossy().to_string())
            }
        }
    }
}

impl From<u32> for Symbol {
    fn from(val: u32) -> Self {
        Symbol::Int(val)
    }
}

impl From<String> for Symbol {
    fn from(val: String) -> Self {
        Symbol::String(val)
    }
}

impl From<&str> for Symbol {
    fn from(val: &str) -> Self {
        Symbol::String(val.to_owned())
    }
}
