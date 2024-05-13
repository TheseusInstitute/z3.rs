use std::convert::TryInto;
use std::ffi::CStr;
use std::fmt;

use z3_sys::*;

use crate::{ast, ast::Ast, Context, FuncDecl, Sort, Symbol};

impl<'ctx> FuncDecl<'ctx> {
    pub(crate) unsafe fn wrap(ctx: &'ctx Context, z3_func_decl: Z3_func_decl) -> Self {
        Z3_inc_ref(ctx.z3_ctx, Z3_func_decl_to_ast(ctx.z3_ctx, z3_func_decl));
        Self { ctx, z3_func_decl }
    }

    pub fn get_context(&self) -> &'ctx Context {
        self.ctx
    }

    pub fn get_z3_context(&self) -> Z3_context {
        self.ctx.z3_ctx
    }

    pub fn get_z3_func_decl(&self) -> Z3_func_decl {
        self.z3_func_decl
    }

    pub fn get_z3_ast(&self) -> Z3_ast {
        unsafe { Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl) }
    }

    pub fn new<S: Into<Symbol>>(
        ctx: &'ctx Context,
        name: S,
        domain: &[&Sort<'ctx>],
        range: &Sort<'ctx>,
    ) -> Self {
        assert!(domain.iter().all(|s| s.ctx.z3_ctx == ctx.z3_ctx));
        assert_eq!(ctx.z3_ctx, range.ctx.z3_ctx);

        let domain: Vec<_> = domain.iter().map(|s| s.z3_sort).collect();

        unsafe {
            Self::wrap(
                ctx,
                Z3_mk_func_decl(
                    ctx.z3_ctx,
                    name.into().as_z3_symbol(ctx),
                    domain.len().try_into().unwrap(),
                    domain.as_ptr(),
                    range.z3_sort,
                ),
            )
        }
    }

    /// Return the number of arguments of a function declaration.
    ///
    /// If the function declaration is a constant, then the arity is `0`.
    ///
    /// ```
    /// # use z3::{Config, Context, FuncDecl, Solver, Sort, Symbol};
    /// # let cfg = Config::new();
    /// # let ctx = Context::new(&cfg);
    /// let f = FuncDecl::new(
    ///     &ctx,
    ///     "f",
    ///     &[&Sort::int(&ctx), &Sort::real(&ctx)],
    ///     &Sort::int(&ctx));
    /// assert_eq!(f.arity(), 2);
    /// ```
    pub fn arity(&self) -> usize {
        unsafe { Z3_get_arity(self.ctx.z3_ctx, self.z3_func_decl) as usize }
    }

    /// Create a constant (if `args` has length 0) or function application (otherwise).
    ///
    /// Note that `args` should have the types corresponding to the `domain` of the `FuncDecl`.
    pub fn apply(&self, args: &[&dyn ast::Ast<'ctx>]) -> ast::Dynamic<'ctx> {
        assert!(args.iter().all(|s| s.get_ctx().z3_ctx == self.ctx.z3_ctx));

        let args: Vec<_> = args.iter().map(|a| a.get_z3_ast()).collect();

        unsafe {
            ast::Dynamic::wrap(self.ctx, {
                Z3_mk_app(
                    self.ctx.z3_ctx,
                    self.z3_func_decl,
                    args.len().try_into().unwrap(),
                    args.as_ptr(),
                )
            })
        }
    }

    /// Return the `DeclKind` of this `FuncDecl`.
    pub fn kind(&self) -> DeclKind {
        unsafe { Z3_get_decl_kind(self.ctx.z3_ctx, self.z3_func_decl) }
    }

    /// Return the name of this `FuncDecl`.
    ///
    /// Strings will return the `Symbol`.  Ints will have a `"k!"` prepended to
    /// the `Symbol`.
    pub fn name(&self) -> String {
        unsafe {
            let z3_ctx = self.ctx.z3_ctx;
            let symbol = Z3_get_decl_name(z3_ctx, self.z3_func_decl);
            match Z3_get_symbol_kind(z3_ctx, symbol) {
                SymbolKind::String => CStr::from_ptr(Z3_get_symbol_string(z3_ctx, symbol))
                    .to_string_lossy()
                    .into_owned(),
                SymbolKind::Int => format!("k!{}", Z3_get_symbol_int(z3_ctx, symbol)),
            }
        }
    }

    pub fn get_domain(&self, idx: usize) -> Option<Sort<'ctx>> {
        if idx >= self.arity() {
            return None;
        }

        unsafe {
            let z3_sort = Z3_get_domain(self.ctx.z3_ctx, self.z3_func_decl, idx as u32);
            if z3_sort.is_null() {
                None
            } else {
                Some(Sort::wrap(self.ctx, z3_sort))
            }
        }
    }

    pub fn get_param_name(&self, idx: usize) -> Option<Symbol> {
        if idx >= self.arity() {
            return None;
        }

        unsafe {
            let z3_sort =
                Z3_get_decl_symbol_parameter(self.ctx.z3_ctx, self.z3_func_decl, idx as u32);
            if Z3_get_error_code(self.ctx.z3_ctx) != ErrorCode::OK || z3_sort.is_null() {
                None
            } else {
                Some(Symbol::wrap(self.ctx, z3_sort))
            }
        }
    }

    pub fn into_lambda(&self) -> Option<ast::Lambda<'ctx>> {
        ast::Lambda::builder_fallible::<()>(self.ctx, |builder| {
            // Build parameters in reverse order, as this approximates de-bruijn order
            let arity = self.arity();
            let mut parameters = Vec::with_capacity(arity);
            let self_name = self.name();
            for i in (0..arity).rev() {
                let param_name: Symbol = self
                    .get_param_name(i)
                    .unwrap_or_else(|| Symbol::String(format!("{}{}", self_name.as_str(), i)));
                let var = builder.bind(param_name, self.get_domain(i).ok_or(())?);
                parameters.push(var);
            }
            parameters.reverse();

            Ok(builder.build(|_ctx| {
                let parameters = parameters
                    .iter()
                    .map(|v| v as &dyn Ast<'ctx>)
                    .collect::<Vec<_>>();
                self.apply(parameters.as_slice())
            }))
        })
        .ok()
    }

    pub fn as_dynamic(&self) -> ast::Dynamic<'ctx> {
        unsafe { ast::Dynamic::wrap(self.ctx, self.get_z3_ast()) }
    }
}

impl<'ctx> fmt::Display for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let p = unsafe { Z3_func_decl_to_string(self.ctx.z3_ctx, self.z3_func_decl) };
        if p.is_null() {
            return Result::Err(fmt::Error);
        }
        match unsafe { CStr::from_ptr(p) }.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => Result::Err(fmt::Error),
        }
    }
}

impl<'ctx> fmt::Debug for FuncDecl<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        <Self as fmt::Display>::fmt(self, f)
    }
}

impl<'ctx> Drop for FuncDecl<'ctx> {
    fn drop(&mut self) {
        unsafe {
            Z3_dec_ref(
                self.ctx.z3_ctx,
                Z3_func_decl_to_ast(self.ctx.z3_ctx, self.z3_func_decl),
            );
        }
    }
}
