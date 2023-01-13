use smallvec::smallvec;

use crate::{context::*, context_object::*, metalogic::*};

pub fn get_mltt() -> MetaLogic {
    MetaLogic::construct(
        &[
            ("U", "U"),
            ("Pi", "Pi U (λ A : U. Fun (Fun A U) U)"),
            ("Fun", "Fun U (Fun U U)"),
        ],
        &[(&[("A", "U"), ("B", "U")], "Fun A B", "Pi A (λ _ : A. B)")],
        |ctx| Box::new(MLTTLambdaHandler::new(ctx)),
    )
    .unwrap()
}

struct MLTTLambdaHandler {
    u_idx: VarIndex,
    pi_idx: VarIndex,
    fun_idx: VarIndex,
}

impl MLTTLambdaHandler {
    fn new(ctx: &Context<Param>) -> Self {
        MLTTLambdaHandler {
            u_idx: ctx.get_var_index("U").unwrap(),
            pi_idx: ctx.get_var_index("Pi").unwrap(),
            fun_idx: ctx.get_var_index("Fun").unwrap(),
        }
    }
}

impl LambdaHandler for MLTTLambdaHandler {
    fn get_type_type(&self) -> Result<Expr, String> {
        Ok(Expr::var(self.u_idx))
    }

    fn get_pi_type(&self, domain: Expr, prop: Expr, _: &Context<Param>) -> Result<Expr, String> {
        Ok(Expr::multi_app(Expr::var(self.pi_idx), smallvec![domain, prop]))
    }

    fn get_fun_type(&self, domain: Expr, codomain: Expr, _: &Context<Param>) -> Result<Expr, String> {
        Ok(Expr::multi_app(Expr::var(self.fun_idx), smallvec![domain, codomain]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basics() {
        let mltt = get_mltt();
        let root_ctx = mltt.get_root_context();

        let pi = mltt.get_constant("Pi").unwrap();
        assert_eq!(
            pi.type_expr.print(&root_ctx),
            "Pi U (λ A : U. Fun (Fun A U) U)"
        );

        let id_ctor = Expr::parse("λ A : U. A", &root_ctx).unwrap();
        let id_ctor_type = mltt.get_expr_type(&id_ctor, &root_ctx).unwrap();
        assert_eq!(id_ctor_type.print(&root_ctx), "Pi U (λ A : U. U)");

        let app_u_pi = Expr::parse("λ F : Pi U (λ _ : U. U). F U", &root_ctx).unwrap();
        let app_u_pi_type = mltt.get_expr_type(&app_u_pi, &root_ctx).unwrap();
        assert_eq!(
            app_u_pi_type.print(&root_ctx),
            "Pi (Pi U (λ _ : U. U)) (λ F : Pi U (λ _ : U. U). U)"
        );

        let app_u_fun = Expr::parse("λ F : Fun U U. F U", &root_ctx).unwrap();
        let app_u_fun_type = mltt.get_expr_type(&app_u_fun, &root_ctx).unwrap();
        assert_eq!(
            app_u_fun_type.print(&root_ctx),
            "Pi (Fun U U) (λ F : Fun U U. U)"
        );
    }

    #[test]
    fn test_type_errors() {
        let mltt = get_mltt();
        let root_ctx = mltt.get_root_context();

        let non_fun_app = Expr::parse("λ A : U. A A", &root_ctx).unwrap();
        assert!(mltt.get_expr_type(&non_fun_app, &root_ctx).is_err());

        let app_mismatch = Expr::parse("λ F : Fun U U. F F", &root_ctx).unwrap();
        assert!(mltt.get_expr_type(&app_mismatch, &root_ctx).is_err());
    }

    #[test]
    fn test_reduction_rule_types() {
        let mltt = get_mltt();
        mltt.check_reduction_rule_types().unwrap();
    }
}
