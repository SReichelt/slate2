use metalogic_mltt::*;
use slate_kernel_metalogic::{expr::*, metalogic_context::*};

pub mod metalogic_mltt;

fn main() {
    let mltt = get_mltt();
    let root_ctx = mltt.get_root_context_with_options(MetaLogicContextOptions {
        print_all_implicit_args: true,
        ..mltt.root_ctx_options
    });

    for constant in mltt.get_constants() {
        println!("{}", constant.param.print(&root_ctx));

        for rule in &constant.reduction_rules {
            println!("    {}", rule.print(&root_ctx));
        }
        println!();
    }
}
