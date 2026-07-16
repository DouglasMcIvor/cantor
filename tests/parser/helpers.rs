use cantor::ast::{BinOp, ExprKind};
use cantor::parser::{parse_expr, parse_set_expr};

pub fn parse(src: &str) -> ExprKind {
    parse_expr(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"))
        .kind
}

pub fn parse_err(src: &str) -> String {
    parse_expr(src)
        .err()
        .unwrap_or_else(|| panic!("expected parse error for {src:?}"))
        .to_string()
}

pub fn parse_set(src: &str) -> ExprKind {
    parse_set_expr(src)
        .unwrap_or_else(|e| panic!("parse error for {src:?}: {e}"))
        .kind
}

/// Walk the AST and collect BinOp operators in inorder (lhs op rhs) order.
/// Useful for checking associativity without spelling out the full AST.
pub fn inorder_ops(kind: &ExprKind) -> Vec<BinOp> {
    match kind {
        ExprKind::BinOp { op, lhs, rhs } => {
            let mut ops = inorder_ops(&lhs.kind);
            ops.push(*op);
            ops.extend(inorder_ops(&rhs.kind));
            ops
        }
        _ => vec![],
    }
}
