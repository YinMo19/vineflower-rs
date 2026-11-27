//! EliminateDeadVarsPass, using the use graph from the current SSAU split.

use std::{io, sync::Arc};

use crate::decompiler::{
    exps::{ConstantValue, Expr, ExprKind},
    ir::{ExprId, Ir, StatId},
    sforms::{reset_versions, try_split_ssau},
    vars::var_version_pair::VarVersionPair,
};
use crate::engine::Cx;

pub(super) fn eliminate(cx: &mut Cx, root: StatId) -> io::Result<()> {
    let method = Arc::clone(root.method(&cx.ir));
    let ssau = try_split_ssau(&mut cx.ir, root, &method).map_err(|version| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("missing variable version {version}"),
        )
    })?;
    // Removed assignments leave the split's use graph in place for all sweeps.
    loop {
        let mut changed = false;
        for &node in &ssau.graph.order {
            let list = ssau.graph[node].exprents;
            let mut index = 0;
            while let Some(&expr) = cx.ir[list].get(index) {
                if let Some(pair) = removable_assignment(&cx.ir, expr) {
                    let node = ssau.versions.graph.get(pair).ok_or_else(|| {
                        io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!("missing variable version {pair}"),
                        )
                    })?;
                    if node.successors.is_empty() {
                        cx.ir[list].remove(index);
                        changed = true;
                        continue;
                    }
                }
                index += 1;
            }
        }
        if !changed {
            break;
        }
    }
    reset_versions(&mut cx.ir, root);
    Ok(())
}

fn removable_assignment(ir: &Ir, expr: ExprId) -> Option<VarVersionPair> {
    let ExprKind::Assignment { left, right, .. } = ir[expr].kind else {
        return None;
    };
    let var = Expr::variable(ir, left)?;
    let pure = match &ir[right].kind {
        ExprKind::Constant {
            value: ConstantValue::Null | ConstantValue::Integer(0),
            ..
        } => true,
        ExprKind::Field(field) => {
            field.is_static() && field.classname.as_deref() == Some("kotlin/Unit")
        }
        _ => false,
    };
    pure.then(|| var.pair())
}
