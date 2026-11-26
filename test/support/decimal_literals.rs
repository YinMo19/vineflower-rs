// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use vineflower_rs::decompiler::exps::{ConstantValue, literal::render};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::StructContext;
use vineflower_rs::types::VarType;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 decimal conversion"]
fn finite_decimal_literals_match_jdk17_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let reference = super::upstream_reference::Corpus::discover().run(
        "DecimalLiteralReference",
        &[],
        scratch.path(),
    );
    let mut options = Options::default();
    options.keep_literals = true;
    let mut context = StructContext::new(Arc::new(options), None);
    context
        .add_file(&scratch.path().join("classes"), true)
        .unwrap();
    let constants = context.get_class("DecimalConstants").unwrap();
    let mut cx = Cx::new(Arc::new(context));
    let mut verified = [0; 3];

    for row in reference.lines() {
        let [kind, key, expected]: [&str; 3] =
            row.splitn(3, '\t').collect::<Vec<_>>().try_into().unwrap();
        let (ty, value, kind_index) = match kind {
            "class" => {
                let field = constants
                    .fields
                    .iter()
                    .find(|field| field.name == key)
                    .unwrap();
                let attr = field.attributes.constant_value.unwrap();
                let value = constants
                    .pool
                    .get_primitive_constant(attr.index)
                    .unwrap()
                    .value;
                (VarType::from_signature(&field.descriptor), value, 0)
            }
            "float" => {
                let bits = u32::from_str_radix(key, 16).unwrap();
                (
                    VarType::VARTYPE_FLOAT,
                    ConstantValue::Float(f32::from_bits(bits)),
                    1,
                )
            }
            "double" => {
                let bits = u64::from_str_radix(key, 16).unwrap();
                (
                    VarType::VARTYPE_DOUBLE,
                    ConstantValue::Double(f64::from_bits(bits)),
                    2,
                )
            }
            _ => panic!("Unexpected reference row {row}"),
        };
        let actual = render(&mut cx, &ty, &value, None, false)
            .unwrap()
            .convert_to_string_and_allow_data_discard();
        assert_eq!(actual, expected, "{kind} {key}");
        verified[kind_index] += 1;
    }

    assert_eq!(verified[0], 22);
    assert!(verified[1] > 6_000);
    assert!(verified[2] > 25_000);
}
