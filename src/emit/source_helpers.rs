use std::{fmt::Write, rc::Rc};

use crate::{
    descriptor::{MethodDescriptor, Type},
    lift::{
        DynamicHelper,
        invoke_groovy::{CALL_SITE, GroovyDispatch},
    },
    source_text::Document,
};

use super::{DecompileError, Writer, parse};

impl Writer<'_, '_> {
    pub(super) fn write_source_helpers(&mut self, needs_gap: &mut bool) -> Result<(), DecompileError> {
        let helpers = Rc::clone(&self.dynamic_helpers);
        for helper in &*helpers.borrow() {
            if matches!(helper, DynamicHelper::Synthetic(..)) {
                continue;
            }
            if *needs_gap {
                self.line(0, "");
            }
            match helper {
                DynamicHelper::GroovyDispatch(bridge) => self.write_groovy_dispatch(bridge)?,
                DynamicHelper::Rethrow(name) => self.write_rethrow(name),
                DynamicHelper::Synthetic(..) => unreachable!("synthetic member is not a helper"),
            }
            *needs_gap = true;
        }
        Ok(())
    }

    fn write_rethrow(&mut self, name: &str) {
        let throwable = self.names.render("java/lang/Throwable");
        let runtime = self.names.render("java/lang/RuntimeException");
        let suppression = self.names.render("java/lang/SuppressWarnings");
        self.line(1, &format!("@{suppression}(\"unchecked\")"));
        self.line(1, &format!("private static <$E extends {throwable}> {runtime} {name}({throwable} failure) throws $E {{"));
        self.line(2, "throw ($E)failure;");
        self.line(1, "}");
    }

    fn write_groovy_dispatch(&mut self, bridge: &GroovyDispatch) -> Result<(), DecompileError> {
        let pool = &self.class.pool;
        let (owner, method, descriptor) = pool.member_ref(bridge.member)?;
        let ty = parse(descriptor, MethodDescriptor::parse)?;
        let owner_type = self.names.render(owner);
        let throwable = self.names.render("java/lang/Throwable");
        let suppression = self.names.render("java/lang/SuppressWarnings");
        let result = ty.return_type.render(|name| self.names.render(name));
        let receiver = owner == CALL_SITE;
        let parameter_count = ty.parameters.len() + usize::from(receiver);
        let mut head = Document::from(format!(
            "private static <$E extends {throwable}> {result} {}",
            bridge.name,
        ));
        head.append(Document::relative_delimited_with(0..parameter_count, |head, index| {
            if receiver && index == 0 {
                head.push_str(&owner_type);
            } else {
                let ty = &ty.parameters[index - usize::from(receiver)];
                head.push_str(&ty.render(|name| self.names.render(name)));
            }
            write!(head, " arg{index}").unwrap();
        }));
        head.push_str(" throws $E");
        for &catch in &bridge.catches {
            head.push_str(", ");
            head.push_str(&self.names.render(pool.class_name(catch)?));
        }
        head.push_str(" {");

        let mut call = Document::new();
        if ty.return_type != Type::Void {
            call.push_str("return ");
        }
        call.push_str(if receiver { "arg0" } else { &owner_type });
        call.push('.');
        call.push_str(method);
        let first = usize::from(receiver);
        call.append(Document::relative_delimited_with(first..first + ty.parameters.len(), |call, index| {
            write!(call, "arg{index}").unwrap();
        }));
        call.push(';');

        self.line(1, &format!("@{suppression}(\"unchecked\")"));
        self.document_line(1, &head);
        self.line(2, "try {");
        self.document_line(3, &call);
        self.line(2, &format!("}} catch ({throwable} failure) {{"));
        // $E erases to Throwable, so the cast does not check or change failure.
        self.line(3, "throw ($E)failure;");
        self.line(2, "}");
        self.line(1, "}");
        Ok(())
    }
}
