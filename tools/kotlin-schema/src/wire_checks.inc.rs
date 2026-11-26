use super::proto::*;

pub(super) trait CheckWire {
    fn check_wire(&mut self) -> Result<(), &'static str>;
}

macro_rules! check_wire {
    (
        $type:ty;
        required [$($required:ident: $description:literal),*],
        optional [$($optional:ident),*],
        repeated [$($repeated:ident),*],
        enums [$($enum:ident: $variant:path),*],
    ) => {
        impl CheckWire for $type {
            fn check_wire(&mut self) -> Result<(), &'static str> {
                $(
                    if self.$enum.is_some_and(|value| <$variant>::try_from(value).is_err()) {
                        self.$enum = None;
                    }
                )*
                $(
                    if self.$required.is_none() {
                        return Err($description);
                    }
                )*
                $(
                    if let Some(value) = &mut self.$optional {
                        value.check_wire()?;
                    }
                )*
                $(
                    for value in &mut self.$repeated {
                        value.check_wire()?;
                    }
                )*
                Ok(())
            }
        }
    };
}
