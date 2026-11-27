//! The attributes published by the Kotlin metadata parser on class, method,
//! and field objects. The session retains their original JVM identities.

use std::{io, sync::Arc};

use arcstr::ArcStr;
use rustc_hash::FxHashMap;

use crate::{
    engine::Cx,
    structs::{
        StructClass, StructField, StructMethod, attr::AnnotationData, consts::ConstantValue,
    },
    types::VarType,
    util::java_str::JavaString,
};

use super::{
    declarations::{KContract, KParameter, KType, KTypeParameter},
    metadata::{self, NameResolver, ParseError, Payload, Warning, proto},
};

mod bind;
mod objects;

pub(crate) use bind::search_for_method;
pub use objects::process_objects;

#[derive(Clone)]
pub enum ClassElement {
    Class(Arc<KClass>),
    File(Arc<KFile>),
    Synthetic(Arc<KFunction>),
    FailedLambda,
    MultifileFacade(Vec<JavaString>),
    FunctionReference,
}

pub struct KClass {
    pub proto: Box<proto::Class>,
    pub names: Option<NameResolver>,
}

pub struct KFile {
    pub proto: Box<proto::Package>,
    pub names: Option<NameResolver>,
    pub multifile_name: Option<JavaString>,
}

#[derive(Clone)]
pub enum MethodElement {
    Function(Arc<KFunction>),
    Constructor(Arc<KConstructor>),
    Property(Arc<KProperty>),
    Hidden(Hidden),
}

#[derive(Clone)]
pub enum FieldElement {
    Property(Arc<KProperty>),
    Hidden(Hidden),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Hidden {
    Generic,
    CompanionInstance,
    CompanionItem,
    ObjectInstance,
    DefaultImpl,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PropertyMethod {
    Getter,
    Setter,
}

pub struct KFunction {
    pub name: ArcStr,
    pub parameters: Vec<KParameter>,
    pub type_parameters: Vec<KTypeParameter>,
    pub return_type: KType,
    pub flags: i32,
    pub context_receiver_types: Vec<KType>,
    pub receiver_type: Option<KType>,
    pub contract: Option<KContract>,
    pub known_override: bool,
    pub defaults: DefaultArguments,
    pub class: Arc<StructClass>,
    pub method: Arc<StructMethod>,
}

pub struct KConstructor {
    pub parameters: Vec<KParameter>,
    pub flags: i32,
    pub defaults: DefaultArguments,
    pub class: Arc<StructClass>,
    pub method: Option<Arc<StructMethod>>,
    pub is_primary: bool,
    pub class_flags: i32,
}

pub enum DefaultArguments {
    Method { name: ArcStr, descriptor: ArcStr },
    Annotation,
}

pub struct KProperty {
    pub name: ArcStr,
    pub ty: Option<KType>,
    pub flags: i32,
    pub getter: Option<KPropertyAccessor>,
    pub setter: Option<KPropertyAccessor>,
    pub setter_param_name: Option<ArcStr>,
    pub underlying_field: Option<Arc<StructField>>,
    pub initializer: Option<PropertyInitializer>,
    pub annotations: Vec<AnnotationData>,
    pub class: Arc<StructClass>,
}

pub struct KPropertyAccessor {
    pub flags: i32,
    pub method: Arc<StructMethod>,
}

pub enum PropertyInitializer {
    Field { key: String, is_static: bool },
    Constant { ty: VarType, value: ConstantValue },
}

#[derive(Default)]
pub struct KotlinMembers {
    classes: ObjectAttributes<StructClass, ClassAttributes>,
    methods: ObjectAttributes<StructMethod, MethodAttributes>,
    fields: ObjectAttributes<StructField, FieldAttributes>,
    deprecated_annotation: Option<AnnotationData>,
}

#[derive(Default)]
struct ClassAttributes {
    element: Option<ClassElement>,
    primary_constructor: Option<Arc<KConstructor>>,
    removed_repeatables: usize,
    companion_fields: Vec<Arc<StructField>>,
    companion_accessors: Vec<Arc<StructMethod>>,
}

#[derive(Default)]
struct MethodAttributes {
    element: Option<MethodElement>,
    property_method: Option<PropertyMethod>,
}

#[derive(Default)]
struct FieldAttributes {
    element: Option<FieldElement>,
}

/// The key follows JVM object identity. Holding the original Arc prevents
/// address reuse, including for lazily loaded library classes.
struct ObjectAttributes<T, A>(FxHashMap<usize, (Arc<T>, A)>);

impl<T, A> Default for ObjectAttributes<T, A> {
    fn default() -> Self {
        Self(FxHashMap::default())
    }
}

impl<T, A: Default> ObjectAttributes<T, A> {
    fn get(&self, object: &T) -> Option<&A> {
        self.0
            .get(&(object as *const T as usize))
            .map(|(_, attrs)| attrs)
    }

    fn get_mut(&mut self, object: &Arc<T>) -> &mut A {
        &mut self
            .0
            .entry(Arc::as_ptr(object) as usize)
            .or_insert_with(|| (Arc::clone(object), A::default()))
            .1
    }
}

impl KotlinMembers {
    pub fn class(&self, class: &StructClass) -> Option<&ClassElement> {
        self.classes.get(class)?.element.as_ref()
    }

    pub fn primary_constructor(&self, class: &StructClass) -> Option<&Arc<KConstructor>> {
        self.classes.get(class)?.primary_constructor.as_ref()
    }

    pub fn method(&self, method: &StructMethod) -> Option<&MethodElement> {
        self.methods.get(method)?.element.as_ref()
    }

    pub fn property_method(&self, method: &StructMethod) -> Option<PropertyMethod> {
        self.methods.get(method)?.property_method
    }

    pub fn field(&self, field: &StructField) -> Option<&FieldElement> {
        self.fields.get(field)?.element.as_ref()
    }

    pub fn fields<'a>(
        &'a self,
        class: &'a StructClass,
    ) -> impl Iterator<Item = &'a Arc<StructField>> + 'a {
        class.fields.iter().chain(
            self.classes
                .get(class)
                .into_iter()
                .flat_map(|attrs| &attrs.companion_fields),
        )
    }

    pub fn methods<'a>(
        &'a self,
        class: &'a StructClass,
    ) -> impl Iterator<Item = &'a Arc<StructMethod>> + 'a {
        class.methods.iter().chain(
            self.classes
                .get(class)
                .into_iter()
                .flat_map(|attrs| &attrs.companion_accessors),
        )
    }

    fn find_field<'a>(
        &'a self,
        class: &'a StructClass,
        name: &str,
        descriptor: &str,
    ) -> Option<&'a Arc<StructField>> {
        self.classes
            .get(class)
            .and_then(|attrs| {
                attrs
                    .companion_fields
                    .iter()
                    .rev()
                    .find(|field| field.name == name && field.descriptor == descriptor)
            })
            .or_else(|| class.get_field(name, descriptor))
    }

    fn find_method<'a>(
        &'a self,
        class: &'a StructClass,
        name: &str,
        descriptor: &str,
    ) -> Option<&'a Arc<StructMethod>> {
        self.classes
            .get(class)
            .and_then(|attrs| {
                attrs
                    .companion_accessors
                    .iter()
                    .rev()
                    .find(|method| method.name == name && method.descriptor == descriptor)
            })
            .or_else(|| class.get_method(name, descriptor))
    }
}

fn state(cx: &mut Cx) -> &mut KotlinMembers {
    cx.kotlin_members.get_or_insert_with(Box::default)
}

/// KotlinWriter removes the first visible Java repeatable marker from the class
/// before writing an annotation definition. Keep the mutation in this session.
pub(crate) fn remove_repeatable(
    cx: &mut Cx,
    class: &Arc<StructClass>,
) -> io::Result<(usize, Option<ArcStr>)> {
    use crate::structs::attr::ElementValue;
    let annotations = class
        .attributes
        .runtime_visible_annotations
        .as_ref()
        .ok_or_else(|| invalid_data("Kotlin annotation class has no visible annotations"))?;
    let attrs = state(cx).classes.get_mut(class);
    let Some(next) = annotations
        .annotations
        .iter()
        .filter(|a| a.class_name == "java/lang/annotation/Repeatable")
        .nth(attrs.removed_repeatables)
    else {
        return Ok((attrs.removed_repeatables, None));
    };
    let Some(ElementValue::Class(container)) = next.par_values.first().map(|value| &value.value)
    else {
        return Err(invalid_data("Repeatable container is not a class literal"));
    };
    attrs.removed_repeatables += 1;
    Ok((attrs.removed_repeatables, Some(container.clone())))
}

/// KotlinChooser.isLanguage binds selected annotations even in export-only
/// mode or when declaration binding fails.
pub fn select_language(cx: &mut Cx, class: &Arc<StructClass>) -> bool {
    if !cx.options.decompile_kotlin {
        return false;
    }
    let Some(selection) =
        metadata::select(class, cx.options.kt_enable, cx.options.kt_export_metadata)
    else {
        return false;
    };
    parse_metadata_for(cx, class);
    selection.decompile
}

/// Called also for library classes on first use by a Kotlin expression.
/// A failed parse may already have published some member attributes.
pub fn parse_metadata_for(cx: &mut Cx, class: &Arc<StructClass>) {
    if cx
        .kotlin_members
        .as_ref()
        .and_then(|members| members.class(class))
        .is_some()
    {
        return;
    }
    let Some(annotation) = metadata::metadata_annotation(class) else {
        return;
    };
    let name = &class.qualified_name;
    let warning = |warning| match warning {
        Warning::MissingStrings => {
            log::warn!("No d2 attribute (strings) in class metadata for class {name}")
        }
        Warning::MissingFacade => log::warn!(
            "No xs attribute (extra string; multifile part name) in class metadata for class {name}"
        ),
        Warning::MissingDataAssumingFunctionReference => log::warn!(
            "No d1 attribute (data) in class metadata for class {name}, assuming function reference"
        ),
    };
    match metadata::read_annotation(class, annotation, warning) {
        Ok(Some(decoded)) => {
            if let Err(error) = bind_metadata(cx, class, decoded, warning) {
                log::warn!("Failed to parse metadata for class {name}: {error}");
            }
        }
        Ok(None) => {}
        Err(ParseError::MissingKind) => log::warn!(
            "No k attribute (type) in class metadata for class {name}, cannot continue Kotlin parsing"
        ),
        Err(ParseError::MissingData) => log::warn!(
            "No d1 attribute (data) in class metadata for class {name}, cannot continue Kotlin parsing"
        ),
        Err(error) => log::warn!("Failed to parse metadata for class {name}: {error}"),
    }
}

fn bind_metadata(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    decoded: metadata::Decoded,
    mut warning: impl FnMut(Warning),
) -> io::Result<()> {
    use metadata::DecodedPayload::{Complete, MultifilePart};
    let names = decoded.names;
    let element = match decoded.payload {
        Complete(Payload::Class(proto)) => {
            if let Some(names) = &names {
                bind::properties(cx, class, &proto.property, names, None)?;
                bind::functions(
                    cx,
                    class,
                    &proto.function,
                    names,
                    proto.type_table.as_ref(),
                    false,
                    None,
                )?;
                bind::constructors(cx, class, &proto, names)?;
            }
            ClassElement::Class(Arc::new(KClass { proto, names }))
        }
        Complete(Payload::File(proto)) => {
            bind_package(cx, class, &proto, names.as_ref())?;
            ClassElement::File(Arc::new(KFile {
                proto,
                names,
                multifile_name: None,
            }))
        }
        MultifilePart { package, facade } => {
            bind_package(cx, class, &package, names.as_ref())?;
            let (facade, was_missing) = facade.map_err(invalid_data)?;
            if was_missing {
                warning(Warning::MissingFacade);
            }
            ClassElement::File(Arc::new(KFile {
                proto: package,
                names,
                multifile_name: Some(facade),
            }))
        }
        Complete(Payload::Synthetic(function)) => {
            if let Some(names) = &names {
                bind::functions(
                    cx,
                    class,
                    std::slice::from_ref(&function),
                    names,
                    function.type_table.as_ref(),
                    true,
                    None,
                )?;
            }
            if state(cx).class(class).is_some() {
                return Ok(());
            }
            ClassElement::FailedLambda
        }
        Complete(Payload::MultifileFacade(parts)) => ClassElement::MultifileFacade(parts),
        Complete(Payload::FunctionReference) => ClassElement::FunctionReference,
        Complete(Payload::MultifilePart { .. }) => {
            unreachable!("multifile metadata is finalized after member binding")
        }
    };
    state(cx).classes.get_mut(class).element = Some(element);
    Ok(())
}

fn bind_package(
    cx: &mut Cx,
    class: &Arc<StructClass>,
    proto: &proto::Package,
    names: Option<&NameResolver>,
) -> io::Result<()> {
    if let Some(names) = names {
        bind::properties(cx, class, &proto.property, names, None)?;
        bind::functions(
            cx,
            class,
            &proto.function,
            names,
            proto.type_table.as_ref(),
            false,
            None,
        )?;
    }
    Ok(())
}

fn invalid_data(error: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, error)
}

/// KInvocationExprent gets the exact JVM method before triggering lazy
/// metadata loading, then takes a snapshot of its two attributes.
pub fn invocation(
    cx: &mut Cx,
    owner: &str,
    name: &str,
    descriptor: &str,
) -> Option<(MethodElement, Option<PropertyMethod>)> {
    let class = cx.classes().get_class(owner)?;
    let method = cx
        .kotlin_members
        .as_ref()
        .and_then(|members| members.find_method(&class, name, descriptor))
        .or_else(|| class.get_method(name, descriptor))?
        .clone();
    parse_metadata_for(cx, &class);
    let members = cx.kotlin_members.as_ref()?;
    Some((
        members.method(&method)?.clone(),
        members.property_method(&method),
    ))
}
