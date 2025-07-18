pub(crate) mod all;
pub(crate) mod any;
pub(crate) mod cidr;
pub(crate) mod concat;
pub(crate) mod len;
pub(crate) mod lower;
pub(crate) mod starts_with;
pub(crate) mod wildcard_replace;

use crate::{
    ParserSettings,
    filter::CompiledValueResult,
    types::{ExpectedType, ExpectedTypeList, GetType, LhsValue, RhsValue, Type, TypeMismatchError},
};
pub use all::AllFunction;
pub use any::AnyFunction;
pub use cidr::CIDRFunction;
pub use concat::ConcatFunction;
pub use len::LenFunction;
pub use lower::LowerFunction;
pub use starts_with::StartsWithFunction;
use std::any::Any;
use std::convert::TryFrom;
use std::fmt::{self, Debug};
use std::iter::once;
use thiserror::Error;
pub use wildcard_replace::WildcardReplaceFunction;

pub(crate) struct ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    chain: std::iter::Chain<A, B>,
    len_a: usize,
    len_b: usize,
}

impl<A, B> ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    #[inline]
    pub(crate) fn new(a: A, b: B) -> ExactSizeChain<A, B> {
        let len_a = a.len();
        let len_b = b.len();
        ExactSizeChain {
            chain: a.chain(b),
            len_a,
            len_b,
        }
    }
}

impl<A, B> Iterator for ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    type Item = A::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.chain.next() {
            None => None,
            Some(elem) => {
                if self.len_a > 0 {
                    self.len_a -= 1;
                } else if self.len_b > 0 {
                    self.len_b -= 1;
                }
                Some(elem)
            }
        }
    }
}

impl<A, B> ExactSizeIterator for ExactSizeChain<A, B>
where
    A: ExactSizeIterator,
    B: ExactSizeIterator<Item = <A as Iterator>::Item>,
{
    #[inline]
    fn len(&self) -> usize {
        self.len_a + self.len_b
    }
}

/// An iterator over function arguments as [`LhsValue`]s.
pub type FunctionArgs<'i, 'a> =
    &'i mut (dyn ExactSizeIterator<Item = CompiledValueResult<'a>> + 'i);

/// Defines what kind of argument a function expects.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum FunctionArgKind {
    /// Allow only literal as argument.
    Literal,
    /// Allow only field as argument.
    Field,
}

/// An error that occurs on a kind mismatch.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("expected argument of kind {expected:?}, but got {actual:?}")]
pub struct FunctionArgKindMismatchError {
    /// Expected value type.
    pub expected: FunctionArgKind,
    /// Provided value type.
    pub actual: FunctionArgKind,
}

/// An error that occurs on a kind mismatch.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("invalid argument: {msg:?}")]
pub struct FunctionArgInvalidConstantError {
    msg: String,
}

impl FunctionArgInvalidConstantError {
    /// Returns a new invalid constant error.
    #[inline]
    pub fn new(msg: String) -> Self {
        Self { msg }
    }
}

impl From<String> for FunctionArgInvalidConstantError {
    #[inline]
    fn from(msg: String) -> Self {
        Self::new(msg)
    }
}

/// An error that occurs for a bad function parameter
#[derive(Debug, PartialEq, Eq, Error)]
pub enum FunctionParamError {
    /// Function paramater value type has a different type than expected
    #[error("expected {0}")]
    TypeMismatch(#[source] TypeMismatchError),
    /// Function parameter argument kind has a different kind than expected
    #[error("expected {0}")]
    KindMismatch(#[source] FunctionArgKindMismatchError),
    /// Function parameter constant value is invalid
    #[error("{0}")]
    InvalidConstant(#[source] FunctionArgInvalidConstantError),
}

impl From<TypeMismatchError> for FunctionParamError {
    #[inline]
    fn from(err: TypeMismatchError) -> Self {
        Self::TypeMismatch(err)
    }
}

impl From<FunctionArgKindMismatchError> for FunctionParamError {
    #[inline]
    fn from(err: FunctionArgKindMismatchError) -> Self {
        Self::KindMismatch(err)
    }
}

impl From<FunctionArgInvalidConstantError> for FunctionParamError {
    #[inline]
    fn from(err: FunctionArgInvalidConstantError) -> Self {
        Self::InvalidConstant(err)
    }
}

/// Function parameter
#[derive(Clone, Debug)]
pub enum FunctionParam<'a> {
    /// Contant function parameter (literal value)
    Constant(&'a RhsValue),
    /// Variable function parameter (field, or complex expressions)
    Variable(Type),
}

impl From<&FunctionParam<'_>> for FunctionArgKind {
    fn from(arg: &FunctionParam<'_>) -> Self {
        match arg {
            FunctionParam::Constant(_) => FunctionArgKind::Literal,
            FunctionParam::Variable(_) => FunctionArgKind::Field,
        }
    }
}

impl GetType for FunctionParam<'_> {
    fn get_type(&self) -> Type {
        match self {
            FunctionParam::Constant(value) => value.get_type(),
            FunctionParam::Variable(ty) => *ty,
        }
    }
}

impl<'a> FunctionParam<'a> {
    /// Returns the underlying value if the current parameter is a constant, otherwise an error.
    pub fn as_constant(&self) -> Result<&'a RhsValue, FunctionArgKindMismatchError> {
        match self {
            Self::Constant(value) => Ok(value),
            Self::Variable(_) => Err(FunctionArgKindMismatchError {
                expected: FunctionArgKind::Literal,
                actual: FunctionArgKind::Field,
            }),
        }
    }

    /// Returns the underlying type if the current parameter is a variable, otherwise an error.
    pub fn as_variable(&self) -> Result<&Type, FunctionArgKindMismatchError> {
        match self {
            Self::Variable(ty) => Ok(ty),
            Self::Constant(_) => Err(FunctionArgKindMismatchError {
                expected: FunctionArgKind::Field,
                actual: FunctionArgKind::Literal,
            }),
        }
    }

    /// Check if the arg_kind of current paramater matches the expected_arg_kind
    pub fn expect_arg_kind(
        &self,
        expected_arg_kind: FunctionArgKind,
    ) -> Result<(), FunctionParamError> {
        let kind = self.into();
        if kind == expected_arg_kind {
            Ok(())
        } else {
            Err(FunctionParamError::KindMismatch(
                FunctionArgKindMismatchError {
                    expected: expected_arg_kind,
                    actual: kind,
                },
            ))
        }
    }

    /// Checks if the val_type of current parameter matches the expected_type
    pub fn expect_val_type(
        &self,
        expected_types: impl Iterator<Item = ExpectedType>,
    ) -> Result<(), FunctionParamError> {
        let ty = self.get_type();
        let mut types = ExpectedTypeList::default();
        for expected_type in expected_types {
            match (&expected_type, &ty) {
                (ExpectedType::Array, Type::Array(_)) => return Ok(()),
                (ExpectedType::Array, _) => {}
                (ExpectedType::Map, Type::Map(_)) => return Ok(()),
                (ExpectedType::Map, _) => {}
                (ExpectedType::Type(val_type), _) => {
                    if ty == *val_type {
                        return Ok(());
                    }
                }
            }
            types.insert(expected_type);
        }
        Err(FunctionParamError::TypeMismatch(TypeMismatchError {
            expected: types,
            actual: ty,
        }))
    }

    /// Checks that the parameter is a constant of a certain type
    /// and call the closure `op` to verify its value
    pub fn expect_const_value<
        U: TryFrom<&'a RhsValue, Error = TypeMismatchError>,
        F: FnOnce(U) -> Result<(), String>,
    >(
        &self,
        op: F,
    ) -> Result<(), FunctionParamError> {
        match self {
            Self::Constant(value) => {
                op(U::try_from(value).map_err(FunctionParamError::TypeMismatch)?).map_err(|msg| {
                    FunctionParamError::InvalidConstant(FunctionArgInvalidConstantError { msg })
                })
            }
            Self::Variable(_) => Err(FunctionParamError::KindMismatch(
                FunctionArgKindMismatchError {
                    expected: FunctionArgKind::Literal,
                    actual: FunctionArgKind::Field,
                },
            )),
        }
    }
}

/// Context that can be created and used
/// when parsing a function call
pub struct FunctionDefinitionContext {
    inner: Box<dyn Any + Send + Sync>,
    clone_cb: fn(&(dyn Any + Send + Sync)) -> Box<dyn Any + Send + Sync>,
    fmt_cb: fn(&(dyn Any + Send + Sync), &mut std::fmt::Formatter<'_>) -> std::fmt::Result,
}

impl FunctionDefinitionContext {
    fn clone_any<T: Any + Clone + Send + Sync>(
        t: &(dyn Any + Send + Sync),
    ) -> Box<dyn Any + Send + Sync> {
        Box::new(t.downcast_ref::<T>().unwrap().clone())
    }

    fn fmt_any<T: Any + Debug + Send + Sync>(
        t: &(dyn Any + Send + Sync),
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        t.downcast_ref::<T>().unwrap().fmt(f)
    }

    /// Creates a new FunctionDefinitionContext object containing user-defined
    /// object of type `T`
    pub fn new<T: Any + Clone + Debug + Send + Sync>(t: T) -> Self {
        Self {
            inner: Box::new(t),
            clone_cb: Self::clone_any::<T>,
            fmt_cb: Self::fmt_any::<T>,
        }
    }

    /// Returns a reference to the underlying Any object
    pub fn as_any_ref(&self) -> &(dyn Any + Send + Sync) {
        &*self.inner
    }

    /// Returns a mutable reference to the underlying Any object
    pub fn as_any_mut(&mut self) -> &mut (dyn Any + Send + Sync) {
        &mut self.inner
    }

    /// Converts current `FunctionDefinitionContext` to `Box<dyn Any>`
    pub fn into_any(self) -> Box<dyn Any + Send + Sync> {
        let Self { inner, .. } = self;
        inner
    }

    /// Attempt to downcast the context to a concrete type.
    pub fn downcast<T: Any + Send + Sync>(self) -> Result<Box<T>, Self> {
        let Self {
            inner,
            clone_cb,
            fmt_cb,
        } = self;
        inner.downcast::<T>().map_err(|inner| Self {
            inner,
            clone_cb,
            fmt_cb,
        })
    }

    /// Returns some reference to the inner value if it is of type T, or None if it isn’t.
    pub fn downcast_ref<T: Any + Send + Sync>(&self) -> Option<&T> {
        self.inner.downcast_ref::<T>()
    }

    /// Returns some mutable reference to the inner value if it is of type T, or None if it isn’t.
    pub fn downcast_mut<T: Any + Send + Sync>(&mut self) -> Option<&mut T> {
        self.inner.downcast_mut::<T>()
    }
}

impl Clone for FunctionDefinitionContext {
    fn clone(&self) -> Self {
        Self {
            inner: (self.clone_cb)(&*self.inner),
            clone_cb: self.clone_cb,
            fmt_cb: self.fmt_cb,
        }
    }
}

impl std::fmt::Debug for FunctionDefinitionContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FunctionDefinitionContext(")?;
        (self.fmt_cb)(&*self.inner, f)?;
        write!(f, ")")?;
        Ok(())
    }
}

/// Trait to implement function
pub trait FunctionDefinition: Debug + Send + Sync {
    /// Custom context to store information during parsing
    fn context(&self) -> Option<FunctionDefinitionContext> {
        None
    }
    /// Given a slice of already checked parameters, checks that next_param is
    /// correct. Return the expected the parameter definition.
    fn check_param(
        &self,
        settings: &ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        next_param: &FunctionParam<'_>,
        ctx: Option<&mut FunctionDefinitionContext>,
    ) -> Result<(), FunctionParamError>;
    /// Function return type.
    fn return_type(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        ctx: Option<&FunctionDefinitionContext>,
    ) -> Type;
    /// Number of mandatory arguments and number of optional arguments
    /// (N, Some(0)) means N mandatory arguments and no optional arguments
    /// (N, None) means N mandatory arguments and unlimited optional arguments
    fn arg_count(&self) -> (usize, Option<usize>);
    /// Compile the function definition down to a closure that is going to be called
    /// during filter execution.
    fn compile(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        ctx: Option<FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>;
}

/* Simple function APIs */

type FunctionPtr = for<'i, 'a> fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>>;

/// Wrapper around a function pointer providing the runtime implementation.
#[derive(Clone, Copy)]
pub struct SimpleFunctionImpl(FunctionPtr);

impl SimpleFunctionImpl {
    /// Creates a new wrapper around a function pointer.
    pub fn new(func: FunctionPtr) -> Self {
        Self(func)
    }
}

impl fmt::Debug for SimpleFunctionImpl {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("SimpleFunctionImpl")
            .field(&(self.0 as *const ()))
            .finish()
    }
}

impl PartialEq for SimpleFunctionImpl {
    fn eq(&self, other: &SimpleFunctionImpl) -> bool {
        std::ptr::eq(self.0 as *const (), other.0 as *const ())
    }
}

impl Eq for SimpleFunctionImpl {}

/// Defines a mandatory function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The type of its associated value.
    pub val_type: Type,
}

/// Defines an optional function argument.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionOptParam {
    /// How the argument can be specified when calling a function.
    pub arg_kind: FunctionArgKind,
    /// The default value if the argument is missing.
    pub default_value: LhsValue<'static>,
}

/// Simple interface to define a function.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleFunctionDefinition {
    /// List of mandatory arguments.
    pub params: Vec<SimpleFunctionParam>,
    /// List of optional arguments that can be specified after manatory ones.
    pub opt_params: Vec<SimpleFunctionOptParam>,
    /// Function return type.
    pub return_type: Type,
    /// Actual implementation that will be called at runtime.
    pub implementation: SimpleFunctionImpl,
}

impl FunctionDefinition for SimpleFunctionDefinition {
    fn check_param(
        &self,
        _settings: &ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        next_param: &FunctionParam<'_>,
        _: Option<&mut FunctionDefinitionContext>,
    ) -> Result<(), FunctionParamError> {
        let index = params.len();
        if index < self.params.len() {
            let param = &self.params[index];
            next_param.expect_arg_kind(param.arg_kind)?;
            next_param.expect_val_type(once(ExpectedType::Type(param.val_type)))?;
        } else if index < self.params.len() + self.opt_params.len() {
            let opt_param = &self.opt_params[index - self.params.len()];
            next_param.expect_arg_kind(opt_param.arg_kind)?;
            next_param
                .expect_val_type(once(ExpectedType::Type(opt_param.default_value.get_type())))?;
        } else {
            unreachable!();
        }
        Ok(())
    }

    fn return_type(
        &self,
        _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<&FunctionDefinitionContext>,
    ) -> Type {
        self.return_type
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (self.params.len(), Some(self.opt_params.len()))
    }

    fn compile(
        &self,
        params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
        _: Option<FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        let params_count = params.len();
        let opt_params = &self.opt_params[(params_count - self.params.len())..];
        let implementation = self.implementation;
        if opt_params.is_empty() {
            Box::new(move |args| {
                assert_eq!(params_count, args.len());
                (implementation.0)(args)
            })
        } else {
            let opt_args: Vec<Result<LhsValue<'static>, Type>> = opt_params
                .iter()
                .map(|opt_param| Ok(opt_param.default_value.clone()))
                .collect();
            Box::new(move |args| {
                assert_eq!(params_count, args.len());
                (implementation.0)(&mut ExactSizeChain::new(args, opt_args.iter().cloned()))
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_definition_context() {
        let mut ctx1 = FunctionDefinitionContext::new(42u8);

        assert_eq!(
            "FunctionDefinitionContext(42)".to_owned(),
            format!("{ctx1:?}")
        );

        assert_eq!(ctx1.downcast_ref::<u8>(), Some(&42u8));

        let ctx2 = ctx1.clone();

        assert_eq!(ctx2.downcast_ref::<u8>(), Some(&42u8));

        *ctx1.downcast_mut::<u8>().unwrap() = 255u8;

        let value = ctx1.downcast::<u8>().unwrap();

        assert_eq!(*value, 255u8);

        assert_eq!(*ctx2.downcast::<u8>().unwrap(), 42u8);

        fn is_send<T: Send>() {}

        is_send::<FunctionDefinitionContext>();

        fn is_sync<T: Sync>() {}

        is_sync::<FunctionDefinitionContext>();
    }
}
