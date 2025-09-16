use std::{borrow::Cow, iter};

use crate::{FunctionArgs, FunctionDefinition, LhsValue, Type};
use outer_regex::bytes::Regex;

/// Replaces the first occurrence of a regular expression match in `source` with
/// `replacement`. The replacement string can reference capture groups using
/// `${1}`..`${8}` and escape a literal `$` using `$$`.
#[derive(Debug, Default)]
pub struct RegexReplaceFunction {}

fn build_replacement(
    replacement_str: &str,
    caps: &outer_regex::bytes::Captures<'_>,
    src: &[u8],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(replacement_str.len());
    let bytes = replacement_str.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b'$' {
            if i + 1 < bytes.len() && bytes[i + 1] == b'$' {
                out.push(b'$');
                i += 2;
                continue;
            }
            if i + 2 < bytes.len() && bytes[i + 1] == b'{' {
                if let Some(close_pos) = bytes[i + 2..].iter().position(|&b| b == b'}') {
                    let num_slice = &bytes[i + 2..i + 2 + close_pos];
                    if let Ok(num_str) = std::str::from_utf8(num_slice) {
                        if let Ok(n) = num_str.parse::<usize>() {
                            if n > 0 && n <= 8 {
                                if let Some(m) = caps.get(n) {
                                    let start = m.start();
                                    let end = m.end();
                                    out.extend_from_slice(&src[start..end]);
                                }
                                i += 2 + close_pos + 1;
                                continue;
                            }
                        }
                    }
                    out.push(b'$');
                    i += 1;
                    continue;
                }
            }
            out.push(b'$');
            i += 1;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    out
}

#[inline]
fn regex_replace_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let source_arg = args.next().expect("expected 3 arguments, got 0");
    let pattern_arg = args.next().expect("expected 3 arguments, got 1");
    let replacement_arg = args.next().expect("expected 3 arguments, got 2");

    if args.next().is_some() {
        panic!("expected 3 arguments, got {}", 4 + args.count());
    }

    match (source_arg, pattern_arg, replacement_arg) {
        (
            Ok(LhsValue::Bytes(source)),
            Ok(LhsValue::Bytes(pattern_bytes)),
            Ok(LhsValue::Bytes(replacement_bytes)),
        ) => {
            let pattern_str =
                std::str::from_utf8(pattern_bytes.as_ref()).expect("Pattern must be valid UTF-8");
            let replacement_str = std::str::from_utf8(replacement_bytes.as_ref())
                .expect("Replacement must be valid UTF-8");

            let re = Regex::new(pattern_str).expect("Invalid regex pattern");

            let src = source.as_ref();
            if let Some(caps) = re.captures(src) {
                let m = caps.get(0).unwrap();
                let mut out = Vec::with_capacity(src.len());
                out.extend_from_slice(&src[..m.start()]);
                let repl = build_replacement(replacement_str, &caps, src);
                out.extend_from_slice(&repl);
                out.extend_from_slice(&src[m.end()..]);
                Some(LhsValue::Bytes(Cow::Owned(out)))
            } else {
                Some(LhsValue::Bytes(Cow::Owned(src.to_vec())))
            }
        }
        (Err(Type::Bytes), _, _) => None,
        (_, Err(Type::Bytes), _) => None,
        (_, _, Err(Type::Bytes)) => None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for RegexReplaceFunction {
    fn check_param(
        &self,
        _: &crate::ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        next_param: &super::FunctionParam<'_>,
        _: Option<&mut super::FunctionDefinitionContext>,
    ) -> Result<(), super::FunctionParamError> {
        match params.len() {
            0 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Field)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            1 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            2 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Bytes.into()))?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn return_type(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<&super::FunctionDefinitionContext>,
    ) -> crate::Type {
        Type::Bytes
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (3, Some(0))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(regex_replace_impl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn owned_bytes(s: &str) -> LhsValue<'_> {
        LhsValue::Bytes(Cow::Owned(s.as_bytes().to_vec()))
    }

    #[test]
    fn test_regex_replace_literal() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/foo/bar"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/bar$"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/baz"))),
        ]
        .into_iter();
        assert_eq!(regex_replace_impl(&mut args), Some(owned_bytes("/foo/baz")));
    }

    #[test]
    fn test_regex_replace_no_match() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/x"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"^/y$"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/mumble"))),
        ]
        .into_iter();
        assert_eq!(regex_replace_impl(&mut args), Some(owned_bytes("/x")));
    }

    #[test]
    fn test_regex_replace_case_sensitive() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/foo"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"^/FOO$"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/x"))),
        ]
        .into_iter();
        assert_eq!(regex_replace_impl(&mut args), Some(owned_bytes("/foo")));
    }

    #[test]
    fn test_regex_replace_first_only() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/a/a"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/a"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/b"))),
        ]
        .into_iter();
        assert_eq!(regex_replace_impl(&mut args), Some(owned_bytes("/b/a")));
    }

    #[test]
    fn test_regex_replace_escape_dollar() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/b"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"^/b$"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/b$$"))),
        ]
        .into_iter();
        assert_eq!(regex_replace_impl(&mut args), Some(owned_bytes("/b$")));
    }

    #[test]
    fn test_regex_replace_capture_groups() {
        let mut args = vec![
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/foo/a/path"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"^/foo/([^/]*)/(.*)$"))),
            Ok(LhsValue::Bytes(Cow::Borrowed(b"/bar/${2}/${1}"))),
        ]
        .into_iter();
        assert_eq!(
            regex_replace_impl(&mut args),
            Some(owned_bytes("/bar/path/a"))
        );
    }

    #[test]
    #[should_panic(expected = "expected 3 arguments, got 0")]
    fn test_panic_no_args() {
        let mut args = vec![].into_iter();
        regex_replace_impl(&mut args);
    }
}
