// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `extrude`, an enum extraction library.
//!
//! The [`extrude!()`] macro is very similar to the standard [`matches!()`]
//! macro, but rather than return whether the match succeeded, it returns
//! every bound variable in the match as a tuple wrapped in an [`Option`].
//!
//! This is best seen rather than explained:
//!
//! ```
//! # use extrude::extrude;
//! # #[derive(PartialEq, Eq, Clone, Copy, Debug)]
//! enum Ast<'a> {
//!   Literal(i64),
//!   Ident(&'a str),
//!   Op {
//!     lhs: &'a Ast<'a>,
//!     rhs: Option<&'a Ast<'a>>,
//!   },
//! }
//!
//! let ast = Ast::Op {
//!     lhs: &Ast::Literal(5),
//!     rhs: Some(&Ast::Ident("x")),
//! };
//!
//! let (lhs, rhs) = extrude!(ast, Ast::Op {
//!   lhs,
//!   rhs: Some(Ast::Ident(id)),
//! }).unwrap();
//! assert_eq!(lhs, &Ast::Literal(5));
//! assert_eq!(rhs, &"x");
//! ```
//!
//! # Why?
//!
//! [`Option`] provides a vast array of helpers for extracting and
//! transforming the contained item that most `enum`s do not. While it is
//! possible to use third-party `derive`s to alleviate these, they tend
//! to be complex and require ownership of the type.
//!
//! On the other hand, [`extrude!()`] converts the parts of an enum value
//! you care about into a option-of-tuple, allowing you to use the
//! existing vocabulary without needing to write a `match` in the common
//! case.
//!
//! # Caveats
//!
//! Currently this is implemented as a declarative macro, which means it does
//! not parse the pattern grammar perfectly. In particular, paths with generic
//! arguments, and single-element path patterns (which rustc disambiguates
//! using name lookup) are not supported.
//!
//! Also, tuples are built using basic traits, and cannot support infinitely
//! large tuples. We support tuples with up to 32 elements.
//!
//! Extruding a pattern with only one bound value will not produce a
//! single-element tuple `(T,)`, since this is almost never what you want.
//! This special case is unlikely to be surprising but is worth calling out.
//!
//! This macro can't do everything, and that's ok! `match` is a more
//! appropriate tool most of the time. `let-else` statements will, once
//! stabilized, replace some of the intended uses of this crates. Prefer
//! `let-else` in that case.

#![no_std]
#![deny(warnings, missing_docs, unused)]

#[doc(hidden)]
pub use {None as __None, Some as __Some};

#[doc(hidden)]
pub mod __tuple {
  pub trait Push<T> {
    type Output;
    fn push(self, x: T) -> Self::Output;
  }

  impl<T, U> Push<U> for (T,) {
    type Output = (T, U);
    #[inline(always)]
    fn push(self, x: U) -> (T, U) {
      (self.0, x)
    }
  }

  pub trait SingleFlatten {
    type Output;
    fn flatten(self) -> Self::Output;
  }

  impl<T> SingleFlatten for (T,) {
    type Output = T;
    #[inline(always)]
    fn flatten(self) -> T {
      self.0
    }
  }

  macro_rules! impls {
    ($($($Ts:ident)*;)*) => {$(
      #[allow(non_snake_case)]
      impl<$($Ts,)* T> Push<T> for ($($Ts,)*) {
        type Output = ($($Ts,)* T,);
        #[inline(always)]
        fn push(self, x: T) -> Self::Output {
          let ($($Ts,)*) = self;
          ($($Ts,)* x,)
        }
      }

      #[allow(non_snake_case)]
      impl<$($Ts,)*> SingleFlatten for ($($Ts,)*) {
        type Output = Self;
        #[inline(always)]
        fn flatten(self) -> Self::Output {
          self
        }
      }
    )*}
  }
  impls! {
    ;
    // Implemented explicitly.
    // T0;
    T0 T1;
    T0 T1 T2;
    T0 T1 T2 T3;
    T0 T1 T2 T3 T4;
    T0 T1 T2 T3 T4 T5;
    T0 T1 T2 T3 T4 T5 T6;
    T0 T1 T2 T3 T4 T5 T6 T7;
    T0 T1 T2 T3 T4 T5 T6 T7 T8;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14;
    T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15;
  }
}

/// Helper macro for extracting the identifiers out of a pattern.
///
/// This macro consumes a pattern and tries its hardest to expand into a tuple
/// of identifiers, representing every variable bound by the pattern.
///
/// The heuristic it uses to do so is described below. This is the best
/// possible declarative implementation; we can do better, but it would
/// a proc macro.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl {
  // For a grammar of what we need to consume, see
  // https://doc.rust-lang.org/reference/patterns.html
  //
  // This parser assumes the input is a valid pattern checked by rustc
  // elsewhere.

  // Consume a path, possibly with one component, and recurse into its
  // parentheses-delimited arguments. This cannot be an actual :path
  // variable, since paths cannot be followed by `(`.
  //
  // The path may be empty.
  //
  // This implements GroupedPattern, TuplePattern, and TupleStruct
  // pattern.
  ([$x:tt] $($(::)? $($p:tt)::+)? ($($args:tt)*) $(,$($rest:tt)*)?) => {{
    let $x = $crate::__impl!([$x] $($args)*);
    $crate::__impl!([$x] $($($rest)*)?)
  }};

  // Identical to the above, but with braces.
  //
  // This implements StructPatterns along with the rule below.
  ([$x:tt] $(::)? $($p:tt)::+ {$($args:tt)*} $(,$($rest:tt)*)?) => {{
    let $x = $crate::__impl!([$x] $($args)*);
    $crate::__impl!([$x] $($($rest)*)?)
  }};

  // We can actually just ignore field names with a colon after them;
  // the parser does not need to care about this kind of nesting.
  ([$x:tt] $field:ident: $(,$($rest:tt)*)?) => {
    $crate::__impl!([$x] $($($rest)*)?)
  };

  // Consume bracket-delimited tokens.
  //
  // This implements SlicePattern.
  ([$x:tt] [$($args:tt)*] $(,$($rest:tt)*)?) => {{
    let $x = $crate::__impl!([$x] $($args)*);
    $crate::__impl!([$x] $($($rest)*)?)
  }};

  // Consume an identifier pattern and push it onto the list.
  //
  // Note that this is ambiguous with PathPattern when the
  // pattern has one element. Although in Rust PathPattern dominates,
  // macros cannot do name resolution to distinguish which it is, so
  // identifier patterns dominate.
  //
  // This implements the @-less version of IdentifierPattern.
  ([$x:tt] $id:ident $(,$($rest:tt)*)?) => {{
    let $x = $crate::__tuple::Push::push($x, $id);
    $crate::__impl!([$x] $($($rest)*)?)
  }};

  // Consume a binding pattern and push it onto the list. This is
  // identical to the above; `a @ b`, as a consequence, produces
  // `(a, b)`.
  //
  // This implements the @ version of IdentifierPattern.
  ([$x:tt] $id:ident $(@ $($rest:tt)*)?) => {{
    let $x = $crate::__tuple::Push::push($x, $id);
    $crate::__impl!([$x] $($($rest)*)?)
  }};

  // Consume a path without a trailing brace or brackets.
  //
  // This implements most of PathPattern.
  ([$x:tt] $(::)? $($p:tt)::+ $(,$($rest:tt)*)?) => {
    $crate::__impl!([$x] $($($rest)*)?)
  };

  // Ignore every other token. This includes `ref` and `mut`,
  // commas, &, _, .., ranges, and literals.
  ([$x:tt] $ignored:tt $($rest:tt)*) => {
    $crate::__impl!([$x] $($rest)*)
  };

  // We have consumed the entire input; return the resulting tuple.
  ([$x:tt]) => { $x };
}

/// Extrudes a single variant of an enum into an [`Option<Tuple>`].
///
/// See the [crate documentation][self] for more information.
#[macro_export]
macro_rules! extrude {
  ($e:expr, $($pat:tt)*) => {
    match $e {
      $($pat)* => {
        let __x = ();
        let __x = $crate::__impl!([__x] $($pat)*);
        $crate::__Some($crate::__tuple::SingleFlatten::flatten(__x))
      }
      _ => $crate::__None,
    }
  }
}

#[test]
fn test() {
  #[derive(Copy, Clone)]
  #[allow(unused)]
  enum Foo {
    A,
    B(i32, u32),
    C { a: &'static str, b: &'static Foo },
  }

  let mut f: Foo = Foo::A;
  let _: Option<()> = extrude!(&mut f, Foo::A);
  let _: Option<()> = extrude!(&f, Foo::B(..));
  let _: Option<()> = extrude!(&f, Foo::B(_, _));
  let _: Option<&i32> = extrude!(&f, Foo::B(a, ..));
  let _: Option<&mut u32> = extrude!(&mut f, Foo::B(_, b));
  let _: Option<(&mut i32, &mut u32)> = extrude!(&mut f, Foo::B(a, b));
  let _: Option<&str> = extrude!(f, Foo::C { a, .. });
  let _: Option<(&mut &str, &mut &Foo)> = extrude!(&mut f, Foo::C { a, b });
  let _: Option<&i32> = extrude!(
    f,
    Foo::C {
      a: "foo",
      b: Foo::B(x, _),
    }
  );

  let g: Option<Foo> = None;
  let _: Option<i32> = extrude!(g, Some(Foo::B(a, _)));

  let h: [Option<Foo>; 10] = [None; 10];
  let _: Option<u32> = extrude!(h, [_, Some(Foo::B(_, a)), ..]);
}
