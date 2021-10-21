# extrude

`extrude`, an enum extraction library.

The `extrude!()` macro is very similar to the standard `matches!()`
macro, but rather than return whether the match succeeded, it returns
every bound variable in the match as a tuple wrapped in an `Option`.

This is best seen rather than explained:

```rust
enum Ast<'a> {
  Literal(i64),
  Ident(&'a str),
  Op {
    lhs: &'a Ast<'a>,
    rhs: Option<&'a Ast<'a>>,
  },
}

let ast = Ast::Op {
    lhs: &Ast::Literal(5),
    rhs: Some(&Ast::Ident("x")),
};

let (lhs, rhs) = extrude!(ast, Ast::Op {
  lhs,
  rhs: Some(Ast::Ident(id)),
}).unwrap();
assert_eq!(lhs, &Ast::Literal(5));
assert_eq!(rhs, &"x");
```

## Why?

`Option` provides a vast array of helpers for extracting and
transforming the contained item that most `enum`s do not. While it is
possible to use third-party `derive`s to alleviate these, they tend
to be complex and require ownership of the type.

On the other hand, `extrude!()` converts the parts of an enum value
you care about into a option-of-tuple, allowing you to use the
existing vocabulary without needing to write a `match` in the common
case.

## Caveats

Currently this is implemented as a declarative macro, which means it does
not parse the pattern grammar perfectly. In particular, paths with generic
arguments, and single-element path patterns (which rustc disambiguates
using name lookup) are not supported.

Also, tuples are built using basic traits, and cannot support infinitely
large tuples. We support tuples with up to 32 elements.

Extruding a pattern with only one bound value will not produce a
single-element tuple `(T,)`, since this is almost never what you want.
This special case is unlikely to be surprising but is worth calling out.

This macro can't do everything, and that's ok! `match` is a more
appropriate tool most of the time. `let-else` statements will, once
stabilized, replace some of the intended uses of this crates. Prefer
`let-else` in that case.

License: Apache-2.0
