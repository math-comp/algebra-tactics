<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Algebra Tactics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/algebra-tactics/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/algebra-tactics/actions/workflows/docker-action.yml




This library provides `ring`, `field`, `lra`, `nra`, and `psatz` tactics for
the Mathematical Components library. These tactics use the algebraic
structures defined in the MathComp library and their canonical instances for
the instance resolution, and do not require any special instance declaration,
like the `Add Ring` and `Add Field` commands. Therefore, each of these tactics
works with any instance of the respective structure, including concrete
instances declared through Hierarchy Builder, abstract instances, and mixed
concrete and abstract instances, e.g., `int * R` where `R` is an abstract
commutative ring. Another key feature of Algebra Tactics is that they
automatically push down ring morphisms and additive functions to leaves of
ring/field expressions before applying the proof procedures.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
  - Pierre Roux
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.20 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 2.4 or later
  - [MathComp](https://math-comp.github.io) algebra
  - [Mczify](https://github.com/math-comp/mczify) 1.5.0 or later
  - [Coq-Elpi](https://github.com/LPCIC/coq-elpi) 2.2.0 or later
- Coq namespace: `mathcomp.algebra_tactics`
- Related publication(s):
  - [Reflexive tactics for algebra, revisited](https://drops.dagstuhl.de/opus/volltexte/2022/16738/) doi:[10.4230/LIPIcs.ITP.2022.29](https://doi.org/10.4230/LIPIcs.ITP.2022.29)

## Building and installation instructions

The easiest way to install the latest released version of Algebra Tactics
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-algebra-tactics
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/algebra-tactics.git
cd algebra-tactics
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



## Documentation

**Caveat: the `lra`, `nra`, and `psatz` tactics are considered experimental
features and subject to change.**

This Coq library provides an adaptation of the
[`ring`, `field`](https://coq.inria.fr/refman/addendum/ring),
[`lra`, `nra`, and `psatz`](https://coq.inria.fr/refman/addendum/micromega)
tactics to the MathComp library.
See the Coq reference manual for the basic functionalities of these tactics.
The descriptions of these tactics below mainly focus on the differences
between ones provided by Coq and ones provided by this library, including the
additional features introduced by this library.

### The `ring` tactic

The `ring` tactic solves a goal of the form `p = q :> R` representing a
polynomial equation. The type `R` must have a canonical `comRingType`
(commutative ring) or at least `comSemiRingType` (commutative semiring)
instance.
The `ring` tactic solves the equation by normalizing each side as a
polynomial, whose coefficients are either integers `Z` (if `R` is a
`comRingType`) or natural numbers `N`.

The `ring` tactic can decide the given polynomial equation modulo given
monomial equations. The syntax to use this feature is `ring: t_1 .. t_n` where
each `t_i` is a proof of equality `m_i = p_i`, `m_i` is a monomial, and `p_i`
is a polynomial.
Although the `ring` tactic supports ring homomorphisms (explained below), all
the monomials and polynomials `m_1, .., m_n, p_1, .., p_n, p, q` must have the
same type `R` for the moment.

Each tactic provided by this library has a preprocessor and supports
applications of (semi)ring homomorphisms and additive functions (N-module or
Z-module homomorphisms).
For example, suppose `f : S -> T` and `g : R -> S` are ring homomorphisms. The
preprocessor turns a ring sub-expression of the form `f (x + g (y * z))` into
`f x + f (g y) * f (g z)`.
A composition of homomorphisms from the initial objects `nat`, `N`, `int`, and
`Z` is automatically normalized to the canonical one. For example, if `R` in
the above example is `int`, the result of the preprocessing should be
`f x + y%:~R * z%:~R` where `f \o g : int -> T` is replaced with `intr`
(`_%:~R`).
Thanks to the preprocessor, the `ring` tactic supports the following
constructs apart from homomorphism applications:
- `GRing.zero` (`0%R`),
- `GRing.add` (`+%R`),
- `addn`,
- `N.add`,
- `Z.add`,
- `GRing.natmul`,
- `GRing.opp` (`-%R`),
- `Z.opp`,
- `Z.sub`,
- `intmul`,
- `GRing.one` (`1%R`),
- `GRing.mul` (`*%R`),
- `muln`,
- `N.mul`,
- `Z.mul`,
- `GRing.exp`,[^constant_exponent]
- `exprz`,[^constant_exponent]
- `expn`,[^constant_exponent]
- `N.pow`,[^constant_exponent]
- `Z.pow`,[^constant_exponent]
- `S`,
- `Posz`,
- `Negz`, and
- constants of type `nat`, `N`, or `Z`.

[^constant_exponent]: The exponent must be a constant value. In addition, it
must be non-negative for `exprz`.

### The `field` tactic

The `field` tactic solves a goal of the form `p = q :> F` representing a
rational equation. The type `F` must have a canonical `fieldType` (field)
instance.
The `field` tactic solves the equation by normalizing each side to a pair of
two polynomials representing a fraction, whose coefficients are integers `Z`.
As is the case for the `ring` tactic, the `field` tactic can decide the given
rational equation modulo given monomial equations. The syntax to use this
feature is the same as the `ring` tactic: `field: t_1 .. t_n`.

The `field` tactic generates proof obligations that all the denominators in
the equation are not zero.
A proof obligation of the form `p * q != 0 :> F` is always automatically
reduced to `p != 0 /\ q != 0`.
If the field `F` is a `numFieldType` (partially ordered field), a proof
obligation of the form `c%:~R != 0 :> F` where `c` is a non-zero integer
constant is automatically resolved.

The `field` tactic has a preprocessor similar to the `ring` tactic.
In addition to the constructs supported by the `ring` tactic, the `field`
tactic supports `GRing.inv` and `exprz` with a negative exponent.

### The `lra`, `nra`, and `psatz` tactics

The `lra` tactic is a decision procedure for linear real arithmetic. The `nra`
and `psatz` tactics are incomplete proof procedures for non-linear real
arithmetic.
The carrier type must have a canonical `realDomainType` (totally ordered
integral domain) or `realFieldType` (totally ordered field) instance.
The multiplicative inverse is supported only if the carrier type is a
`realFieldType`.

If the carrier type is not a `realFieldType` but a `realDomainType`, these
three tactics use the same preprocessor as the `ring` tactic.
If the carrier type is a `realFieldType`, these tactics support `GRing.inv`
and `exprz` with a negative exponent.
In contrast to the `field` tactic, these tactics push down the multiplicative
inverse through multiplication and exponentiation, e.g., turning `(x * y)^-1`
into `x^-1 * y^-1`.

## Files

- `theories/`
  - `common.v`: provides the reflexive preprocessors (syntax, interpretation
    function, and normalization functions),
  - `common.elpi`: provides the reification procedure for (semi)ring and
    module expressions, except for the case that the carrier type is a
    `realFieldType` in the `lra`, `nra`, and `psatz` tactics,
  - `ring.v`: provides the Coq code specific to the `ring` and `field`
    tactics, including the reflection lemmas,
  - `ring.elpi`: provides the Elpi code specific to the `ring` and `field`
    tactics,
  - `ring_tac.elpi`: provides the entry point for the `ring` tactic,
  - `field_tac.elpi`: provides the entry point for the `field` tactic,
  - `lra.v`: provides the Coq code specific to the `lra`, `nra`, and `psatz`
    tactics, including the reflection lemmas,
  - `lra.elpi`: provides the Elpi code specific to the `lra`, `nra`, and
    `psatz` tactics, including the reification procedure and the entry point.

## Credits

- The adaptation of the `lra`, `nra`, and `psatz` tactics is contributed by
  Pierre Roux.
- The way we adapt the internal lemmas of Coq's `ring` and `field` tactics to
  algebraic structures of the Mathematical Components library is inspired by
  the [elliptic-curves-ssr](https://github.com/strub/elliptic-curves-ssr)
  library by Evmorfia-Iro Bartzia and Pierre-Yves Strub.
- The example [`from_sander.v`](examples/from_sander.v) contributed by Assia
  Mahboubi was given to her by [Sander Dahmen](http://www.few.vu.nl/~sdn249/).
  It is related to a computational proof that elliptic curves are endowed with
  a group law.
  As [suggested](https://hal.inria.fr/inria-00129237v4/document) by Laurent
  Théry a while ago, this problem is a good benchmark for proof systems.
  Laurent Théry and Guillaume Hanrot [formally
  verified](https://doi.org/10.1007/978-3-540-74591-4_24) this property in Coq
  in 2007.
