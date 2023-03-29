<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Algebra Tactics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/algebra-tactics/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/algebra-tactics/actions?query=workflow:"Docker%20CI"




This library provides `ring`, `field`, `lra`, `nra`, and `psatz` tactics for
algebraic structures of the Mathematical Components library. The `ring` and
`field` tactics respectively work with any `comRingType` and `fieldType`. The
other (Micromega) tactics work with any `realDomainType` or `realFieldType`.
Their instance resolution is done through canonical structure inference.
Therefore, they work with abstract rings and do not require `Add Ring` and
`Add Field` commands. Another key feature of this library is that they
automatically push down ring morphisms and additive functions to leaves of
ring/field expressions before applying the proof procedures.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
  - Pierre Roux
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 1.15 or later
  - [MathComp](https://math-comp.github.io) algebra
  - [Mczify](https://github.com/math-comp/mczify) 1.1.0 or later
  - [Coq-Elpi](https://github.com/LPCIC/coq-elpi) 1.15.0 or later (known not to work with 1.17.0)
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


## Caveat

The `lra`, `nra`, and `psatz` tactics are considered experimental features and
subject to change.

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
