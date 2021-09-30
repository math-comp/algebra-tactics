<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Algebra Tactics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/algebra-tactics/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/algebra-tactics/actions?query=workflow:"Docker%20CI"




This library provides `ring` and `field` tactics for Mathematical Components,
that work with any `comRingType`s and `fieldType`s, respectively. Their
instance resolution is done through canonical structure inference. Therefore,
they work with abstract rings and do not require `Add Ring` and `Add Field`
commands. Another key feature of this library is that they automatically push
down ring morphisms to leaves of ring and field expressions before
normalization to the Horner form.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.13 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.12.0 or later
  - [Mczify](https://github.com/math-comp/mczify) 1.1.0 or later
  - [Coq-Elpi](https://github.com/LPCIC/coq-elpi) 1.10.1 or later
- Coq namespace: `mathcomp.algebra_tactics`
- Related publication(s): none

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


## Credits
The way we adapt internals of Coq's `ring` and `field` tactics to algebraic
structures of the Mathematical Components library is inspired by the
[elliptic-curves-ssr](https://github.com/strub/elliptic-curves-ssr) library by
Evmorfia-Iro Bartzia and Pierre-Yves Strub.
