<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Algebra-tactics

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/algebra-tactics/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/algebra-tactics/actions?query=workflow:"Docker%20CI"




This library provides experimental `ring` and `field` tactics for
`comRingType` and `fieldType` instances of Mathematical Components.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.13 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.12.0 or later
  - [Mczify](https://github.com/math-comp/mczify) 1.0.0 or later
  - [Coq-Elpi](https://github.com/LPCIC/coq-elpi) 1.10.1 or later
- Coq namespace: `mathcomp.algebra_tactics`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Algebra-tactics
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



