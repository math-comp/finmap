<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Finite maps

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/finmap/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/finmap/actions/workflows/docker-action.yml




This library is an extension of mathematical component in order to
support finite sets and finite maps on choicetypes (rather that finite
types). This includes support for functions with finite support and
multisets. The library also contains a generic order and set libary,
which will be used to subsume notations for finite sets, eventually.

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Kazuhiko Sakaguchi
- License: [CeCILL-B](CECILL-B)
- Compatible Rocq/Coq versions: 8.20 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 2.2.0 or later
- Rocq/Coq namespace: `mathcomp.finmap`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Finite maps
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-mathcomp-finmap
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/math-comp/finmap.git
cd finmap
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

The documentation is available in the header of the file.

This library will be integrated to the mathematical components
library in the near future.

## Related work

This library was developed independently but inspired from
[Pierre-Yves Strub's
library](https://github.com/strub/ssrmisc/blob/master/fset.v), from
[Christian Doczkal's
library](https://www.ps.uni-saarland.de/formalizations/fset/html/libs.fset.html)
and from Beta Ziliani's work (no reference provided so far).

Another alternative is [Arthur Azevedo de Amorim extensional
structures library](https://github.com/arthuraa/extructures).

## Acknowledgments

Many thanks to Kazuhiko Sakaguchi (for the order library now moved to
the main math-comp repository) and to [various
contributors](https://github.com/math-comp/finmap/graphs/contributors)
