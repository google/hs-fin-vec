# Fin and Vec

Length-indexed vectors and cardinality-bounded index types.

[![Stack CI](https://github.com/google/hs-fin-vec/actions/workflows/stack-ci.yml/badge.svg)](https://github.com/google/hs-fin-vec/actions/workflows/stack-ci.yml)

## Disclaimer

This is not an officially supported Google product.

## Hackage Status

* [![sint](https://badgen.net/runkit/awpr/hackage/v/sint?icon=haskell&cache=600)](https://hackage.haskell.org/package/sint)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/sint?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/sint?cache=600)
* [![fin-int](https://badgen.net/runkit/awpr/hackage/v/fin-int?icon=haskell&cache=600)](https://hackage.haskell.org/package/fin-int)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/fin-int?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/fin-int?cache=600)
* [![short-vec](https://badgen.net/runkit/awpr/hackage/v/short-vec?icon=haskell&cache=600)](https://hackage.haskell.org/package/short-vec)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/short-vec?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/short-vec?cache=600)
* [![short-vec-lens](https://badgen.net/runkit/awpr/hackage/v/short-vec-lens?icon=haskell&cache=600)](https://hackage.haskell.org/package/short-vec-lens)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/short-vec-lens?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/short-vec-lens?cache=600)
* [![finite-table](https://badgen.net/runkit/awpr/hackage/v/finite-table?icon=haskell&cache=600)](https://hackage.haskell.org/package/finite-table)
  ![Uploaded](https://badgen.net/runkit/awpr/hackage/t/finite-table?cache=600)
  ![Haddock](https://badgen.net/runkit/awpr/hackage/d/finite-table?cache=600)

## Overview

This repository is home to several packages implementing finite sets of ordinal
numbers and length-indexed short vectors, as well as supporting and derived
functionality.

* `sint` implements a singleton type for type-level `Nat` represented by `Int`.

* `fin-int` implements bounded index types represented by `Int`.

* `short-vec` implements length-indexed vectors on top of `SmallArray#`.

* `finite-table` implements `Vec`-based lookup tables over finite enum types.
