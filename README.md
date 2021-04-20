# Fin and Vec

Length-indexed vectors and cardinality-bounded index types.

## Disclaimer

This is not an officially supported Google product.

## Overview

This repository is home to several packages implementing finite sets of ordinal
numbers and length-indexed short vectors, as well as supporting and derived
functionality.

* `sint` implements a singleton type for type-level `Nat` represented by `Int`.

* `fin-int` implements bounded index types represented by `Int`.

* `short-vec` implements length-indexed vectors on top of `SmallArray#`.

* `finite-table` implements `Vec`-based lookup tables over finite enum types.
