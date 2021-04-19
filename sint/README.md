# sint

A singleton type for `Nat` represented as `Int`.

This package implements a type `SInt` that links a runtime `Int` with a
type-level `Nat`, along with some arithmetic and reflection capabilities.

This is useful when mixing type-level `Nat`s with GHC array primitives that
expect `Int`s as sizes and indices.

See the module intro of `Data.SInt` for more details.
