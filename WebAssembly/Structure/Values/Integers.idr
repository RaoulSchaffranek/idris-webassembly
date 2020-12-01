||| Spec: https://webassembly.github.io/spec/core/syntax/values.html#integers
module WebAssembly.Structure.Values.Integers

-- Definition

-- This module only provides a rough over-approximation of WebAssembly's integer-data-types
-- Unsigned and uninterpreted integers are modelled by Idris' (unbounded) natural numbers
-- Signed integers are modelles by Idris' (unbounded) integers

||| Unsigned Integer 32 Bit
public export
U32 : Type
U32 = Nat

||| Signed Interer 32 Bit
public export
S32 : Type
S32 = Integer

||| Uninterpreted Integer 32 Bit
public export
I32 : Type
I32 = Nat

||| Unsigned Integer 32 Bit
public export
U64 : Type
U64 = Nat

||| Signed Interer 32 Bit
public export
S64 : Type
S64 = Integer

||| Uninterpreted Integer 32 Bit
public export
I64 : Type
I64 = Nat

