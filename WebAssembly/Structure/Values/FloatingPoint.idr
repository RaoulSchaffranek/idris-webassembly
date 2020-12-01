||| Spec: https://webassembly.github.io/spec/core/syntax/values.html#floating-point
module WebAssembly.Structure.Values.FloatingPoint

import Decidable.Equality

-- Definition

||| Unsigned Integer 32 Bit
||| Notice: WebAssembly's 32-bit floats are over-approximated by Idris' (64-bit) doubles
public export
F32 : Type
F32 = Double

||| Signed Interer 32 Bit
public export
F64 : Type
F64 = Double

-- Equality

||| Decidable syntactic equality
||| Usage: decEq @{F32DecEq} a b
public export
[F32DecEq] DecEq F32 where
  decEq x y =
    case x == y of -- Blocks if x or y not concrete
      True => Yes primitiveEq 
      False => No primitiveNotEq
    where
      primitiveEq : x = y
      primitiveEq = believe_me (Refl {x})
      primitiveNotEq : x = y -> Void
      primitiveNotEq prf = believe_me {b = Void} ()

||| Decidable syntactic equality
||| Usage: decEq @{F64DecEq} a b
public export
[F64DecEq] DecEq F64 where
  decEq x y =
    case x == y of -- Blocks if x or y not concrete
      True => Yes primitiveEq 
      False => No primitiveNotEq
    where
      primitiveEq : x = y
      primitiveEq = believe_me (Refl {x})
      primitiveNotEq : x = y -> Void
      primitiveNotEq prf = believe_me {b = Void} ()
