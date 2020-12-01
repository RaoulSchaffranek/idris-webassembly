||| Spec: https://webassembly.github.io/spec/core/syntax/values.html#syntax-byte
module WebAssembly.Structure.Values.Bytes

import Data.Fin

import Decidable.Equality

-- Definition

public export
Byte : Type
Byte = Bits8

-- Decidable Equality

public export
implementation DecEq Byte where
  decEq x y = case x == y of -- Blocks if x or y not concrete
    True => Yes primitiveEq 
    False => No primitiveNotEq
  where primitiveEq : x = y
        primitiveEq = really_believe_me (Refl {x})
        primitiveNotEq : x = y -> Void
        primitiveNotEq prf = believe_me {b = Void} ()
