||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#functions
module WebAssembly.Structure.Modules.Functions

import WebAssembly.Structure.Types
import WebAssembly.Structure.Instructions
import WebAssembly.Structure.Modules.Indices

import Decidable.Equality

-- Definition

public export
record Func where
  constructor MkFunc
  type   : TypeIdx
  locals : List ValType
  body   : Expr

-- Equality

total
public export
lemma_func__type_injective : ((t1 = t2) -> Void) -> (MkFunc t1 l1 b1 = MkFunc t2 l2 b2) -> Void
lemma_func__type_injective t1_not_t2 Refl = t1_not_t2 Refl

total
public export
lemma_func__locals_injective : ((l1 = l2) -> Void) -> (MkFunc t1 l1 b1 = MkFunc t2 l2 b2) -> Void
lemma_func__locals_injective l1_not_l2 Refl = l1_not_l2 Refl

total
public export
lemma_func__body_injective : ((b1 = b2) -> Void) -> (MkFunc t1 l1 b1 = MkFunc t2 l2 b2) -> Void
lemma_func__body_injective b1_not_b2 Refl = b1_not_b2 Refl

-- Decidable Equality

public export
implementation DecEq Func where
  decEq (MkFunc t1 l1 b1) (MkFunc t2 l2 b2) = case decEq t1 t2 of
    No t1_not_t2 => No $ lemma_func__type_injective t1_not_t2
    Yes Refl     => case decEq l1 l2 of
      No l1_not_l2 => No $ lemma_func__locals_injective l1_not_l2
      Yes Refl     => case decEq b1 b2 of
        No b1_not_b2 => No $ lemma_func__body_injective b1_not_b2
        Yes Refl     => Yes Refl
