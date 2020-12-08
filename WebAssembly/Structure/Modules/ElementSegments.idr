||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#element-segments
module WebAssembly.Structure.Modules.ElementSegments

import WebAssembly.Structure.Types
import WebAssembly.Structure.Instructions
import WebAssembly.Structure.Modules.Indices

import Decidable.Equality

-- Definition

public export
record Elem where
  constructor MkElem
  type   : TableIdx
  offset : Expr
  init   : List FuncIdx

-- Equality

total public export
lemma_elem__type_injective : ((t1 = t2) -> Void) -> (MkElem t1 o1 i1 = MkElem t2 o2 i2) -> Void
lemma_elem__type_injective t1_not_t2 Refl = t1_not_t2 Refl

total public export
lemma_elem__offset_injective : ((o1 = o2) -> Void) -> (MkElem t1 o1 i1 = MkElem t2 o2 i2) -> Void
lemma_elem__offset_injective o1_not_o2 Refl = o1_not_o2 Refl

total public export
lemma_elem__init_injective : ((i1 = i2) -> Void) -> (MkElem t1 o1 i1 = MkElem t2 o2 i2) -> Void
lemma_elem__init_injective i1_not_i2 Refl = i1_not_i2 Refl

-- Dedidable Equality

public export
implementation DecEq Elem where
  decEq (MkElem t1 o1 i1) (MkElem t2 o2 i2) = case decEq t1 t2 of
    No t1_not_t2 => No $ lemma_elem__type_injective t1_not_t2
    Yes Refl     => case decEq o1 o2 of
      No o1_not_o2 => No $ lemma_elem__offset_injective o1_not_o2
      Yes Refl     => case decEq i1 i2 of
        No i1_not_i2 => No $ lemma_elem__init_injective i1_not_i2
        Yes Refl     => Yes Refl
