||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#data-segments
module WebAssembly.Structure.Modules.DataSegments

import WebAssembly.Structure.Values
import WebAssembly.Structure.Instructions
import WebAssembly.Structure.Modules.Indices

import Decidable.Equality

-- Definition

public export
record Data where
  constructor MkData
  wdata  : MemIdx
  offset : Expr
  init   : List Byte

-- Equality

public export
lemma_data__data_injective : ((d1 = d2) -> Void) -> (MkData d1 o1 i1 = MkData d2 o2 i2) -> Void
lemma_data__data_injective d1_not_d2 Refl = d1_not_d2 Refl

public export
lemma_data__offset_injective : ((o1 = o2) -> Void) -> (MkData d1 o1 i1 = MkData d2 o2 i2) -> Void
lemma_data__offset_injective o1_not_o2 Refl = o1_not_o2 Refl

public export
lemma_data__init_injective : ((i1 = i2) -> Void) -> (MkData d1 o1 i1 = MkData d2 o2 i2) -> Void
lemma_data__init_injective i1_not_i2 Refl = i1_not_i2 Refl

-- Dedidable Equality

public export
implementation DecEq Data where
  decEq (MkData d1 o1 i1) (MkData d2 o2 i2) = case decEq d1 d2 of
    No d1_not_d2 => No $ lemma_data__data_injective d1_not_d2
    Yes Refl     => case decEq o1 o2 of
      No o1_not_o2 => No $ lemma_data__offset_injective o1_not_o2
      Yes Refl     => case decEq i1 i2 of
        No i1_not_i2 => No $ lemma_data__init_injective i1_not_i2
        Yes Refl     => Yes Refl
