||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#globals
module WebAssembly.Structure.Modules.Globals

import WebAssembly.Structure.Types
import WebAssembly.Structure.Instructions

import Decidable.Equality

-- Definition

public export
record Global where
  constructor MkGlobal
  type : GlobalType
  init : Expr

-- Equality

total
public export
lemma_global__type_injective : ((t1 = t2) -> Void) -> (MkGlobal t1 i1 = MkGlobal t2 i2) -> Void
lemma_global__type_injective t1_not_t2 Refl = t1_not_t2 Refl

total
public export
lemma_global__init_injective : ((i1 = i2) -> Void) -> (MkGlobal t1 i1 = MkGlobal t2 i2) -> Void
lemma_global__init_injective i1_not_i2 Refl = i1_not_i2 Refl

-- Decidable Equality

public export
implementation DecEq Global where
  decEq (MkGlobal t1 i1) (MkGlobal t2 i2) = case decEq t1 t2 of
    No t1_not_t2 => No $ lemma_global__type_injective t1_not_t2
    Yes Refl     => case decEq i1 i2 of
      No i1_not_i2 => No $ lemma_global__init_injective i1_not_i2
      Yes Refl     => Yes Refl
