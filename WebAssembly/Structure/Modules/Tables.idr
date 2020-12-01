||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#tables
module WebAssembly.Structure.Modules.Tables

import WebAssembly.Structure.Types

import Decidable.Equality

-- Definition

public export
record Table where
  constructor MkTable
  type : TableType


-- Equality

public export
lemma_table__type_injective : ((t1 = t2) -> Void) -> (MkTable t1 = MkTable t2) -> Void
lemma_table__type_injective t1_not_t2 Refl = t1_not_t2 Refl

-- Decidable Equality

public export
implementation DecEq Table where
  decEq (MkTable t1) (MkTable t2) = case decEq t1 t2 of
    No t1_not_t2 => No $ lemma_table__type_injective t1_not_t2
    Yes Refl     => Yes Refl
