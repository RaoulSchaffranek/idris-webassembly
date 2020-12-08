||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#memories
module WebAssembly.Structure.Modules.Memories

import WebAssembly.Structure.Types

import Decidable.Equality

-- Definition

public export
record Mem where
  constructor MkMem
  type : MemType

-- Equality

total public export
lemma_mem__type_injective : ((m1 = m2) -> Void) -> (MkMem m1 = MkMem m2) -> Void
lemma_mem__type_injective m1_not_m2 Refl = m1_not_m2 Refl

-- Decidable Equality

public export
implementation DecEq Mem where
  decEq (MkMem m1) (MkMem m2) = case decEq m1 m2 of
    No m1_not_m2 => No $ lemma_mem__type_injective m1_not_m2
    Yes Refl     => Yes Refl
