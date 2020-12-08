module WebAssembly.Structure.Instructions.Memory

import WebAssembly.Structure.Values

import Decidable.Equality

-- Definition
-- Hint: Actual control-instructions are defined in
-- WebAssembly.Structure.Instructions

public export
record MemArg where
  constructor MkMemArg
  offset : U32
  algin  : U32

-- Equality

total public export
lemma_memarg__offset_injective: ((o1 = o2) -> Void) -> (MkMemArg o1 a1 = MkMemArg o2 a2) -> Void
lemma_memarg__offset_injective o1_not_o2 Refl = o1_not_o2 Refl

total public export
lemma_memarg__align_injective: ((a1 = a2) -> Void) -> (MkMemArg o1 a1 = MkMemArg o2 a2) -> Void
lemma_memarg__align_injective a1_not_a2 Refl = a1_not_a2 Refl

-- Decidable Equality

public export
implementation DecEq MemArg where
  decEq (MkMemArg o1 a1) (MkMemArg o2 a2) = case decEq o1 o2 of
    No o1_not_o2 => No $ lemma_memarg__offset_injective o1_not_o2
    Yes Refl     => case decEq a1 a2 of
      No a1_not_a2 => No $ lemma_memarg__align_injective a1_not_a2
      Yes Refl     => Yes Refl

