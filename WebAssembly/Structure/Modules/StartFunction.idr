||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#start-function
module WebAssembly.Structure.Modules.StartFunction

import WebAssembly.Structure.Modules.Indices

import Decidable.Equality

-- Definition

public export
record Start where
  constructor MkStart
  func : FuncIdx

-- Equality

public export
lemma_start__func_injective : ((f1 = f2) -> Void) -> (MkStart f1 = MkStart f2) -> Void
lemma_start__func_injective f1_not_f2 Refl = f1_not_f2 Refl

-- Decidable Equality

public export
implementation DecEq Start where
  decEq (MkStart f1) (MkStart f2) = case decEq f1 f2 of
    No f1_not_f2 => No $ lemma_start__func_injective f1_not_f2
    Yes Refl     => Yes Refl
