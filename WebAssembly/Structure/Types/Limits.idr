||| Spec: http://webassembly.github.io/spec/core/syntax/types.html#limits
module WebAssembly.Structure.Types.Limits

import WebAssembly.Structure.Values

import Decidable.Equality

-- Definition

public export
data Limits : Type where
  MkLimits : (n: U32) -> (m: Maybe U32) -> Limits

-- Equality

total
public export
lemma_limits__lowerbound_injective : (lb1_not_lb2 : (lb1 = lb2) -> Void) -> (MkLimits lb1 up1 = MkLimits lb2 up2) -> Void
lemma_limits__lowerbound_injective lb1_not_lb2 Refl = lb1_not_lb2 Refl

total
public export
lemma_limits__upperbound_injective : (up1_not_up2 : (up1 = up2) -> Void) -> (MkLimits lb1 up1 = MkLimits lb1 up2) -> Void
lemma_limits__upperbound_injective up1_not_up2 Refl = up1_not_up2 Refl

-- Decidable Equality

public export
implementation DecEq Limits where
  decEq (MkLimits lb1 up1) (MkLimits lb2 up2) = case (decEq lb1 lb2) of
    No lb1_not_lb2 => No (lemma_limits__lowerbound_injective lb1_not_lb2)
    Yes Refl       => case (decEq up1 up2) of
      No up1_not_up2 => No (lemma_limits__upperbound_injective up1_not_up2)
      Yes Refl       => Yes Refl
