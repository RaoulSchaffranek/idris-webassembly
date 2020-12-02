||| Spec: http://webassembly.github.io/spec/core/syntax/types.html#function-types
module WebAssembly.Structure.Types.FunctionTypes

import WebAssembly.Structure.Types.ValueTypes
import WebAssembly.Structure.Types.ResultTypes

import Decidable.Equality

-- Definition

infixr 6 ->>

public export
data FuncType : Type where
  (->>) : ResultType -> ResultType -> FuncType

-- Equality

total
public export
lemma_functype__inputs_injective : ((in1 = in2) -> Void) -> ((in1 ->> out1) = (in2 ->> out2)) -> Void
lemma_functype__inputs_injective in1_not_in2 Refl = in1_not_in2 Refl

total
public export
lemma_functype__outputs_injective : ((out1 = out2) -> Void) -> ((in1 ->> out1) = (in2 ->> out2)) -> Void
lemma_functype__outputs_injective out1_not_out2 Refl = out1_not_out2 Refl

-- Decidable Equality

public export
implementation DecEq FuncType where
  decEq (in1 ->> out1) (in2 ->> out2) = case (decEq in1 in2) of
    No in1_not_in2 => No $ lemma_functype__inputs_injective in1_not_in2
    Yes Refl  => case (decEq out1 out2) of
      No out1_not_out2 => No $ lemma_functype__outputs_injective out1_not_out2
      Yes Refl         => Yes Refl
