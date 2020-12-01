||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#table-types
module WebAssembly.Structure.Types.TableTypes

import WebAssembly.Structure.Types.Limits

import Decidable.Equality

-- Definition

public export
data ElemType : Type where
  FuncRef : ElemType

public export
TableType : Type
TableType = (Limits, ElemType)

-- Equality

-- Decidable Equality

public export
implementation DecEq ElemType where
  decEq FuncRef FuncRef = Yes Refl
