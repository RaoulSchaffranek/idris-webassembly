||| Spec: https://webassembly.github.io/spec/core/valid/types.html#function-types
module WebAssembly.Validation.Types.FunctionTypes

import WebAssembly.Structure

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidFunctionType : (funcType : FuncType) -> Type where
  MkValidFunctionType : (funcType : FuncType) -> ValidFunctionType funcType

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

total
public export
isFunctionTypeValid : (funcType : FuncType) -> Dec (ValidFunctionType funcType)
isFunctionTypeValid funcType = Yes (MkValidFunctionType funcType)
