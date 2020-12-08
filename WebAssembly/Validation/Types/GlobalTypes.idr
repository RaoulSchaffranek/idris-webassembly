||| Spec: https://webassembly.github.io/spec/core/valid/types.html#global-types
module WebAssembly.Validation.Types.GlobalTypes

import WebAssembly.Structure

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidGlobalType : GlobalType -> Type where
  MkGlobalValidType : (globalType: GlobalType) -> ValidGlobalType globalType

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

total public export
isGlobalTypeValid : (globalType : GlobalType) -> Dec (ValidGlobalType globalType)
isGlobalTypeValid globalType = Yes (MkGlobalValidType globalType)
