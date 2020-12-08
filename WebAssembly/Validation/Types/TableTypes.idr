||| Spec: https://webassembly.github.io/spec/core/valid/types.html#table-types
module WebAssembly.Validation.Types.TableTypes

import WebAssembly.Structure
import WebAssembly.Validation.Types.Limits

public export
MAX_LIMIT_TABLE : Nat
MAX_LIMIT_TABLE = power 2 4  -- set to (power 2 32) for original WebAssembly behvaiour WARNING: type-checking then takes like forever

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidTableType : TableType -> Type where
  MkValidTableType : (limits : Limits)
                  -> (elementType : ElemType)
                  -> (limits_valid: ValidLimits limits MAX_LIMIT_TABLE)
                  -> ValidTableType (limits, elementType)

-------------------------------------------------------------------------------
-- Lemmas about table-type validation
-------------------------------------------------------------------------------

total invalid_limit : (contra : ValidLimits limits MAX_LIMIT_TABLE -> Void) -> ValidTableType (limits, elemType) -> Void
invalid_limit contra (MkValidTableType limits elemType limits_valid) = contra limits_valid

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

total public export
isTableTypeValid : (tableType : TableType) -> Dec (ValidTableType tableType)
isTableTypeValid (limits, elemType) = case (isLimitsValid limits MAX_LIMIT_TABLE) of
  No contra => No (invalid_limit contra)
  Yes prof  => Yes (MkValidTableType limits elemType prof)
