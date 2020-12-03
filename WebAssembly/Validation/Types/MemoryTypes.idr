||| Spec: https://webassembly.github.io/spec/core/valid/types.html#memory-types
module WebAssembly.Validation.Types.MemoryTypes

import WebAssembly.Structure
import WebAssembly.Validation.Types.Limits

public export
MAX_LIMIT_MEMORY : Nat
MAX_LIMIT_MEMORY = power 2 4  -- set to (power 2 16) for original WebAssembly behvaiour WARNING: type-checking then takes like forever

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidMemoryType : MemType -> Type where
  |||
  |||   ⊢ limits : 2^16
  |||----------------------
  |||     ⊢ limits ok
  |||
  MkValidMemoryType : (limits: Limits) -> (limits_valid: ValidLimits limits MAX_LIMIT_MEMORY) -> ValidMemoryType limits

-------------------------------------------------------------------------------
-- Lemmas about memory-type validation
-------------------------------------------------------------------------------

total
invalid_limit_mem : (contra : ValidLimits memType MAX_LIMIT_MEMORY -> Void) -> ValidMemoryType memType -> Void
invalid_limit_mem contra (MkValidMemoryType memType limits_valid) = contra limits_valid

-------------------------------------------------------------------------------
-- Decidability of validation
-------------------------------------------------------------------------------

total
public export
isMemoryTypeValid : (memType : MemType) -> Dec (ValidMemoryType memType)
isMemoryTypeValid memType = case (isLimitsValid memType MAX_LIMIT_MEMORY) of
  No contra => No (invalid_limit_mem contra)
  Yes prof  => Yes (MkValidMemoryType memType prof)
