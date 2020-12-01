||| Spec: http://webassembly.github.io/spec/core/syntax/types.html#value-types
module WebAssembly.Structure.Types.ValueTypes

import Decidable.Equality

-- Definition

public export
data ValType : Type where
  TI32 : ValType
  TI64 : ValType
  TF32 : ValType
  TF64 : ValType

-- Equality

public export
lemma_ti32_not_ti64 : (TI32 = TI64) -> Void
lemma_ti32_not_ti64 Refl impossible

public export
lemma_ti32_not_tf32 : (TI32 = TF32) -> Void
lemma_ti32_not_tf32 Refl impossible

public export
lemma_ti32_not_tf64 : (TI32 = TF64) -> Void
lemma_ti32_not_tf64 Refl impossible

public export
lemma_ti64_not_ti32 : (TI64 = TI32) -> Void
lemma_ti64_not_ti32 Refl impossible

public export
lemma_ti64_not_tf32 : (TI64 = TF32) -> Void
lemma_ti64_not_tf32 Refl impossible

public export
lemma_ti64_not_tf64 : (TI64 = TF64) -> Void
lemma_ti64_not_tf64 Refl impossible

public export
lemma_tf32_not_ti32 : (TF32 = TI32) -> Void
lemma_tf32_not_ti32 Refl impossible

public export
lemma_tf32_not_ti64 : (TF32 = TI64) -> Void
lemma_tf32_not_ti64 Refl impossible

public export
lemma_tf32_not_tf64 : (TF32 = TF64) -> Void
lemma_tf32_not_tf64 Refl impossible

public export
lemma_tf64_not_ti32 : (TF64 = TI32) -> Void
lemma_tf64_not_ti32 Refl impossible

public export
lemma_tf64_not_ti64 : (TF64 = TI64) -> Void
lemma_tf64_not_ti64 Refl impossible

public export
lemma_tf64_not_tf32 : (TF64 = TF32) -> Void
lemma_tf64_not_tf32 Refl impossible

-- Decidable Equality

public export
implementation DecEq ValType where
  decEq TI32 TI32 = Yes Refl
  decEq TI32 TI64 = No lemma_ti32_not_ti64
  decEq TI32 TF32 = No lemma_ti32_not_tf32
  decEq TI32 TF64 = No lemma_ti32_not_tf64
  decEq TI64 TI32 = No lemma_ti64_not_ti32
  decEq TI64 TI64 = Yes Refl
  decEq TI64 TF32 = No lemma_ti64_not_tf32
  decEq TI64 TF64 = No lemma_ti64_not_tf64
  decEq TF32 TI32 = No lemma_tf32_not_ti32
  decEq TF32 TI64 = No lemma_tf32_not_ti64
  decEq TF32 TF32 = Yes Refl
  decEq TF32 TF64 = No lemma_tf32_not_tf64
  decEq TF64 TI32 = No lemma_tf64_not_ti32
  decEq TF64 TI64 = No lemma_tf64_not_ti64
  decEq TF64 TF32 = No lemma_tf64_not_tf32
  decEq TF64 TF64 = Yes Refl
