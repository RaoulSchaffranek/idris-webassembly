module WebAssembly.Validation.Instructions

import WebAssembly.Structure.Values
import WebAssembly.Structure.Instructions
import WebAssembly.Structure.Types
import WebAssembly.Validation.Contexts

-- Some proofs here fall back to "believe_me" to avoid quadratic explosion of cases.

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

public export
data ValidConst : Instr -> FuncType -> Type where
  |||
  ||| ------------------------------
  |||   C ⊢ t.const c : [] -> [t]
  MkValidI32Const : ValidConst (I32Const c) ([] ->> [TI32])
  MkValidI64Const : ValidConst (I64Const c) ([] ->> [TI64])
  MkValidF32Const : ValidConst (F32Const c) ([] ->> [TF32])
  MkValidF64Const : ValidConst (F64Const c) ([] ->> [TF64])

total
public export
inferConstType : (i: Instr) -> Dec (ft ** ValidConst i ft)
inferConstType (I32Const c) = Yes $ ([] ->> [TI32] ** MkValidI32Const)
inferConstType (I64Const c) = Yes $ ([] ->> [TI64] ** MkValidI64Const)
inferConstType (F32Const c) = Yes $ ([] ->> [TF32] ** MkValidF32Const)
inferConstType (F64Const c) = Yes $ ([] ->> [TF64] ** MkValidF64Const)
inferConstType i = No believe_me -- i is not a const-instructions

total
public export
invalid_i32const : ((ft = ([] ->> [TI32])) -> Void) -> ValidConst (I32Const c) ft -> Void
invalid_i32const contra MkValidI32Const = contra Refl

total
public export
invalid_i64const : ((ft = ([] ->> [TI64])) -> Void) -> ValidConst (I64Const c) ft -> Void
invalid_i64const contra MkValidI64Const = contra Refl

total
public export
invalid_f32const : ((ft = ([] ->> [TF32])) -> Void) -> ValidConst (F32Const c) ft -> Void
invalid_f32const contra MkValidF32Const = contra Refl

total
public export
invalid_f64const : ((ft = ([] ->> [TF64])) -> Void) -> ValidConst (F64Const c) ft -> Void
invalid_f64const contra MkValidF64Const = contra Refl

total
public export
checkConstType : (i: Instr) -> (ft : FuncType) -> Dec (ValidConst i ft)
checkConstType (I32Const c) ft = case decEq ft ([] ->> [TI32]) of
  No contra => No (invalid_i32const contra)
  Yes Refl  => Yes MkValidI32Const
checkConstType (I64Const c) ft = case decEq ft ([] ->> [TI64]) of
  No contra => No (invalid_i64const contra)
  Yes Refl  => Yes MkValidI64Const
checkConstType (F32Const c) ft = case decEq ft ([] ->> [TF32]) of
  No contra => No (invalid_f32const contra)
  Yes Refl  => Yes MkValidF32Const
checkConstType (F64Const c) ft = case decEq ft ([] ->> [TF64]) of
  No contra => No (invalid_f64const contra)
  Yes Refl  => Yes MkValidF64Const
checkConstType i ft = No believe_me -- i is not a const-instructions
