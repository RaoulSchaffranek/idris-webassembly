module WebAssembly.Validation.Instructions

import WebAssembly.Structure.Values
import WebAssembly.Structure.Instructions
import WebAssembly.Structure.Types
import WebAssembly.Validation.Contexts

-- Some proofs here fall back to "believe_me" to avoid quadratic explosion of cases.

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------

||| ------------------------------
|||   C ⊢ t.const c : [] -> [t]
public export
data ValidConst : Instr -> FuncType -> Type where
  MkValidI32Const : ValidConst (I32Const c) ([] ->> [TI32])
  MkValidI64Const : ValidConst (I64Const c) ([] ->> [TI64])
  MkValidF32Const : ValidConst (F32Const c) ([] ->> [TF32])
  MkValidF64Const : ValidConst (F64Const c) ([] ->> [TF64])

total public export
inferConstType : (i: Instr) -> Dec (ft ** ValidConst i ft)
inferConstType (I32Const c) = Yes $ ([] ->> [TI32] ** MkValidI32Const)
inferConstType (I64Const c) = Yes $ ([] ->> [TI64] ** MkValidI64Const)
inferConstType (F32Const c) = Yes $ ([] ->> [TF32] ** MkValidF32Const)
inferConstType (F64Const c) = Yes $ ([] ->> [TF64] ** MkValidF64Const)
inferConstType i = No believe_me -- i is not a const-instructions

total public export
invalid_i32const : ((ft = ([] ->> [TI32])) -> Void) -> ValidConst (I32Const c) ft -> Void
invalid_i32const contra MkValidI32Const = contra Refl

total public export
invalid_i64const : ((ft = ([] ->> [TI64])) -> Void) -> ValidConst (I64Const c) ft -> Void
invalid_i64const contra MkValidI64Const = contra Refl

total public export
invalid_f32const : ((ft = ([] ->> [TF32])) -> Void) -> ValidConst (F32Const c) ft -> Void
invalid_f32const contra MkValidF32Const = contra Refl

total public export
invalid_f64const : ((ft = ([] ->> [TF64])) -> Void) -> ValidConst (F64Const c) ft -> Void
invalid_f64const contra MkValidF64Const = contra Refl

total public export
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

-------------------------------------------------------------------------------
--- Unary Instructions
-------------------------------------------------------------------------------

|||   ----------------------------
|||     C ⊢ t.unop : [t] -> [t]
public export
data ValidUnop : Instr -> FuncType -> Type where
  MkValidI32Clz     : ValidUnop I32Clz     ([TI32] ->> [TI32])
  MkValidI32Ctz     : ValidUnop I32Ctz     ([TI32] ->> [TI32])
  MkValidI32Popcnt  : ValidUnop I32Popcnt  ([TI32] ->> [TI32]) 
  MkValidI64Clz     : ValidUnop I64Clz     ([TI64] ->> [TI64])
  MkValidI64Ctz     : ValidUnop I64Ctz     ([TI64] ->> [TI64])
  MkValidI64Popcnt  : ValidUnop I64Popcnt  ([TI64] ->> [TI64])
  MkValidF32Abs     : ValidUnop F32Abs     ([TF32] ->> [TF32])
  MkValidF32Neg     : ValidUnop F32Neg     ([TF32] ->> [TF32])
  MkValidF32Sqrt    : ValidUnop F32Sqrt    ([TF32] ->> [TF32])
  MkValidF32Ceil    : ValidUnop F32Ceil    ([TF32] ->> [TF32])
  MkValidF32Floor   : ValidUnop F32Floor   ([TF32] ->> [TF32])
  MkValidF32Trunc   : ValidUnop F32Trunc   ([TF32] ->> [TF32])
  MkValidF32Nearest : ValidUnop F32Nearest ([TF32] ->> [TF32])
  MkValidF64Abs     : ValidUnop F64Abs     ([TF64] ->> [TF64])
  MkValidF64Neg     : ValidUnop F64Neg     ([TF64] ->> [TF64])
  MkValidF64Sqrt    : ValidUnop F64Sqrt    ([TF64] ->> [TF64])
  MkValidF64Ceil    : ValidUnop F64Ceil    ([TF64] ->> [TF64])
  MkValidF64Floor   : ValidUnop F64Floor   ([TF64] ->> [TF64])
  MkValidF64Trunc   : ValidUnop F64Trunc   ([TF64] ->> [TF64])
  MkValidF64Nearest : ValidUnop F64Nearest ([TF64] ->> [TF64])

total public export
inferUnopType : (i : Instr) -> Dec (ft : FuncType ** ValidUnop i ft)
inferUnopType I32Clz     = Yes $ ([TI32] ->> [TI32] ** MkValidI32Clz)
inferUnopType I32Ctz     = Yes $ ([TI32] ->> [TI32] ** MkValidI32Ctz)
inferUnopType I32Popcnt  = Yes $ ([TI32] ->> [TI32] ** MkValidI32Popcnt)
inferUnopType I64Clz     = Yes $ ([TI64] ->> [TI64] ** MkValidI64Clz)
inferUnopType I64Ctz     = Yes $ ([TI64] ->> [TI64] ** MkValidI64Ctz)
inferUnopType I64Popcnt  = Yes $ ([TI64] ->> [TI64] ** MkValidI64Popcnt)
inferUnopType F32Abs     = Yes $ ([TF32] ->> [TF32] ** MkValidF32Abs)
inferUnopType F32Neg     = Yes $ ([TF32] ->> [TF32] ** MkValidF32Neg)
inferUnopType F32Sqrt    = Yes $ ([TF32] ->> [TF32] ** MkValidF32Sqrt)
inferUnopType F32Ceil    = Yes $ ([TF32] ->> [TF32] ** MkValidF32Ceil)
inferUnopType F32Floor   = Yes $ ([TF32] ->> [TF32] ** MkValidF32Floor)
inferUnopType F32Trunc   = Yes $ ([TF32] ->> [TF32] ** MkValidF32Trunc)
inferUnopType F32Nearest = Yes $ ([TF32] ->> [TF32] ** MkValidF32Nearest)
inferUnopType F64Abs     = Yes $ ([TF64] ->> [TF64] ** MkValidF64Abs)
inferUnopType F64Neg     = Yes $ ([TF64] ->> [TF64] ** MkValidF64Neg)
inferUnopType F64Sqrt    = Yes $ ([TF64] ->> [TF64] ** MkValidF64Sqrt)
inferUnopType F64Ceil    = Yes $ ([TF64] ->> [TF64] ** MkValidF64Ceil)
inferUnopType F64Floor   = Yes $ ([TF64] ->> [TF64] ** MkValidF64Floor)
inferUnopType F64Trunc   = Yes $ ([TF64] ->> [TF64] ** MkValidF64Trunc)
inferUnopType F64Nearest = Yes $ ([TF64] ->> [TF64] ** MkValidF64Nearest)
inferUnopType _          = No believe_me -- no unary instruction

-- I32 Unary Instructions

total public export
invalid_i32clz : ((ft = [TI32] ->> [TI32]) -> Void) -> (ValidUnop I32Clz ft) -> Void
invalid_i32clz contra MkValidI32Clz = contra Refl

total public export
invalid_i32ctz : ((ft = [TI32] ->> [TI32]) -> Void) -> (ValidUnop I32Ctz ft) -> Void
invalid_i32ctz contra MkValidI32Ctz = contra Refl

total public export
invalid_i32popcnt : ((ft = [TI32] ->> [TI32]) -> Void) -> (ValidUnop I32Popcnt ft) -> Void
invalid_i32popcnt contra MkValidI32Popcnt = contra Refl

-- I64 Unary Instructions

total public export
invalid_i64clz : ((ft = [TI64] ->> [TI64]) -> Void) -> (ValidUnop I64Clz ft) -> Void
invalid_i64clz contra MkValidI64Clz = contra Refl

total public export
invalid_i64ctz : ((ft = [TI64] ->> [TI64]) -> Void) -> (ValidUnop I64Ctz ft) -> Void
invalid_i64ctz contra MkValidI64Ctz = contra Refl

total public export
invalid_i64popcnt : ((ft = [TI64] ->> [TI64]) -> Void) -> (ValidUnop I64Popcnt ft) -> Void
invalid_i64popcnt contra MkValidI64Popcnt = contra Refl

-- F32 Unary Instructions

total public export
invalid_f32abs : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Abs ft) -> Void
invalid_f32abs contra MkValidF32Abs = contra Refl

total public export
invalid_f32neg : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Neg ft) -> Void
invalid_f32neg contra MkValidF32Neg = contra Refl

total public export
invalid_f32sqrt : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Sqrt ft) -> Void
invalid_f32sqrt contra MkValidF32Sqrt = contra Refl

total public export
invalid_f32ceil : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Ceil ft) -> Void
invalid_f32ceil contra MkValidF32Ceil = contra Refl

total public export
invalid_f32floor : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Floor ft) -> Void
invalid_f32floor contra MkValidF32Floor = contra Refl

total public export
invalid_f32trunc : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Trunc ft) -> Void
invalid_f32trunc contra MkValidF32Trunc = contra Refl

total public export
invalid_f32nearest : ((ft = [TF32] ->> [TF32]) -> Void) -> (ValidUnop F32Nearest ft) -> Void
invalid_f32nearest contra MkValidF32Nearest = contra Refl

-- F64 Unary Instructions

total public export
invalid_f64abs : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Abs ft) -> Void
invalid_f64abs contra MkValidF64Abs = contra Refl

total public export
invalid_f64neg : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Neg ft) -> Void
invalid_f64neg contra MkValidF64Neg = contra Refl

total public export
invalid_f64sqrt : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Sqrt ft) -> Void
invalid_f64sqrt contra MkValidF64Sqrt = contra Refl

total public export
invalid_f64ceil : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Ceil ft) -> Void
invalid_f64ceil contra MkValidF64Ceil = contra Refl

total public export
invalid_f64floor : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Floor ft) -> Void
invalid_f64floor contra MkValidF64Floor = contra Refl

total public export
invalid_f64trunc : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Trunc ft) -> Void
invalid_f64trunc contra MkValidF64Trunc = contra Refl

total public export
invalid_f64nearest : ((ft = [TF64] ->> [TF64]) -> Void) -> (ValidUnop F64Nearest ft) -> Void
invalid_f64nearest contra MkValidF64Nearest = contra Refl

total public export
checkUnopType : (i : Instr) -> (ft : FuncType) -> Dec (ValidUnop i ft)
checkUnopType I32Clz     ft = case decEq ft ([TI32] ->> [TI32]) of
  No contra => No $ invalid_i32clz contra
  Yes Refl  => Yes MkValidI32Clz
checkUnopType I32Ctz     ft = case decEq ft ([TI32] ->> [TI32]) of
  No contra => No $ invalid_i32ctz contra
  Yes Refl  => Yes MkValidI32Ctz
checkUnopType I32Popcnt  ft = case decEq ft ([TI32] ->> [TI32]) of
  No contra => No $ invalid_i32popcnt contra
  Yes Refl  => Yes MkValidI32Popcnt
checkUnopType I64Clz     ft = case decEq ft ([TI64] ->> [TI64]) of
  No contra => No $ invalid_i64clz contra
  Yes Refl  => Yes MkValidI64Clz
checkUnopType I64Ctz     ft = case decEq ft ([TI64] ->> [TI64]) of
  No contra => No $ invalid_i64ctz contra
  Yes Refl  => Yes MkValidI64Ctz
checkUnopType I64Popcnt  ft = case decEq ft ([TI64] ->> [TI64]) of
  No contra => No $ invalid_i64popcnt contra
  Yes Refl  => Yes MkValidI64Popcnt
checkUnopType F32Abs     ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32abs contra
  Yes Refl  => Yes MkValidF32Abs
checkUnopType F32Neg     ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32neg contra
  Yes Refl  => Yes MkValidF32Neg
checkUnopType F32Sqrt    ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32sqrt contra
  Yes Refl  => Yes MkValidF32Sqrt
checkUnopType F32Ceil    ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32ceil contra
  Yes Refl  => Yes MkValidF32Ceil
checkUnopType F32Floor   ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32floor contra
  Yes Refl  => Yes MkValidF32Floor
checkUnopType F32Trunc   ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32trunc contra
  Yes Refl  => Yes MkValidF32Trunc
checkUnopType F32Nearest ft = case decEq ft ([TF32] ->> [TF32]) of
  No contra => No $ invalid_f32nearest contra
  Yes Refl  => Yes MkValidF32Nearest
checkUnopType F64Abs     ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64abs contra
  Yes Refl  => Yes MkValidF64Abs
checkUnopType F64Neg     ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64neg contra
  Yes Refl  => Yes MkValidF64Neg
checkUnopType F64Sqrt    ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64sqrt contra
  Yes Refl  => Yes MkValidF64Sqrt
checkUnopType F64Ceil    ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64ceil contra
  Yes Refl  => Yes MkValidF64Ceil
checkUnopType F64Floor   ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64floor contra
  Yes Refl  => Yes MkValidF64Floor
checkUnopType F64Trunc   ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64trunc contra
  Yes Refl  => Yes MkValidF64Trunc
checkUnopType F64Nearest ft = case decEq ft ([TF64] ->> [TF64]) of
  No contra => No $ invalid_f64nearest contra
  Yes Refl  => Yes MkValidF64Nearest
checkUnopType i ft = No believe_me -- no unary instruction
