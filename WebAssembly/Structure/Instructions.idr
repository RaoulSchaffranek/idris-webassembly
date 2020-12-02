||| Spec: https://webassembly.github.io/spec/core/syntax/instructions.html#numeric-instructions
module WebAssembly.Structure.Instructions

import WebAssembly.Structure.Values
import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices
import public WebAssembly.Structure.Instructions.Control
import public WebAssembly.Structure.Instructions.Memory

import Decidable.Equality

-- Definition

||| Caution!
||| Whenever a constructor is renamed or added to Instr, make sure to add a
||| corresponding case to "instrMaybeEqual". Otherwise the decEq-instance will
||| produce unsound results.
public export
data Instr : Type where
  Unreachable       : Instr
  Nop               : Instr
  Block             : BlockType -> Instr
  Loop              : BlockType -> Instr
  If                : BlockType -> Instr
  Else              : Instr
  End               : Instr
  Br                : LabelIdx -> Instr
  BrIf              : LabelIdx -> Instr
  BrTable           : List LabelIdx -> LabelIdx -> Instr
  Return            : Instr
  Call              : FuncIdx -> Instr
  CallIndirect      : TypeIdx -> Instr
  Drop              : Instr
  Select            : Instr
  LocalGet          : LocalIdx -> Instr
  LocalSet          : LocalIdx -> Instr
  LocalTee          : LocalIdx -> Instr
  GlobalGet         : GlobalIdx -> Instr
  GlobalSet         : GlobalIdx -> Instr
  I32Load           : MemArg -> Instr
  I64Load           : MemArg -> Instr
  F32Load           : MemArg -> Instr
  F64Load           : MemArg -> Instr
  I32Load8S         : MemArg -> Instr
  I32Load8U         : MemArg -> Instr
  I32Load16S        : MemArg -> Instr
  I32Load16U        : MemArg -> Instr
  I64Load8S         : MemArg -> Instr
  I64Load8U         : MemArg -> Instr
  I64Load16S        : MemArg -> Instr
  I64Load16U        : MemArg -> Instr
  I64Load32S        : MemArg -> Instr
  I64Load32U        : MemArg -> Instr
  I32Store          : MemArg -> Instr
  I64Store          : MemArg -> Instr
  F32Store          : MemArg -> Instr
  F64Store          : MemArg -> Instr
  I32Store8         : MemArg -> Instr
  I32Store16        : MemArg -> Instr
  I64Store8         : MemArg -> Instr
  I64Store16        : MemArg -> Instr
  I64Store32        : MemArg -> Instr
  MemorySize        : Instr
  MemoryGrow        : Instr
  I32Const          : I32 -> Instr
  I64Const          : I64 -> Instr
  F32Const          : F32 -> Instr
  F64Const          : F64 -> Instr
  I32Eqz            : Instr
  I32Eq             : Instr
  I32Ne             : Instr
  I32LtS            : Instr
  I32LtU            : Instr
  I32GtS            : Instr
  I32GtU            : Instr
  I32LeS            : Instr
  I32LeU            : Instr
  I32GeS            : Instr
  I32GeU            : Instr
  I64Eqz            : Instr
  I64Eq             : Instr
  I64Ne             : Instr
  I64LtS            : Instr
  I64LtU            : Instr
  I64GtS            : Instr
  I64GtU            : Instr
  I64LeS            : Instr
  I64LeU            : Instr
  I64GeS            : Instr
  I64GeU            : Instr
  F32Eq             : Instr
  F32Ne             : Instr
  F32Lt             : Instr
  F32Gt             : Instr
  F32Le             : Instr
  F32Ge             : Instr
  F64Eq             : Instr
  F64Ne             : Instr
  F64Lt             : Instr
  F64Gt             : Instr
  F64Le             : Instr
  F64Ge             : Instr
  I32Clz            : Instr
  I32Ctz            : Instr
  I32Popcnt         : Instr
  I32Add            : Instr
  I32Sub            : Instr
  I32Mul            : Instr
  I32DivS           : Instr
  I32DivU           : Instr
  I32RemS           : Instr
  I32RemU           : Instr
  I32And            : Instr
  I32Or             : Instr
  I32Xor            : Instr
  I32Shl            : Instr
  I32ShrS           : Instr
  I32ShrU           : Instr
  I32Rotl           : Instr
  I32Rotr           : Instr
  I64Clz            : Instr
  I64Ctz            : Instr
  I64Popcnt         : Instr
  I64Add            : Instr
  I64Sub            : Instr
  I64Mul            : Instr
  I64DivS           : Instr
  I64DivU           : Instr
  I64RemS           : Instr
  I64RemU           : Instr
  I64And            : Instr
  I64Or             : Instr
  I64Xor            : Instr
  I64Shl            : Instr
  I64ShrS           : Instr
  I64ShrU           : Instr
  I64Rotl           : Instr
  I64Rotr           : Instr
  F32Abs            : Instr
  F32Neg            : Instr
  F32Ceil           : Instr
  F32Floor          : Instr
  F32Trunc          : Instr
  F32Nearest        : Instr
  F32Sqrt           : Instr
  F32Add            : Instr
  F32Sub            : Instr
  F32Mul            : Instr
  F32Div            : Instr
  F32Min            : Instr
  F32Max            : Instr
  F32Copysign       : Instr
  F64Abs            : Instr
  F64Neg            : Instr
  F64Ceil           : Instr
  F64Floor          : Instr
  F64Trunc          : Instr
  F64Nearest        : Instr
  F64Sqrt           : Instr
  F64Add            : Instr
  F64Sub            : Instr
  F64Mul            : Instr
  F64Div            : Instr
  F64Min            : Instr
  F64Max            : Instr
  F64Copysign       : Instr
  I32WrapI64        : Instr
  I32TruncF32S      : Instr
  I32TruncF32U      : Instr
  I32TruncF64S      : Instr
  I32TruncF64U      : Instr
  I64ExtendI32S     : Instr
  I64ExtendI32U     : Instr
  I64TruncF32S      : Instr
  I64TruncF32U      : Instr
  I64TruncF64S      : Instr
  I64TruncF64U      : Instr
  F32ConvertI32S    : Instr
  F32ConvertI32U    : Instr
  F32ConvertI64S    : Instr
  F32ConvertI64U    : Instr
  F32DemoteF64      : Instr
  F64ConvertI32S    : Instr
  F64ConvertI32U    : Instr
  F64ConvertI64S    : Instr
  F64ConvertI64U    : Instr
  F64PromoteF32     : Instr
  I32ReinterpretF32 : Instr
  I64ReinterpretF64 : Instr
  F32ReinterpretI32 : Instr
  F64ReinterpretI64 : Instr
  I32Extend8S       : Instr
  I32Extend16S      : Instr
  I64Extend8S       : Instr
  I64Extend16S      : Instr
  I64Extend32S      : Instr
  I32TruncSatF32S   : Instr
  I32TruncSatF32U   : Instr
  I32TruncSatF64S   : Instr
  I32TruncSatF64U   : Instr
  I64TruncSatF32S   : Instr
  I64TruncSatF32U   : Instr
  I64TruncSatF64S   : Instr
  I64TruncSatF64U   : Instr

public export
Expr : Type
Expr = List Instr

-- Decidable Equality

total
public export
instrMaybeEqual : (i1 : Instr) -> (i2 : Instr)     -> Maybe (i1 = i2)
instrMaybeEqual Unreachable       Unreachable       = Just Refl
instrMaybeEqual Nop               Nop               = Just Refl
instrMaybeEqual (Block x)         (Block y)         = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (Loop x)          (Loop y)          = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (If x)            (If y)            = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual Else              Else              = Just Refl
instrMaybeEqual End               End               = Just Refl
instrMaybeEqual (Br x)            (Br y)            = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (BrIf x)          (BrIf y)          = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (BrTable xs x)    (BrTable ys y)    = case decEq xs ys of
  No contra => Nothing
  Yes Refl  => case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
instrMaybeEqual Return            Return            = Just Refl
instrMaybeEqual (Call x)          (Call y)          = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (CallIndirect x)  (CallIndirect y)  = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual Drop              Drop              = Just Refl
instrMaybeEqual Select            Select            = Just Refl
instrMaybeEqual (LocalGet x)      (LocalGet y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (LocalSet x)      (LocalSet y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (LocalTee x)      (LocalTee y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (GlobalGet x)     (GlobalGet y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (GlobalSet x)     (GlobalSet y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Load x)       (I32Load y)       = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load x)       (I64Load y)       = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F32Load x)       (F32Load y)       = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F64Load x)       (F64Load y)       = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Load8S x)     (I32Load8S y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Load8U x)     (I32Load8U y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Load16S x)    (I32Load16S y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Load16U x)    (I32Load16U y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load8S x)     (I64Load8S y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load8U x)     (I64Load8U y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load16S x)    (I64Load16S y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load16U x)    (I64Load16U y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load32S x)    (I64Load32S y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Load32U x)    (I64Load32U y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Store x)      (I32Store y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Store x)      (I64Store y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F32Store x)      (F32Store y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F64Store x)      (F64Store y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Store8 x)     (I32Store8 y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I32Store16 x)    (I32Store16 y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Store8 x)     (I64Store8 y)     = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Store16 x)    (I64Store16 y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Store32 x)    (I64Store32 y)    = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual MemorySize        MemorySize        = Just Refl
instrMaybeEqual MemoryGrow        MemoryGrow        = Just Refl
instrMaybeEqual (I32Const x)      (I32Const y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (I64Const x)      (I64Const y)      = case decEq x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F32Const x)      (F32Const y)      = case decEq @{F32DecEq} x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual (F64Const x)      (F64Const y)      = case decEq @{F64DecEq} x y of
  No contra => Nothing
  Yes Refl  => Just Refl
instrMaybeEqual I32Eqz            I32Eqz            = Just Refl
instrMaybeEqual I32Eq             I32Eq             = Just Refl
instrMaybeEqual I32Ne             I32Ne             = Just Refl
instrMaybeEqual I32LtS            I32LtS            = Just Refl
instrMaybeEqual I32LtU            I32LtU            = Just Refl
instrMaybeEqual I32GtS            I32GtS            = Just Refl
instrMaybeEqual I32GtU            I32GtU            = Just Refl
instrMaybeEqual I32LeS            I32LeS            = Just Refl
instrMaybeEqual I32LeU            I32LeU            = Just Refl
instrMaybeEqual I32GeS            I32GeS            = Just Refl
instrMaybeEqual I32GeU            I32GeU            = Just Refl
instrMaybeEqual I64Eqz            I64Eqz            = Just Refl
instrMaybeEqual I64Eq             I64Eq             = Just Refl
instrMaybeEqual I64Ne             I64Ne             = Just Refl
instrMaybeEqual I64LtS            I64LtS            = Just Refl
instrMaybeEqual I64LtU            I64LtU            = Just Refl
instrMaybeEqual I64GtS            I64GtS            = Just Refl
instrMaybeEqual I64GtU            I64GtU            = Just Refl
instrMaybeEqual I64LeS            I64LeS            = Just Refl
instrMaybeEqual I64LeU            I64LeU            = Just Refl
instrMaybeEqual I64GeS            I64GeS            = Just Refl
instrMaybeEqual I64GeU            I64GeU            = Just Refl
instrMaybeEqual F32Eq             F32Eq             = Just Refl
instrMaybeEqual F32Ne             F32Ne             = Just Refl
instrMaybeEqual F32Lt             F32Lt             = Just Refl
instrMaybeEqual F32Gt             F32Gt             = Just Refl
instrMaybeEqual F32Le             F32Le             = Just Refl
instrMaybeEqual F32Ge             F32Ge             = Just Refl
instrMaybeEqual F64Eq             F64Eq             = Just Refl
instrMaybeEqual F64Ne             F64Ne             = Just Refl
instrMaybeEqual F64Lt             F64Lt             = Just Refl
instrMaybeEqual F64Gt             F64Gt             = Just Refl
instrMaybeEqual F64Le             F64Le             = Just Refl
instrMaybeEqual F64Ge             F64Ge             = Just Refl
instrMaybeEqual I32Clz            I32Clz            = Just Refl
instrMaybeEqual I32Ctz            I32Ctz            = Just Refl
instrMaybeEqual I32Popcnt         I32Popcnt         = Just Refl
instrMaybeEqual I32Add            I32Add            = Just Refl
instrMaybeEqual I32Sub            I32Sub            = Just Refl
instrMaybeEqual I32Mul            I32Mul            = Just Refl
instrMaybeEqual I32DivS           I32DivS           = Just Refl
instrMaybeEqual I32DivU           I32DivU           = Just Refl
instrMaybeEqual I32RemS           I32RemS           = Just Refl
instrMaybeEqual I32RemU           I32RemU           = Just Refl
instrMaybeEqual I32And            I32And            = Just Refl
instrMaybeEqual I32Or             I32Or             = Just Refl
instrMaybeEqual I32Xor            I32Xor            = Just Refl
instrMaybeEqual I32Shl            I32Shl            = Just Refl
instrMaybeEqual I32ShrS           I32ShrS           = Just Refl
instrMaybeEqual I32ShrU           I32ShrU           = Just Refl
instrMaybeEqual I32Rotl           I32Rotl           = Just Refl
instrMaybeEqual I32Rotr           I32Rotr           = Just Refl
instrMaybeEqual I64Clz            I64Clz            = Just Refl
instrMaybeEqual I64Ctz            I64Ctz            = Just Refl
instrMaybeEqual I64Popcnt         I64Popcnt         = Just Refl
instrMaybeEqual I64Add            I64Add            = Just Refl
instrMaybeEqual I64Sub            I64Sub            = Just Refl
instrMaybeEqual I64Mul            I64Mul            = Just Refl
instrMaybeEqual I64DivS           I64DivS           = Just Refl
instrMaybeEqual I64DivU           I64DivU           = Just Refl
instrMaybeEqual I64RemS           I64RemS           = Just Refl
instrMaybeEqual I64RemU           I64RemU           = Just Refl
instrMaybeEqual I64And            I64And            = Just Refl
instrMaybeEqual I64Or             I64Or             = Just Refl
instrMaybeEqual I64Xor            I64Xor            = Just Refl
instrMaybeEqual I64Shl            I64Shl            = Just Refl
instrMaybeEqual I64ShrS           I64ShrS           = Just Refl
instrMaybeEqual I64ShrU           I64ShrU           = Just Refl
instrMaybeEqual I64Rotl           I64Rotl           = Just Refl
instrMaybeEqual I64Rotr           I64Rotr           = Just Refl
instrMaybeEqual F32Abs            F32Abs            = Just Refl
instrMaybeEqual F32Neg            F32Neg            = Just Refl
instrMaybeEqual F32Ceil           F32Ceil           = Just Refl
instrMaybeEqual F32Floor          F32Floor          = Just Refl
instrMaybeEqual F32Trunc          F32Trunc          = Just Refl
instrMaybeEqual F32Nearest        F32Nearest        = Just Refl
instrMaybeEqual F32Sqrt           F32Sqrt           = Just Refl
instrMaybeEqual F32Add            F32Add            = Just Refl
instrMaybeEqual F32Sub            F32Sub            = Just Refl
instrMaybeEqual F32Mul            F32Mul            = Just Refl
instrMaybeEqual F32Div            F32Div            = Just Refl
instrMaybeEqual F32Min            F32Min            = Just Refl
instrMaybeEqual F32Max            F32Max            = Just Refl
instrMaybeEqual F32Copysign       F32Copysign       = Just Refl
instrMaybeEqual F64Abs            F64Abs            = Just Refl
instrMaybeEqual F64Neg            F64Neg            = Just Refl
instrMaybeEqual F64Ceil           F64Ceil           = Just Refl
instrMaybeEqual F64Floor          F64Floor          = Just Refl
instrMaybeEqual F64Trunc          F64Trunc          = Just Refl
instrMaybeEqual F64Nearest        F64Nearest        = Just Refl
instrMaybeEqual F64Sqrt           F64Sqrt           = Just Refl
instrMaybeEqual F64Add            F64Add            = Just Refl
instrMaybeEqual F64Sub            F64Sub            = Just Refl
instrMaybeEqual F64Mul            F64Mul            = Just Refl
instrMaybeEqual F64Div            F64Div            = Just Refl
instrMaybeEqual F64Min            F64Min            = Just Refl
instrMaybeEqual F64Max            F64Max            = Just Refl
instrMaybeEqual F64Copysign       F64Copysign       = Just Refl
instrMaybeEqual I32WrapI64        I32WrapI64        = Just Refl
instrMaybeEqual I32TruncF32S      I32TruncF32S      = Just Refl
instrMaybeEqual I32TruncF32U      I32TruncF32U      = Just Refl
instrMaybeEqual I32TruncF64S      I32TruncF64S      = Just Refl
instrMaybeEqual I32TruncF64U      I32TruncF64U      = Just Refl
instrMaybeEqual I64ExtendI32S     I64ExtendI32S     = Just Refl
instrMaybeEqual I64ExtendI32U     I64ExtendI32U     = Just Refl
instrMaybeEqual I64TruncF32S      I64TruncF32S      = Just Refl
instrMaybeEqual I64TruncF32U      I64TruncF32U      = Just Refl
instrMaybeEqual I64TruncF64S      I64TruncF64S      = Just Refl
instrMaybeEqual I64TruncF64U      I64TruncF64U      = Just Refl
instrMaybeEqual F32ConvertI32S    F32ConvertI32S    = Just Refl
instrMaybeEqual F32ConvertI32U    F32ConvertI32U    = Just Refl
instrMaybeEqual F32ConvertI64S    F32ConvertI64S    = Just Refl
instrMaybeEqual F32ConvertI64U    F32ConvertI64U    = Just Refl
instrMaybeEqual F32DemoteF64      F32DemoteF64      = Just Refl
instrMaybeEqual F64ConvertI32S    F64ConvertI32S    = Just Refl
instrMaybeEqual F64ConvertI32U    F64ConvertI32U    = Just Refl
instrMaybeEqual F64ConvertI64S    F64ConvertI64S    = Just Refl
instrMaybeEqual F64ConvertI64U    F64ConvertI64U    = Just Refl
instrMaybeEqual F64PromoteF32     F64PromoteF32     = Just Refl
instrMaybeEqual I32ReinterpretF32 I32ReinterpretF32 = Just Refl
instrMaybeEqual I64ReinterpretF64 I64ReinterpretF64 = Just Refl
instrMaybeEqual F32ReinterpretI32 F32ReinterpretI32 = Just Refl
instrMaybeEqual F64ReinterpretI64 F64ReinterpretI64 = Just Refl
instrMaybeEqual I32Extend8S       I32Extend8S       = Just Refl
instrMaybeEqual I32Extend16S      I32Extend16S      = Just Refl
instrMaybeEqual I64Extend8S       I64Extend8S       = Just Refl
instrMaybeEqual I64Extend16S      I64Extend16S      = Just Refl
instrMaybeEqual I64Extend32S      I64Extend32S      = Just Refl
instrMaybeEqual I32TruncSatF32S   I32TruncSatF32S   = Just Refl
instrMaybeEqual I32TruncSatF32U   I32TruncSatF32U   = Just Refl
instrMaybeEqual I32TruncSatF64S   I32TruncSatF64S   = Just Refl
instrMaybeEqual I32TruncSatF64U   I32TruncSatF64U   = Just Refl
instrMaybeEqual I64TruncSatF32S   I64TruncSatF32S   = Just Refl
instrMaybeEqual I64TruncSatF32U   I64TruncSatF32U   = Just Refl
instrMaybeEqual I64TruncSatF64S   I64TruncSatF64S   = Just Refl
instrMaybeEqual I64TruncSatF64U   I64TruncSatF64U   = Just Refl
instrMaybeEqual _                 _                 = Nothing

||| Caution!
||| A complete decEq-proof would need O((number of instructions)^2) cases.
||| Apparently, Idris' type-checker is currently overcharged with this
||| amount of  work. The situation for Idris 2 seems to be even worse.
||| Therefore, this decidability-proof falls back to "believe_me" for
||| the negative cases. This reduces the number of cases to check to
||| O(number of instructions).
public export
implementation DecEq Instr where
  decEq i1 i2 = case instrMaybeEqual i1 i2 of
    Just prf => Yes prf
    Nothing  => No $ (\prf => believe_me {b = Void} ())
