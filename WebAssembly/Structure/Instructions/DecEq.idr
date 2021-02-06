||| Spec: https://webassembly.github.io/spec/core/syntax/instructions.html#numeric-instructions
module WebAssembly.Structure.Instructions.DecEq

import WebAssembly.Structure.Values
import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices
import WebAssembly.Structure.Instructions.Definition
import WebAssembly.Structure.Instructions.Control
import WebAssembly.Structure.Instructions.Memory

import Decidable.Equality

mutual
  total
  maybeEquals  : (is : List Instr) -> (js : List Instr) -> Maybe (is = js)
  maybeEquals [] [] = Just Refl
  maybeEquals [] (x :: xs) = Nothing
  maybeEquals (x :: xs) [] = Nothing
  maybeEquals (x :: xs) (y :: ys) = case maybeEqual x y of
    Nothing   => Nothing
    Just Refl => case maybeEquals xs ys of
      Nothing   => Nothing
      Just Refl => Just Refl

  total
  maybeEqual : (i1 : Instr) -> (i2 : Instr)     -> Maybe (i1 = i2)
  maybeEqual Unreachable       Unreachable       = Just Refl
  maybeEqual Nop               Nop               = Just Refl
  maybeEqual     (Block x is) (Block y js) with (decEq x y)
    maybeEqual   (Block x is) (Block y js) | No contra = Nothing
    maybeEqual   (Block x is) (Block x js) | Yes Refl with (maybeEquals is js)
      maybeEqual (Block x is) (Block x js) | Yes Refl | Nothing   = Nothing
      maybeEqual (Block x is) (Block x is) | Yes Refl | Just Refl = Just Refl
  maybeEqual (Loop x is)          (Loop y js)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => case maybeEquals is js of
      Nothing   => Nothing
      Just Refl => Just Refl
  maybeEqual (If x is1 js1)    (If y is2 js2)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => case maybeEquals is1 is2 of
      Nothing   => Nothing
      Just Refl => case maybeEquals js1 js2 of
        Nothing   => Nothing
        Just Refl => Just Refl
  maybeEqual Else              Else              = Just Refl
  maybeEqual End               End               = Just Refl
  maybeEqual (Br x)            (Br y)            = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (BrIf x)          (BrIf y)          = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (BrTable xs x)    (BrTable ys y)    = case decEq xs ys of
    No contra => Nothing
    Yes Refl  => case decEq x y of
      No contra => Nothing
      Yes Refl  => Just Refl
  maybeEqual Return            Return            = Just Refl
  maybeEqual (Call x)          (Call y)          = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (CallIndirect x)  (CallIndirect y)  = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual Drop              Drop              = Just Refl
  maybeEqual Select            Select            = Just Refl
  maybeEqual (LocalGet x)      (LocalGet y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (LocalSet x)      (LocalSet y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (LocalTee x)      (LocalTee y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (GlobalGet x)     (GlobalGet y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (GlobalSet x)     (GlobalSet y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Load x)       (I32Load y)       = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load x)       (I64Load y)       = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F32Load x)       (F32Load y)       = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F64Load x)       (F64Load y)       = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Load8S x)     (I32Load8S y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Load8U x)     (I32Load8U y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Load16S x)    (I32Load16S y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Load16U x)    (I32Load16U y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load8S x)     (I64Load8S y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load8U x)     (I64Load8U y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load16S x)    (I64Load16S y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load16U x)    (I64Load16U y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load32S x)    (I64Load32S y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Load32U x)    (I64Load32U y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Store x)      (I32Store y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Store x)      (I64Store y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F32Store x)      (F32Store y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F64Store x)      (F64Store y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Store8 x)     (I32Store8 y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I32Store16 x)    (I32Store16 y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Store8 x)     (I64Store8 y)     = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Store16 x)    (I64Store16 y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (I64Store32 x)    (I64Store32 y)    = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual MemorySize        MemorySize        = Just Refl
  maybeEqual MemoryGrow        MemoryGrow        = Just Refl
  maybeEqual   (I32Const x)    (I32Const y) with (decEq x y)
    maybeEqual (I32Const x)    (I32Const y) | No contra = Nothing
    maybeEqual (I32Const x)    (I32Const x) | Yes Refl  = Just Refl
  maybeEqual (I64Const x)      (I64Const y)      = case decEq x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F32Const x)      (F32Const y)      = case decEq @{F32DecEq} x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual (F64Const x)      (F64Const y)      = case decEq @{F64DecEq} x y of
    No contra => Nothing
    Yes Refl  => Just Refl
  maybeEqual I32Eqz            I32Eqz            = Just Refl
  maybeEqual I32Eq             I32Eq             = Just Refl
  maybeEqual I32Ne             I32Ne             = Just Refl
  maybeEqual I32LtS            I32LtS            = Just Refl
  maybeEqual I32LtU            I32LtU            = Just Refl
  maybeEqual I32GtS            I32GtS            = Just Refl
  maybeEqual I32GtU            I32GtU            = Just Refl
  maybeEqual I32LeS            I32LeS            = Just Refl
  maybeEqual I32LeU            I32LeU            = Just Refl
  maybeEqual I32GeS            I32GeS            = Just Refl
  maybeEqual I32GeU            I32GeU            = Just Refl
  maybeEqual I64Eqz            I64Eqz            = Just Refl
  maybeEqual I64Eq             I64Eq             = Just Refl
  maybeEqual I64Ne             I64Ne             = Just Refl
  maybeEqual I64LtS            I64LtS            = Just Refl
  maybeEqual I64LtU            I64LtU            = Just Refl
  maybeEqual I64GtS            I64GtS            = Just Refl
  maybeEqual I64GtU            I64GtU            = Just Refl
  maybeEqual I64LeS            I64LeS            = Just Refl
  maybeEqual I64LeU            I64LeU            = Just Refl
  maybeEqual I64GeS            I64GeS            = Just Refl
  maybeEqual I64GeU            I64GeU            = Just Refl
  maybeEqual F32Eq             F32Eq             = Just Refl
  maybeEqual F32Ne             F32Ne             = Just Refl
  maybeEqual F32Lt             F32Lt             = Just Refl
  maybeEqual F32Gt             F32Gt             = Just Refl
  maybeEqual F32Le             F32Le             = Just Refl
  maybeEqual F32Ge             F32Ge             = Just Refl
  maybeEqual F64Eq             F64Eq             = Just Refl
  maybeEqual F64Ne             F64Ne             = Just Refl
  maybeEqual F64Lt             F64Lt             = Just Refl
  maybeEqual F64Gt             F64Gt             = Just Refl
  maybeEqual F64Le             F64Le             = Just Refl
  maybeEqual F64Ge             F64Ge             = Just Refl
  maybeEqual I32Clz            I32Clz            = Just Refl
  maybeEqual I32Ctz            I32Ctz            = Just Refl
  maybeEqual I32Popcnt         I32Popcnt         = Just Refl
  maybeEqual I32Add            I32Add            = Just Refl
  maybeEqual I32Sub            I32Sub            = Just Refl
  maybeEqual I32Mul            I32Mul            = Just Refl
  maybeEqual I32DivS           I32DivS           = Just Refl
  maybeEqual I32DivU           I32DivU           = Just Refl
  maybeEqual I32RemS           I32RemS           = Just Refl
  maybeEqual I32RemU           I32RemU           = Just Refl
  maybeEqual I32And            I32And            = Just Refl
  maybeEqual I32Or             I32Or             = Just Refl
  maybeEqual I32Xor            I32Xor            = Just Refl
  maybeEqual I32Shl            I32Shl            = Just Refl
  maybeEqual I32ShrS           I32ShrS           = Just Refl
  maybeEqual I32ShrU           I32ShrU           = Just Refl
  maybeEqual I32Rotl           I32Rotl           = Just Refl
  maybeEqual I32Rotr           I32Rotr           = Just Refl
  maybeEqual I64Clz            I64Clz            = Just Refl
  maybeEqual I64Ctz            I64Ctz            = Just Refl
  maybeEqual I64Popcnt         I64Popcnt         = Just Refl
  maybeEqual I64Add            I64Add            = Just Refl
  maybeEqual I64Sub            I64Sub            = Just Refl
  maybeEqual I64Mul            I64Mul            = Just Refl
  maybeEqual I64DivS           I64DivS           = Just Refl
  maybeEqual I64DivU           I64DivU           = Just Refl
  maybeEqual I64RemS           I64RemS           = Just Refl
  maybeEqual I64RemU           I64RemU           = Just Refl
  maybeEqual I64And            I64And            = Just Refl
  maybeEqual I64Or             I64Or             = Just Refl
  maybeEqual I64Xor            I64Xor            = Just Refl
  maybeEqual I64Shl            I64Shl            = Just Refl
  maybeEqual I64ShrS           I64ShrS           = Just Refl
  maybeEqual I64ShrU           I64ShrU           = Just Refl
  maybeEqual I64Rotl           I64Rotl           = Just Refl
  maybeEqual I64Rotr           I64Rotr           = Just Refl
  maybeEqual F32Abs            F32Abs            = Just Refl
  maybeEqual F32Neg            F32Neg            = Just Refl
  maybeEqual F32Ceil           F32Ceil           = Just Refl
  maybeEqual F32Floor          F32Floor          = Just Refl
  maybeEqual F32Trunc          F32Trunc          = Just Refl
  maybeEqual F32Nearest        F32Nearest        = Just Refl
  maybeEqual F32Sqrt           F32Sqrt           = Just Refl
  maybeEqual F32Add            F32Add            = Just Refl
  maybeEqual F32Sub            F32Sub            = Just Refl
  maybeEqual F32Mul            F32Mul            = Just Refl
  maybeEqual F32Div            F32Div            = Just Refl
  maybeEqual F32Min            F32Min            = Just Refl
  maybeEqual F32Max            F32Max            = Just Refl
  maybeEqual F32Copysign       F32Copysign       = Just Refl
  maybeEqual F64Abs            F64Abs            = Just Refl
  maybeEqual F64Neg            F64Neg            = Just Refl
  maybeEqual F64Ceil           F64Ceil           = Just Refl
  maybeEqual F64Floor          F64Floor          = Just Refl
  maybeEqual F64Trunc          F64Trunc          = Just Refl
  maybeEqual F64Nearest        F64Nearest        = Just Refl
  maybeEqual F64Sqrt           F64Sqrt           = Just Refl
  maybeEqual F64Add            F64Add            = Just Refl
  maybeEqual F64Sub            F64Sub            = Just Refl
  maybeEqual F64Mul            F64Mul            = Just Refl
  maybeEqual F64Div            F64Div            = Just Refl
  maybeEqual F64Min            F64Min            = Just Refl
  maybeEqual F64Max            F64Max            = Just Refl
  maybeEqual F64Copysign       F64Copysign       = Just Refl
  maybeEqual I32WrapI64        I32WrapI64        = Just Refl
  maybeEqual I32TruncF32S      I32TruncF32S      = Just Refl
  maybeEqual I32TruncF32U      I32TruncF32U      = Just Refl
  maybeEqual I32TruncF64S      I32TruncF64S      = Just Refl
  maybeEqual I32TruncF64U      I32TruncF64U      = Just Refl
  maybeEqual I64ExtendI32S     I64ExtendI32S     = Just Refl
  maybeEqual I64ExtendI32U     I64ExtendI32U     = Just Refl
  maybeEqual I64TruncF32S      I64TruncF32S      = Just Refl
  maybeEqual I64TruncF32U      I64TruncF32U      = Just Refl
  maybeEqual I64TruncF64S      I64TruncF64S      = Just Refl
  maybeEqual I64TruncF64U      I64TruncF64U      = Just Refl
  maybeEqual F32ConvertI32S    F32ConvertI32S    = Just Refl
  maybeEqual F32ConvertI32U    F32ConvertI32U    = Just Refl
  maybeEqual F32ConvertI64S    F32ConvertI64S    = Just Refl
  maybeEqual F32ConvertI64U    F32ConvertI64U    = Just Refl
  maybeEqual F32DemoteF64      F32DemoteF64      = Just Refl
  maybeEqual F64ConvertI32S    F64ConvertI32S    = Just Refl
  maybeEqual F64ConvertI32U    F64ConvertI32U    = Just Refl
  maybeEqual F64ConvertI64S    F64ConvertI64S    = Just Refl
  maybeEqual F64ConvertI64U    F64ConvertI64U    = Just Refl
  maybeEqual F64PromoteF32     F64PromoteF32     = Just Refl
  maybeEqual I32ReinterpretF32 I32ReinterpretF32 = Just Refl
  maybeEqual I64ReinterpretF64 I64ReinterpretF64 = Just Refl
  maybeEqual F32ReinterpretI32 F32ReinterpretI32 = Just Refl
  maybeEqual F64ReinterpretI64 F64ReinterpretI64 = Just Refl
  maybeEqual I32Extend8S       I32Extend8S       = Just Refl
  maybeEqual I32Extend16S      I32Extend16S      = Just Refl
  maybeEqual I64Extend8S       I64Extend8S       = Just Refl
  maybeEqual I64Extend16S      I64Extend16S      = Just Refl
  maybeEqual I64Extend32S      I64Extend32S      = Just Refl
  maybeEqual I32TruncSatF32S   I32TruncSatF32S   = Just Refl
  maybeEqual I32TruncSatF32U   I32TruncSatF32U   = Just Refl
  maybeEqual I32TruncSatF64S   I32TruncSatF64S   = Just Refl
  maybeEqual I32TruncSatF64U   I32TruncSatF64U   = Just Refl
  maybeEqual I64TruncSatF32S   I64TruncSatF32S   = Just Refl
  maybeEqual I64TruncSatF32U   I64TruncSatF32U   = Just Refl
  maybeEqual I64TruncSatF64S   I64TruncSatF64S   = Just Refl
  maybeEqual I64TruncSatF64U   I64TruncSatF64U   = Just Refl
  maybeEqual _                 _                 = Nothing

mutual
  total
  maybeNotEquals : (xs : List Instr) -> (Nothing = maybeEquals xs xs) -> Void
  maybeNotEquals [] Refl impossible
  maybeNotEquals (x :: xs) prf with (maybeEqual x x) proof h1
    | Just Refl with (maybeEquals xs xs) proof h2
      | Just Refl = absurd prf
      | Nothing = maybeNotEquals xs h2
    | Nothing = maybeNotEqual x h1

  maybeNotEqual : (a : Instr) -> (Nothing = maybeEqual a a) -> Void
  maybeNotEqual Unreachable Refl impossible
  maybeNotEqual Nop Refl impossible
  maybeNotEqual (Block x xs) prf with (decEq x x)
    | Yes Refl  with (maybeEquals xs xs) proof p
      | Just Refl = absurd prf
      | Nothing   = maybeNotEquals xs p
    | No contra = contra Refl
  maybeNotEqual (Loop x xs) prf with (decEq x x)
    | Yes Refl  with (maybeEquals xs xs) proof p
      | Just Refl = absurd prf
      | Nothing   = maybeNotEquals xs p
    | No contra = contra Refl
  maybeNotEqual (If x xs ys) prf with (decEq x x)
    | Yes Refl  with (maybeEquals xs xs) proof p1
      | Just Refl with (maybeEquals ys ys) proof p2
        | Just Refl = absurd prf
        | Nothing = maybeNotEquals ys p2
      | Nothing   = maybeNotEquals xs p1
    | No contra = contra Refl
  maybeNotEqual Else Refl impossible
  maybeNotEqual End Refl impossible
  maybeNotEqual (Br k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (BrIf k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (BrTable xs x) prf with (decEq xs xs)
    | Yes Refl   with (decEq x x)
      | Yes Refl  = absurd prf
      | No contra = contra Refl
    | No  contra = contra Refl
  maybeNotEqual Return Refl impossible
  maybeNotEqual (Call k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (CallIndirect k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual Drop Refl impossible
  maybeNotEqual Select Refl impossible
  maybeNotEqual (LocalGet k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (LocalSet k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (LocalTee k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (GlobalGet k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (GlobalSet k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Load x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F32Load x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F64Load x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Load8S x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Load8U x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Load16S x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Load16U x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load8S x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load8U x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load16S x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load16U x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load32S x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Load32U x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Store x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Store x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F32Store x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F64Store x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Store8 x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I32Store16 x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Store8 x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Store16 x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Store32 x) prf with (decEq x x)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual MemorySize Refl impossible
  maybeNotEqual MemoryGrow Refl impossible
  maybeNotEqual (I32Const k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (I64Const k) prf with (decEq k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F32Const k) prf with (decEq @{F32DecEq} k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual (F64Const k) prf with (decEq @{F64DecEq} k k)
    | Yes Refl   = absurd prf
    | No  contra = contra Refl
  maybeNotEqual I32Eqz Refl impossible
  maybeNotEqual I32Eq Refl impossible
  maybeNotEqual I32Ne Refl impossible
  maybeNotEqual I32LtS Refl impossible
  maybeNotEqual I32LtU Refl impossible
  maybeNotEqual I32GtS Refl impossible
  maybeNotEqual I32GtU Refl impossible
  maybeNotEqual I32LeS Refl impossible
  maybeNotEqual I32LeU Refl impossible
  maybeNotEqual I32GeS Refl impossible
  maybeNotEqual I32GeU Refl impossible
  maybeNotEqual I64Eqz Refl impossible
  maybeNotEqual I64Eq Refl impossible
  maybeNotEqual I64Ne Refl impossible
  maybeNotEqual I64LtS Refl impossible
  maybeNotEqual I64LtU Refl impossible
  maybeNotEqual I64GtS Refl impossible
  maybeNotEqual I64GtU Refl impossible
  maybeNotEqual I64LeS Refl impossible
  maybeNotEqual I64LeU Refl impossible
  maybeNotEqual I64GeS Refl impossible
  maybeNotEqual I64GeU Refl impossible
  maybeNotEqual F32Eq Refl impossible
  maybeNotEqual F32Ne Refl impossible
  maybeNotEqual F32Lt Refl impossible
  maybeNotEqual F32Gt Refl impossible
  maybeNotEqual F32Le Refl impossible
  maybeNotEqual F32Ge Refl impossible
  maybeNotEqual F64Eq Refl impossible
  maybeNotEqual F64Ne Refl impossible
  maybeNotEqual F64Lt Refl impossible
  maybeNotEqual F64Gt Refl impossible
  maybeNotEqual F64Le Refl impossible
  maybeNotEqual F64Ge Refl impossible
  maybeNotEqual I32Clz Refl impossible
  maybeNotEqual I32Ctz Refl impossible
  maybeNotEqual I32Popcnt Refl impossible
  maybeNotEqual I32Add Refl impossible
  maybeNotEqual I32Sub Refl impossible
  maybeNotEqual I32Mul Refl impossible
  maybeNotEqual I32DivS Refl impossible
  maybeNotEqual I32DivU Refl impossible
  maybeNotEqual I32RemS Refl impossible
  maybeNotEqual I32RemU Refl impossible
  maybeNotEqual I32And Refl impossible
  maybeNotEqual I32Or Refl impossible
  maybeNotEqual I32Xor Refl impossible
  maybeNotEqual I32Shl Refl impossible
  maybeNotEqual I32ShrS Refl impossible
  maybeNotEqual I32ShrU Refl impossible
  maybeNotEqual I32Rotl Refl impossible
  maybeNotEqual I32Rotr Refl impossible
  maybeNotEqual I64Clz Refl impossible
  maybeNotEqual I64Ctz Refl impossible
  maybeNotEqual I64Popcnt Refl impossible
  maybeNotEqual I64Add Refl impossible
  maybeNotEqual I64Sub Refl impossible
  maybeNotEqual I64Mul Refl impossible
  maybeNotEqual I64DivS Refl impossible
  maybeNotEqual I64DivU Refl impossible
  maybeNotEqual I64RemS Refl impossible
  maybeNotEqual I64RemU Refl impossible
  maybeNotEqual I64And Refl impossible
  maybeNotEqual I64Or Refl impossible
  maybeNotEqual I64Xor Refl impossible
  maybeNotEqual I64Shl Refl impossible
  maybeNotEqual I64ShrS Refl impossible
  maybeNotEqual I64ShrU Refl impossible
  maybeNotEqual I64Rotl Refl impossible
  maybeNotEqual I64Rotr Refl impossible
  maybeNotEqual F32Abs Refl impossible
  maybeNotEqual F32Neg Refl impossible
  maybeNotEqual F32Ceil Refl impossible
  maybeNotEqual F32Floor Refl impossible
  maybeNotEqual F32Trunc Refl impossible
  maybeNotEqual F32Nearest Refl impossible
  maybeNotEqual F32Sqrt Refl impossible
  maybeNotEqual F32Add Refl impossible
  maybeNotEqual F32Sub Refl impossible
  maybeNotEqual F32Mul Refl impossible
  maybeNotEqual F32Div Refl impossible
  maybeNotEqual F32Min Refl impossible
  maybeNotEqual F32Max Refl impossible
  maybeNotEqual F32Copysign Refl impossible
  maybeNotEqual F64Abs Refl impossible
  maybeNotEqual F64Neg Refl impossible
  maybeNotEqual F64Ceil Refl impossible
  maybeNotEqual F64Floor Refl impossible
  maybeNotEqual F64Trunc Refl impossible
  maybeNotEqual F64Nearest Refl impossible
  maybeNotEqual F64Sqrt Refl impossible
  maybeNotEqual F64Add Refl impossible
  maybeNotEqual F64Sub Refl impossible
  maybeNotEqual F64Mul Refl impossible
  maybeNotEqual F64Div Refl impossible
  maybeNotEqual F64Min Refl impossible
  maybeNotEqual F64Max Refl impossible
  maybeNotEqual F64Copysign Refl impossible
  maybeNotEqual I32WrapI64 Refl impossible
  maybeNotEqual I32TruncF32S Refl impossible
  maybeNotEqual I32TruncF32U Refl impossible
  maybeNotEqual I32TruncF64S Refl impossible
  maybeNotEqual I32TruncF64U Refl impossible
  maybeNotEqual I64ExtendI32S Refl impossible
  maybeNotEqual I64ExtendI32U Refl impossible
  maybeNotEqual I64TruncF32S Refl impossible
  maybeNotEqual I64TruncF32U Refl impossible
  maybeNotEqual I64TruncF64S Refl impossible
  maybeNotEqual I64TruncF64U Refl impossible
  maybeNotEqual F32ConvertI32S Refl impossible
  maybeNotEqual F32ConvertI32U Refl impossible
  maybeNotEqual F32ConvertI64S Refl impossible
  maybeNotEqual F32ConvertI64U Refl impossible
  maybeNotEqual F32DemoteF64 Refl impossible
  maybeNotEqual F64ConvertI32S Refl impossible
  maybeNotEqual F64ConvertI32U Refl impossible
  maybeNotEqual F64ConvertI64S Refl impossible
  maybeNotEqual F64ConvertI64U Refl impossible
  maybeNotEqual F64PromoteF32 Refl impossible
  maybeNotEqual I32ReinterpretF32 Refl impossible
  maybeNotEqual I64ReinterpretF64 Refl impossible
  maybeNotEqual F32ReinterpretI32 Refl impossible
  maybeNotEqual F64ReinterpretI64 Refl impossible
  maybeNotEqual I32Extend8S Refl impossible
  maybeNotEqual I32Extend16S Refl impossible
  maybeNotEqual I64Extend8S Refl impossible
  maybeNotEqual I64Extend16S Refl impossible
  maybeNotEqual I64Extend32S Refl impossible
  maybeNotEqual I32TruncSatF32S Refl impossible
  maybeNotEqual I32TruncSatF32U Refl impossible
  maybeNotEqual I32TruncSatF64S Refl impossible
  maybeNotEqual I32TruncSatF64U Refl impossible
  maybeNotEqual I64TruncSatF32S Refl impossible
  maybeNotEqual I64TruncSatF32U Refl impossible
  maybeNotEqual I64TruncSatF64S Refl impossible
  maybeNotEqual I64TruncSatF64U Refl impossible

  total
  instr_not_equal : (Nothing = maybeEqual i1 i2) -> (i1 = i2) -> Void
  instr_not_equal maybe_nothing Refl = maybeNotEqual i1 maybe_nothing

  public export
  implementation DecEq Instr where
    decEq i1 i2 with (maybeEqual i1 i2) proof maybe_nothing
      decEq i1 i1 | Just Refl = Yes Refl
      decEq i1 i2 | Nothing = No (instr_not_equal maybe_nothing)
