||| Spec: https://webassembly.github.io/spec/core/syntax/instructions.html#numeric-instructions
module WebAssembly.Structure.Instructions.Definition

import WebAssembly.Structure.Values
import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices
import WebAssembly.Structure.Instructions.Control
import WebAssembly.Structure.Instructions.Memory

import Decidable.Equality

-- Definition

public export
data Instr : Type where
  Unreachable       : Instr
  Nop               : Instr
  Block             : BlockType -> (List Instr) -> Instr
  Loop              : BlockType -> (List Instr) -> Instr
  If                : BlockType -> (List Instr) -> (List Instr) -> Instr
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
