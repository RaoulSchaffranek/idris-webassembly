||| Validation Rules for Instructions
||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html)
module WebAssembly.Validation.Instructions

import WebAssembly.Structure
import WebAssembly.Validation.Types
import WebAssembly.Validation.Conventions

import Data.List

mutual
  ||| Instruction Sequences
  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#instruction-sequences)
  public export
  data ValidSequence : C -> (List Instr) -> FuncType -> Type where
    ||| Empty Instruction Sequence
    |||
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#empty-instruction-sequence-epsilon)
    |||
    ||| > ```
    ||| > ---------------
    ||| > C ⊢ epsilon : ft
    ||| > ```
    ValidEmpty : (c : C) -> (ft : FuncType) -> ValidSequence c [] ft

    ||| Non-Empty Instruction Sequence
    |||
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#non-empty-instruction-sequence-xref-syntax-instructions-syntax-instr-mathit-instr-ast-xref-syntax-instructions-syntax-instr-mathit-instr-n)
    |||
    ||| ```
    ||| C ⊢ instr∗ : [t1∗] -> [t0∗ t]    C ⊢ instr : [t∗] -> [t3∗]
    ||| -----------------------------------------------------------
    ||| C ⊢ instr∗ instr : [t1∗] -> [t0∗ t3∗]
    ||| ```
    ValidCons  : (c : C)
              -> ValidSequence c is (t1 ->> (t0 ++ t))
              -> ValidInstr c i (t ->> t3)
              -> ValidSequence c (is ++ [i]) (t1 ->> (t0 ++ t3)) 

  ||| Instructions
  public export
  data ValidInstr : C -> Instr -> FuncType -> Type where

    ||| Sepc: https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-unreachable
    |||
    ||| ```
    ||| --------------------------------
    ||| C ⊢ unreachable : [t1∗] -> [t2∗]
    ||| ```
    MkValidUnreachable       : (c : C)
                            -> (ft : FuncType)
                            -> ValidInstr c Unreachable ft

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-nop)
    |||
    ||| ```
    ||| ------------------
    ||| C ⊢ nop : [] -> []
    ||| ```
    MkValidNop               : (c : C)
                            -> ValidInstr c Nop ([] ->> [])

    ||| Validation of `block`-instrucions
    |||
    ||| > * The block type must be valid as some function type [t∗1]→[t∗2].
    ||| > * Let C′ be the same context as C, but with the result type [t∗2] prepended to the labels vector.
    ||| > * Under context C′, the instruction sequence instr∗ must be valid with type [t∗1]→[t∗2].
    ||| > * Then the compound instruction is valid with type [t∗1]→[t∗2].
    ||| > – Source: [🔗 Core Specifation](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-block-xref-syntax-instructions-syntax-blocktype-mathit-blocktype-xref-syntax-instructions-syntax-instr-mathit-instr-ast-xref-syntax-instructions-syntax-instr-control-mathsf-end)
    |||
    ||| ```
    ||| C ⊢ blocktype: [t1∗] -> [t2∗]   C,labels[t2∗] ⊢ instr∗ : [t1∗] -> [t2∗]
    ||| -----------------------------------------------------------------------
    ||| C ⊢ block blocktype instr∗ end : [t1∗] -> [t2∗]
    ||| ```
    MkValidBlock             : (c : C)
                            -> ValidBlockType c bt (t1 ->> t2)
                            -> ValidSequence (prependLabels [t2] c) is (t1 ->> t2)
                            -> ValidInstr c (Block bt is) (t1 ->> t2)

    |||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-loop-xref-syntax-instructions-syntax-blocktype-mathit-blocktype-xref-syntax-instructions-syntax-instr-mathit-instr-ast-xref-syntax-instructions-syntax-instr-control-mathsf-end)
    |||
    ||| ```
    ||| C ⊢ blocktype: [t1∗] -> [t2∗]   C,labels[t1∗] ⊢ instr∗ : [t1∗] -> [t2∗]
    ||| -----------------------------------------------------------------------
    ||| C ⊢ loop blocktype instr∗ end : [t1∗] -> [t2∗]
    ||| ```
    MkValidLoop              : (c : C)
                            -> ValidBlockType c bt (t1 ->> t2)
                            -> ValidSequence (prependLabels [t1] c) is (t1 ->> t2)
                            -> ValidInstr c (Loop bt is) (t1 ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-if-xref-syntax-instructions-syntax-blocktype-mathit-blocktype-xref-syntax-instructions-syntax-instr-mathit-instr-1-ast-xref-syntax-instructions-syntax-instr-control-mathsf-else-xref-syntax-instructions-syntax-instr-mathit-instr-2-ast-xref-syntax-instructions-syntax-instr-control-mathsf-end)
    |||
    ||| ```
    ||| C ⊢ blocktype : [t1∗] -> [t2∗]   C,labels[t2∗] ⊢ instr1∗ : [t1∗] -> [t2∗]   C,labels[t2∗] ⊢ instr2∗ : [t1∗] -> [t2∗]
    ||| --------------------------------------------------------------------------------------------------------------------
    ||| C ⊢ if blocktype instr1∗ else instr2∗ end : [t1∗ i32] -> [t2∗]
    ||| ```
    MkValidIf                : (c : C)
                            -> ValidBlockType c bt (t1 ->> t2)
                            -> ValidSequence (prependLabels [t2] c) is (t1 ->> t2)
                            -> ValidSequence (prependLabels [t2] c) js (t1 ->> t2)
                            -> ValidInstr c (If bt is js) ((t1 ++ [TI32]) ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-br-l)
    |||
    ||| ```
    ||| C.labels[l] = [t∗]
    ||| ---------------------------
    ||| C ⊢ br l : [t1∗ t] -> [t2∗]
    ||| ```
    MkValidBr                : (c : C)
                            -> {auto in_bounds: InBounds l (labels c)}
                            -> ((index l (labels c)) = t)
                            -> ValidInstr c (Br l) ((t1 ++ t) ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-br-if-l)
    |||
    ||| ```
    ||| C.labels[l] = [t∗]
    ||| -------------------------------
    ||| C ⊢ br_if l : [t∗ TI32] -> [t∗]
    ||| ```
    MkValidBrIf              : (c : C)
                            -> {auto in_bounds: InBounds l (labels c)}
                            -> ((index l (labels c)) = t)
                            -> ValidInstr c (BrIf l) ((t ++ [TI32]) ->> t)
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-br-table-l-ast-l-n)
    |||
    ||| ```
    ||| (C.labels[l] = [t∗])∗    C.labels[lN] = [t∗]
    ||| --------------------------------------------
    ||| C ⊢ br_table l∗ lN : [t1∗ t∗ i32] -> [t2∗]
    ||| ```
    MkValidBrTable           : (c : C)
                            -> (Elem li ls -> {auto in_bounds_i: InBounds li (labels c)} -> ((index li (labels c)) = t))
                            -> {auto in_bounds: InBounds lN (labels c)}
                            -> ((index lN (labels c)) = t)
                            -> ValidInstr c (BrTable ls ln) ((t1 ++ t ++ [TI32]) ->> t2)
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-return)
    |||
    ||| ```
    ||| C.return = [t∗]
    ||| ------------------------------
    ||| C ⊢ return : [t1∗ t∗] -> [t2∗]
    ||| ```
    MkValidReturn            : (c : C)
                            -> (return c = Just t)
                            -> ValidInstr c (Return) ((t1 ++ t) ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-call-x)
    |||
    ||| ```
    ||| C.funcs[x] = [t1*] -> [t2*]
    ||| ---------------------------
    ||| C ⊢ call x : [t1*] -> [t2*]
    ||| ```
    MkValidCall              : (c : C)
                            -> (x : FuncIdx)
                            -> {auto in_bounds: InBounds x (funcs c)}
                            -> ((index x (funcs c)) = (t1 ->> t2))
                            -> ValidInstr c (Call x) (t1 ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-call-indirect-x)
    |||
    ||| ```
    ||| C.tables[0] = limits functype    C.types[x] = [t1*] -> [t2*]
    ||| ------------------------------------------------------------
    ||| C ⊢ call_indirect x : [t1* i32] -> [t2*]
    ||| ```
    MkValidCallIndirect      : (c : C)
                            -> (x : TypeIdx)
                            -> {auto in_bounds_0: InBounds 0 (tables c)}
                            -> ((snd (index 0 (tables c))) = FuncRef)
                            -> {auto in_bounds_x: InBounds x (types c)}
                            -> ((index x (types c)) = (t1 ->> t2))
                            -> ValidInstr c (CallIndirect x) ((t1 ++ [TI32]) ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-parametric-mathsf-drop)
    |||
    ||| ```
    ||| --------------------
    ||| C ⊢ drop : [t] -> [] 
    ||| ```
    MkValidDrop              : (c : C)
                            -> (t : ValType)
                            -> ValidInstr c Drop ([t] ->> [])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-parametric-mathsf-select)
    |||
    ||| ```
    ||| -----------------------------
    ||| C ⊢ select : [t t i32] -> [t]
    ||| ```
    MkValidSelect            : (c : C)
                            -> (t : ValType)
                            -> ValidInstr c Select ([t, t, TI32] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-local-get-x)
    |||
    ||| ```
    ||| C.locals[x] = t
    ||| ---------------------------
    ||| C ⊢ local.get x : [] -> [t]
    ||| ```
    MkValidLocalGet          : (c : C)
                            -> (x : LocalIdx)
                            -> {auto in_bounds: InBounds x (locals c)}
                            -> ((index x (locals c)) = t)
                            -> ValidInstr c (LocalGet x) ([] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-local-set-x)
    |||
    ||| ```
    ||| C.locals[x] = t
    ||| ---------------------------
    ||| C ⊢ local.set x : [t] -> []
    ||| ```
    MkValidLocalSet          : (c : C)
                            -> (x : LocalIdx)
                            -> {auto in_bounds: InBounds x (locals c)}
                            -> ((index x (locals c)) = t)
                            -> ValidInstr c (LocalSet x) ([t] ->> [])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-local-tee-x)
    |||
    ||| ```
    ||| C.locals[x] = t
    ||| ----------------------------
    ||| C ⊢ local.tee x : [t] -> [t]
    ||| ```
    MkValidLocalTee          : (c : C)
                            -> (x : LocalIdx)
                            -> {auto in_bounds: InBounds x (locals c)}
                            -> ((index x (locals c)) = t)
                            -> ValidInstr c (LocalTee x) ([t] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-global-get-x)
    |||
    ||| ```
    ||| C.globals[x] = mut t
    ||| ----------------------------
    ||| C ⊢ global.get x : [] -> [t]
    ||| ```
    MkValidGlobalGet         : (c : C)
                            -> (x : GlobalIdx)
                            -> {auto in_bounds: InBounds x (globals c)}
                            -> ((index x (globals c)) = (mut, t))
                            -> ValidInstr c (GlobalGet x) ([] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-global-set-x)
    |||
    ||| ```
    ||| C.globals[x] = var t
    ||| ----------------------------
    ||| C ⊢ global.set x : [] -> [t] 
    ||| ```
    MkValidGlobalSet         : (c : C)
                            -> (x : GlobalIdx)
                            -> {auto in_bounds: InBounds x (globals c)}
                            -> ((index x (globals c)) = (Var, t))
                            -> ValidInstr c (GlobalSet x) ([] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI32Load           : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (I32Load memarg) ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load           : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 8
                            -> ValidInstr c (I64Load memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidF32Load           : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (F32Load memarg) ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidF64Load           : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 8
                            -> ValidInstr c (F64Load memarg) ([TI32] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI32Load8S         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I32Load8S memarg) ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI32Load8U         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I32Load8U memarg) ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI32Load16S        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I32Load16S memarg) ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI32Load16U        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I32Load16U memarg) ([TI32] ->> [TI32])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load8S         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I64Load8S memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load8U         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I64Load8U memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load16S        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I64Load16S memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load16U        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I64Load16U memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load32S        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (I64Load32S memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-load-n-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32] -> [t]
    ||| ```
    MkValidI64Load32U        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (I64Load32U memarg) ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI32Store          : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (I32Store memarg) ([TI32, TI32] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI64Store          : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 8
                            -> ValidInstr c (I64Store memarg) ([TI32, TI64] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidF32Store          : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (F32Store memarg) ([TI32, TF32] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= |t|/8
    ||| ------------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidF64Store          : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 8
                            -> ValidInstr c (F64Store memarg) ([TI32, TF64] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-n-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ----------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI32Store8         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I32Store8 memarg) ([TI32, TI32] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-n-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ----------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI32Store16        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I32Store16 memarg) ([TI32, TI32] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-n-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ----------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI64Store8         : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 1
                            -> ValidInstr c (I64Store8 memarg) ([TI32, TI64] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-n-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ----------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI64Store16        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 2
                            -> ValidInstr c (I64Store16 memarg) ([TI32, TI64] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-memory-mathsf-store-n-xref-syntax-instructions-syntax-memarg-mathit-memarg)
    |||
    ||| ```
    ||| C.mems[0] = memtype    2^(memarg.align) <= N/8
    ||| ----------------------------------------------
    ||| C ⊢ t.load memarg : [i32 t] -> []
    ||| ```
    MkValidI64Store32        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> LTE (power 2 (align memarg)) 4
                            -> ValidInstr c (I64Store32 memarg) ([TI32, TI64] ->> [])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-memory-mathsf-memory-size)
    |||
    ||| ```
    ||| C.mems[0] = memtype
    ||| -----------------------------
    ||| C ⊢ memory.size : [] -> [i32]
    ||| ```
    MkValidMemorySize        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> ValidInstr c MemorySize ([] ->> [TI32])
    
    ||| [🔗 Spec]()
    |||
    ||| ```
    ||| C.mems[0] = memtype
    ||| --------------------------------
    ||| C ⊢ memory.grow : [i32] -> [I32]
    ||| ```
    MkValidMemoryGrow        : (c : C)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> ValidInstr c MemoryGrow ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidI32Const          : (c : C)
                            -> ValidInstr c (I32Const ci32) ([] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidI64Const          : (c : C)
                            -> ValidInstr c (I64Const ci64) ([] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidF32Const          : (c : C)
                            -> ValidInstr c (F32Const cf32) ([] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidF64Const          : (c : C)
                            -> ValidInstr c (F64Const cf64) ([] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-testop-mathit-testop)
    |||
    ||| ```
    ||| ---------------------------
    ||| C ⊢ t.testop : [t] -> [i32] 
    ||| ```
    MkValidI32Eqz            : (c : C)
                            -> ValidInstr c I32Eqz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32Eq             : (c : C)
                            -> ValidInstr c I32Eq ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32Ne             : (c : C)
                            -> ValidInstr c I32Ne ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LtS            : (c : C)
                            -> ValidInstr c I32LtS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LtU            : (c : C)
                            -> ValidInstr c I32LtU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GtS            : (c : C)
                            -> ValidInstr c I32GtS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GtU            : (c : C)
                            -> ValidInstr c I32GtU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LeS            : (c : C)
                            -> ValidInstr c I32LeS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LeU            : (c : C)
                            -> ValidInstr c I32LeU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GeS            : (c : C)
                            -> ValidInstr c I32GeS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GeU            : (c : C)
                            -> ValidInstr c I32GeU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-testop-mathit-testop)
    |||
    ||| ```
    ||| ---------------------------
    ||| C ⊢ t.testop : [t] -> [i32] 
    ||| ```
    MkValidI64Eqz            : (c : C)
                            -> ValidInstr c I64Eqz ([TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64Eq             : (c : C)
                            -> ValidInstr c I64Eq ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64Ne             : (c : C)
                            -> ValidInstr c I64Ne ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LtS            : (c : C)
                            -> ValidInstr c I64LtS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LtU            : (c : C)
                            -> ValidInstr c I64LtU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GtS            : (c : C)
                            -> ValidInstr c I64GtS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GtU            : (c : C)
                            -> ValidInstr c I64GtU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LeS            : (c : C)
                            -> ValidInstr c I64LeS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LeU            : (c : C)
                            -> ValidInstr c I64LeU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GeS            : (c : C)
                            -> ValidInstr c I64GeS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GeU            : (c : C)
                            -> ValidInstr c I64GeU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Eq             : (c : C)
                            -> ValidInstr c F32Eq ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Ne             : (c : C)
                            -> ValidInstr c F32Ne ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Lt             : (c : C)
                            -> ValidInstr c F32Lt ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Gt             : (c : C)
                            -> ValidInstr c F32Gt ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Le             : (c : C)
                            -> ValidInstr c F32Le ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Ge             : (c : C)
                            -> ValidInstr c F32Ge ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Eq             : (c : C)
                            -> ValidInstr c F64Eq ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Ne             : (c : C)
                            -> ValidInstr c F64Ne ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Lt             : (c : C)
                            -> ValidInstr c F64Lt ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Gt             : (c : C)
                            -> ValidInstr c F64Gt ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Le             : (c : C)
                            -> ValidInstr c F64Le ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Ge             : (c : C)
                            -> ValidInstr c F64Ge ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Clz            : (c : C)
                            -> ValidInstr c I32Clz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Ctz            : (c : C)
                            -> ValidInstr c I32Ctz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Popcnt         : (c : C)
                            -> ValidInstr c I32Popcnt ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Add            : (c : C)
                            -> ValidInstr c I32Add ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Sub            : (c : C)
                            -> ValidInstr c I32Sub ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Mul            : (c : C)
                            -> ValidInstr c I32Mul ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32DivS           : (c : C)
                            -> ValidInstr c I32DivS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32DivU           : (c : C)
                            -> ValidInstr c I32DivU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32RemS           : (c : C)
                            -> ValidInstr c I32RemS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32RemU           : (c : C)
                            -> ValidInstr c I32RemU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32And            : (c : C)
                            -> ValidInstr c I32And ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Or             : (c : C)
                            -> ValidInstr c I32Or ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Xor            : (c : C)
                            -> ValidInstr c I32Xor ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Shl            : (c : C)
                            -> ValidInstr c I32Shl ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32ShrS           : (c : C)
                            -> ValidInstr c I32ShrS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32ShrU           : (c : C)
                            -> ValidInstr c I32ShrU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Rotl           : (c : C)
                            -> ValidInstr c I32Rotl ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Rotr           : (c : C)
                            -> ValidInstr c I32Rotr ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Clz            : (c : C)
                            -> ValidInstr c I64Clz ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Ctz            : (c : C)
                            -> ValidInstr c I64Ctz ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Popcnt         : (c : C)
                            -> ValidInstr c I64Popcnt ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Add            : (c : C)
                            -> ValidInstr c I64Add ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Sub            : (c : C)
                            -> ValidInstr c I64Sub ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Mul            : (c : C)
                            -> ValidInstr c I64Mul ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64DivS           : (c : C)
                            -> ValidInstr c I64DivS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64DivU           : (c : C)
                            -> ValidInstr c I64DivU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64RemS           : (c : C)
                            -> ValidInstr c I64RemS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64RemU           : (c : C)
                            -> ValidInstr c I64RemU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64And            : (c : C)
                            -> ValidInstr c I64And ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Or             : (c : C)
                            -> ValidInstr c I64Or ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Xor            : (c : C)
                            -> ValidInstr c I64Xor ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Shl            : (c : C)
                            -> ValidInstr c I64Shl ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64ShrS           : (c : C)
                            -> ValidInstr c I64ShrS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64ShrU           : (c : C)
                            -> ValidInstr c I64ShrU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Rotl           : (c : C)
                            -> ValidInstr c I64Rotl ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Rotr           : (c : C)
                            -> ValidInstr c I64Rotr ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Abs            : (c : C)
                            -> ValidInstr c F32Abs ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Neg            : (c : C)
                            -> ValidInstr c F32Neg ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Ceil           : (c : C)
                            -> ValidInstr c F32Ceil ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Floor          : (c : C)
                            -> ValidInstr c F32Floor ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Trunc          : (c : C)
                            -> ValidInstr c F32Trunc ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Nearest        : (c : C)
                            -> ValidInstr c F32Nearest ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Sqrt           : (c : C)
                            -> ValidInstr c F32Sqrt ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Add            : (c : C)
                            -> ValidInstr c F32Add ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Sub            : (c : C)
                            -> ValidInstr c F32Sub ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Mul            : (c : C)
                            -> ValidInstr c F32Mul ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Div            : (c : C)
                            -> ValidInstr c F32Div ([TF32, TF32] ->> [TF32])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Min            : (c : C)
                            -> ValidInstr c F32Min ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Max            : (c : C)
                            -> ValidInstr c F32Max ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Copysign       : (c : C)
                            -> ValidInstr c F32Copysign ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Abs            : (c : C)
                            -> ValidInstr c F64Abs ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Neg            : (c : C)
                            -> ValidInstr c F64Neg ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Ceil           : (c : C)
                            -> ValidInstr c F64Ceil ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Floor          : (c : C)
                            -> ValidInstr c F64Floor ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Trunc          : (c : C)
                            -> ValidInstr c F64Trunc ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Nearest        : (c : C)
                            -> ValidInstr c F64Nearest ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Sqrt           : (c : C)
                            -> ValidInstr c F64Sqrt ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Add            : (c : C)
                            -> ValidInstr c F64Add ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Sub            : (c : C)
                            -> ValidInstr c F64Sub ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Mul            : (c : C)
                            -> ValidInstr c F64Mul ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Div            : (c : C)
                            -> ValidInstr c F64Div ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Min            : (c : C)
                            -> ValidInstr c F64Min ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Max            : (c : C)
                            -> ValidInstr c F64Max ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Copysign       : (c : C)
                            -> ValidInstr c F64Copysign ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32WrapI64        : (c : C)
                            -> ValidInstr c I32WrapI64 ([TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF32S      : (c : C)
                            -> ValidInstr c I32TruncF32S ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF32U      : (c : C)
                            -> ValidInstr c I32TruncF32U ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF64S      : (c : C)
                            -> ValidInstr c I32TruncF64S ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF64U      : (c : C)
                            -> ValidInstr c I32TruncF64U ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ExtendI32S     : (c : C)
                            -> ValidInstr c I64ExtendI32S ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ExtendI32U     : (c : C)
                            -> ValidInstr c I64ExtendI32U ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF32S      : (c : C)
                            -> ValidInstr c I64TruncF32S ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF32U      : (c : C)
                            -> ValidInstr c I64TruncF32U ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF64S      : (c : C)
                            -> ValidInstr c I64TruncF64S ([TF64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF64U      : (c : C)
                            -> ValidInstr c I64TruncF64U ([TF64] ->> [TI64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI32S    : (c : C)
                            -> ValidInstr c F32ConvertI32S ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI32U    : (c : C)
                            -> ValidInstr c F32ConvertI32U ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI64S    : (c : C)
                            -> ValidInstr c F32ConvertI64S ([TI64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI64U    : (c : C)
                            -> ValidInstr c F32ConvertI64U ([TI64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32DemoteF64      : (c : C)
                            -> ValidInstr c F32DemoteF64 ([TF64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI32S    : (c : C)
                            -> ValidInstr c F64ConvertI32S ([TI32] ->> [TF64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI32U    : (c : C)
                            -> ValidInstr c F64ConvertI32U ([TI32] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI64S    : (c : C)
                            -> ValidInstr c F64ConvertI64S ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI64U    : (c : C)
                            -> ValidInstr c F64ConvertI64U ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64PromoteF32     : (c : C)
                            -> ValidInstr c F64PromoteF32 ([TF32] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32ReinterpretF32 : (c : C)
                            -> ValidInstr c I32ReinterpretF32 ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ReinterpretF64 : (c : C)
                            -> ValidInstr c I64ReinterpretF64 ([TF64] ->> [TI64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ReinterpretI32 : (c : C)
                            -> ValidInstr c F32ReinterpretI32 ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ReinterpretI64 : (c : C)
                            -> ValidInstr c F64ReinterpretI64 ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Extend8S       : (c : C)
                            -> ValidInstr c I32Extend8S ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Extend16S      : (c : C)
                            -> ValidInstr c I32Extend16S ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend8S       : (c : C)
                            -> ValidInstr c I64Extend8S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend16S      : (c : C)
                            -> ValidInstr c I64Extend16S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend32S      : (c : C)
                            -> ValidInstr c I64Extend32S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF32S   : (c : C)
                            -> ValidInstr c I32TruncSatF32S ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF32U   : (c : C)
                            -> ValidInstr c I32TruncSatF32U ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF64S   : (c : C)
                            -> ValidInstr c I32TruncSatF64S ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF64U   : (c : C)
                            -> ValidInstr c I32TruncSatF64U ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF32S   : (c : C)
                            -> ValidInstr c I64TruncSatF32S ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF32U   : (c : C)
                            -> ValidInstr c I64TruncSatF32U ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF64S   : (c : C)
                            -> ValidInstr c I64TruncSatF64S ([TF64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF64U   : (c : C)
                            -> ValidInstr c I64TruncSatF64U ([TF64] ->> [TI64])
