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
  data ValidSequence : Context -> (List Instr) -> FuncType -> Type where
    ||| Empty Instruction Sequence
    |||
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#empty-instruction-sequence-epsilon)
    |||
    ||| > ```
    ||| > ---------------
    ||| > C ⊢ epsilon : ft
    ||| > ```
    ValidEmpty : (c : Context) -> (ft : FuncType) -> ValidSequence c [] ft

    ||| Non-Empty Instruction Sequence
    |||
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#non-empty-instruction-sequence-xref-syntax-instructions-syntax-instr-mathit-instr-ast-xref-syntax-instructions-syntax-instr-mathit-instr-n)
    |||
    ||| ```
    ||| C ⊢ instr∗ : [t1∗] -> [t0∗ t]    C ⊢ instr : [t∗] -> [t3∗]
    ||| -----------------------------------------------------------
    ||| C ⊢ instr∗ instr : [t1∗] -> [t0∗ t3∗]
    ||| ```
    ValidCons  : (c : Context)
              -> ValidSequence c is (t1 ->> (t0 ++ t))
              -> ValidInstr c i (t ->> t3)
              -> ValidSequence c (is ++ [i]) (t1 ->> (t0 ++ t3)) 

  ||| Instructions
  public export
  data ValidInstr : Context -> Instr -> FuncType -> Type where

    ||| Sepc: https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-unreachable
    |||
    ||| ```
    ||| --------------------------------
    ||| C ⊢ unreachable : [t1∗] -> [t2∗]
    ||| ```
    MkValidUnreachable       : (c : Context)
                            -> (ft : FuncType)
                            -> ValidInstr c Unreachable ft

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-nop)
    |||
    ||| ```
    ||| ------------------
    ||| C ⊢ nop : [] -> []
    ||| ```
    MkValidNop               : (c : Context)
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
    MkValidBlock             : (c : Context)
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
    MkValidLoop              : (c : Context)
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
    MkValidIf                : (c : Context)
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
    MkValidBr                : (c : Context)
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
    MkValidBrIf              : (c : Context)
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
    MkValidBrTable           : (c : Context)
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
    MkValidReturn            : (c : Context)
                            -> (return c = Just t)
                            -> ValidInstr c (Return) ((t1 ++ t) ->> t2)

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-control-mathsf-call-x)
    |||
    ||| ```
    ||| C.funcs[x] = [t1*] -> [t2*]
    ||| ---------------------------
    ||| C ⊢ call x : [t1*] -> [t2*]
    ||| ```
    MkValidCall              : (c : Context)
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
    MkValidCallIndirect      : (c : Context)
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
    MkValidDrop              : (c : Context)
                            -> (t : ValType)
                            -> ValidInstr c Drop ([t] ->> [])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-parametric-mathsf-select)
    |||
    ||| ```
    ||| -----------------------------
    ||| C ⊢ select : [t t i32] -> [t]
    ||| ```
    MkValidSelect            : (c : Context)
                            -> (t : ValType)
                            -> ValidInstr c Select ([t, t, TI32] ->> [t])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#xref-syntax-instructions-syntax-instr-variable-mathsf-local-get-x)
    |||
    ||| ```
    ||| C.locals[x] = t
    ||| ---------------------------
    ||| C ⊢ local.get x : [] -> [t]
    ||| ```
    MkValidLocalGet          : (c : Context)
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
    MkValidLocalSet          : (c : Context)
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
    MkValidLocalTee          : (c : Context)
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
    MkValidGlobalGet         : (c : Context)
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
    MkValidGlobalSet         : (c : Context)
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
    MkValidI32Load           : (c : Context)
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
    MkValidI64Load           : (c : Context)
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
    MkValidF32Load           : (c : Context)
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
    MkValidF64Load           : (c : Context)
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
    MkValidI32Load8S         : (c : Context)
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
    MkValidI32Load8U         : (c : Context)
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
    MkValidI32Load16S        : (c : Context)
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
    MkValidI32Load16U        : (c : Context)
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
    MkValidI64Load8S         : (c : Context)
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
    MkValidI64Load8U         : (c : Context)
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
    MkValidI64Load16S        : (c : Context)
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
    MkValidI64Load16U        : (c : Context)
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
    MkValidI64Load32S        : (c : Context)
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
    MkValidI64Load32U        : (c : Context)
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
    MkValidI32Store          : (c : Context)
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
    MkValidI64Store          : (c : Context)
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
    MkValidF32Store          : (c : Context)
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
    MkValidF64Store          : (c : Context)
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
    MkValidI32Store8         : (c : Context)
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
    MkValidI32Store16        : (c : Context)
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
    MkValidI64Store8         : (c : Context)
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
    MkValidI64Store16        : (c : Context)
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
    MkValidI64Store32        : (c : Context)
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
    MkValidMemorySize        : (c : Context)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> ValidInstr c MemorySize ([] ->> [TI32])
    
    ||| [🔗 Spec]()
    |||
    ||| ```
    ||| C.mems[0] = memtype
    ||| --------------------------------
    ||| C ⊢ memory.grow : [i32] -> [I32]
    ||| ```
    MkValidMemoryGrow        : (c : Context)
                            -> {auto in_bounds: InBounds 0 (mems c)}
                            -> ValidInstr c MemoryGrow ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidI32Const          : (c : Context)
                            -> ValidInstr c (I32Const ci32) ([] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidI64Const          : (c : Context)
                            -> ValidInstr c (I64Const ci64) ([] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidF32Const          : (c : Context)
                            -> ValidInstr c (F32Const cf32) ([] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-instr-numeric-mathsf-const-c)
    |||
    ||| ```
    ||| -------------------------
    ||| C ⊢ t.const c : [] -> [t] 
    ||| ```
    MkValidF64Const          : (c : Context)
                            -> ValidInstr c (F64Const cf64) ([] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-testop-mathit-testop)
    |||
    ||| ```
    ||| ---------------------------
    ||| C ⊢ t.testop : [t] -> [i32] 
    ||| ```
    MkValidI32Eqz            : (c : Context)
                            -> ValidInstr c I32Eqz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32Eq             : (c : Context)
                            -> ValidInstr c I32Eq ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32Ne             : (c : Context)
                            -> ValidInstr c I32Ne ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LtS            : (c : Context)
                            -> ValidInstr c I32LtS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LtU            : (c : Context)
                            -> ValidInstr c I32LtU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GtS            : (c : Context)
                            -> ValidInstr c I32GtS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GtU            : (c : Context)
                            -> ValidInstr c I32GtU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LeS            : (c : Context)
                            -> ValidInstr c I32LeS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32LeU            : (c : Context)
                            -> ValidInstr c I32LeU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GeS            : (c : Context)
                            -> ValidInstr c I32GeS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI32GeU            : (c : Context)
                            -> ValidInstr c I32GeU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-testop-mathit-testop)
    |||
    ||| ```
    ||| ---------------------------
    ||| C ⊢ t.testop : [t] -> [i32] 
    ||| ```
    MkValidI64Eqz            : (c : Context)
                            -> ValidInstr c I64Eqz ([TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64Eq             : (c : Context)
                            -> ValidInstr c I64Eq ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64Ne             : (c : Context)
                            -> ValidInstr c I64Ne ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LtS            : (c : Context)
                            -> ValidInstr c I64LtS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LtU            : (c : Context)
                            -> ValidInstr c I64LtU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GtS            : (c : Context)
                            -> ValidInstr c I64GtS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GtU            : (c : Context)
                            -> ValidInstr c I64GtU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LeS            : (c : Context)
                            -> ValidInstr c I64LeS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64LeU            : (c : Context)
                            -> ValidInstr c I64LeU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GeS            : (c : Context)
                            -> ValidInstr c I64GeS ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidI64GeU            : (c : Context)
                            -> ValidInstr c I64GeU ([TI64, TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Eq             : (c : Context)
                            -> ValidInstr c F32Eq ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Ne             : (c : Context)
                            -> ValidInstr c F32Ne ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Lt             : (c : Context)
                            -> ValidInstr c F32Lt ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Gt             : (c : Context)
                            -> ValidInstr c F32Gt ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Le             : (c : Context)
                            -> ValidInstr c F32Le ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF32Ge             : (c : Context)
                            -> ValidInstr c F32Ge ([TF32, TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Eq             : (c : Context)
                            -> ValidInstr c F64Eq ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Ne             : (c : Context)
                            -> ValidInstr c F64Ne ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Lt             : (c : Context)
                            -> ValidInstr c F64Lt ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Gt             : (c : Context)
                            -> ValidInstr c F64Gt ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Le             : (c : Context)
                            -> ValidInstr c F64Le ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-relop-mathit-relop)
    |||
    ||| ```
    ||| ----------------------------
    ||| C ⊢ t.relop : [t t] -> [i32]
    ||| ```
    MkValidF64Ge             : (c : Context)
                            -> ValidInstr c F64Ge ([TF64, TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Clz            : (c : Context)
                            -> ValidInstr c I32Clz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Ctz            : (c : Context)
                            -> ValidInstr c I32Ctz ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Popcnt         : (c : Context)
                            -> ValidInstr c I32Popcnt ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Add            : (c : Context)
                            -> ValidInstr c I32Add ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Sub            : (c : Context)
                            -> ValidInstr c I32Sub ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Mul            : (c : Context)
                            -> ValidInstr c I32Mul ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32DivS           : (c : Context)
                            -> ValidInstr c I32DivS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32DivU           : (c : Context)
                            -> ValidInstr c I32DivU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32RemS           : (c : Context)
                            -> ValidInstr c I32RemS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32RemU           : (c : Context)
                            -> ValidInstr c I32RemU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32And            : (c : Context)
                            -> ValidInstr c I32And ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Or             : (c : Context)
                            -> ValidInstr c I32Or ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Xor            : (c : Context)
                            -> ValidInstr c I32Xor ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Shl            : (c : Context)
                            -> ValidInstr c I32Shl ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32ShrS           : (c : Context)
                            -> ValidInstr c I32ShrS ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32ShrU           : (c : Context)
                            -> ValidInstr c I32ShrU ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Rotl           : (c : Context)
                            -> ValidInstr c I32Rotl ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI32Rotr           : (c : Context)
                            -> ValidInstr c I32Rotr ([TI32, TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Clz            : (c : Context)
                            -> ValidInstr c I64Clz ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Ctz            : (c : Context)
                            -> ValidInstr c I64Ctz ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Popcnt         : (c : Context)
                            -> ValidInstr c I64Popcnt ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Add            : (c : Context)
                            -> ValidInstr c I64Add ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Sub            : (c : Context)
                            -> ValidInstr c I64Sub ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Mul            : (c : Context)
                            -> ValidInstr c I64Mul ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64DivS           : (c : Context)
                            -> ValidInstr c I64DivS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64DivU           : (c : Context)
                            -> ValidInstr c I64DivU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64RemS           : (c : Context)
                            -> ValidInstr c I64RemS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64RemU           : (c : Context)
                            -> ValidInstr c I64RemU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64And            : (c : Context)
                            -> ValidInstr c I64And ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Or             : (c : Context)
                            -> ValidInstr c I64Or ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Xor            : (c : Context)
                            -> ValidInstr c I64Xor ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Shl            : (c : Context)
                            -> ValidInstr c I64Shl ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64ShrS           : (c : Context)
                            -> ValidInstr c I64ShrS ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64ShrU           : (c : Context)
                            -> ValidInstr c I64ShrU ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Rotl           : (c : Context)
                            -> ValidInstr c I64Rotl ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidI64Rotr           : (c : Context)
                            -> ValidInstr c I64Rotr ([TI64, TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Abs            : (c : Context)
                            -> ValidInstr c F32Abs ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Neg            : (c : Context)
                            -> ValidInstr c F32Neg ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Ceil           : (c : Context)
                            -> ValidInstr c F32Ceil ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Floor          : (c : Context)
                            -> ValidInstr c F32Floor ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Trunc          : (c : Context)
                            -> ValidInstr c F32Trunc ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Nearest        : (c : Context)
                            -> ValidInstr c F32Nearest ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF32Sqrt           : (c : Context)
                            -> ValidInstr c F32Sqrt ([TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Add            : (c : Context)
                            -> ValidInstr c F32Add ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Sub            : (c : Context)
                            -> ValidInstr c F32Sub ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Mul            : (c : Context)
                            -> ValidInstr c F32Mul ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Div            : (c : Context)
                            -> ValidInstr c F32Div ([TF32, TF32] ->> [TF32])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Min            : (c : Context)
                            -> ValidInstr c F32Min ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Max            : (c : Context)
                            -> ValidInstr c F32Max ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF32Copysign       : (c : Context)
                            -> ValidInstr c F32Copysign ([TF32, TF32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Abs            : (c : Context)
                            -> ValidInstr c F64Abs ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Neg            : (c : Context)
                            -> ValidInstr c F64Neg ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Ceil           : (c : Context)
                            -> ValidInstr c F64Ceil ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Floor          : (c : Context)
                            -> ValidInstr c F64Floor ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Trunc          : (c : Context)
                            -> ValidInstr c F64Trunc ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Nearest        : (c : Context)
                            -> ValidInstr c F64Nearest ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidF64Sqrt           : (c : Context)
                            -> ValidInstr c F64Sqrt ([TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Add            : (c : Context)
                            -> ValidInstr c F64Add ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Sub            : (c : Context)
                            -> ValidInstr c F64Sub ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Mul            : (c : Context)
                            -> ValidInstr c F64Mul ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Div            : (c : Context)
                            -> ValidInstr c F64Div ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Min            : (c : Context)
                            -> ValidInstr c F64Min ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Max            : (c : Context)
                            -> ValidInstr c F64Max ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-binop-mathit-binop)
    |||
    ||| ```
    ||| --------------------------
    ||| C ⊢ t.binop : [t t] -> [t]
    ||| ```
    MkValidF64Copysign       : (c : Context)
                            -> ValidInstr c F64Copysign ([TF64, TF64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32WrapI64        : (c : Context)
                            -> ValidInstr c I32WrapI64 ([TI64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF32S      : (c : Context)
                            -> ValidInstr c I32TruncF32S ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF32U      : (c : Context)
                            -> ValidInstr c I32TruncF32U ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF64S      : (c : Context)
                            -> ValidInstr c I32TruncF64S ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncF64U      : (c : Context)
                            -> ValidInstr c I32TruncF64U ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ExtendI32S     : (c : Context)
                            -> ValidInstr c I64ExtendI32S ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ExtendI32U     : (c : Context)
                            -> ValidInstr c I64ExtendI32U ([TI32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF32S      : (c : Context)
                            -> ValidInstr c I64TruncF32S ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF32U      : (c : Context)
                            -> ValidInstr c I64TruncF32U ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF64S      : (c : Context)
                            -> ValidInstr c I64TruncF64S ([TF64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncF64U      : (c : Context)
                            -> ValidInstr c I64TruncF64U ([TF64] ->> [TI64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI32S    : (c : Context)
                            -> ValidInstr c F32ConvertI32S ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI32U    : (c : Context)
                            -> ValidInstr c F32ConvertI32U ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI64S    : (c : Context)
                            -> ValidInstr c F32ConvertI64S ([TI64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ConvertI64U    : (c : Context)
                            -> ValidInstr c F32ConvertI64U ([TI64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32DemoteF64      : (c : Context)
                            -> ValidInstr c F32DemoteF64 ([TF64] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI32S    : (c : Context)
                            -> ValidInstr c F64ConvertI32S ([TI32] ->> [TF64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI32U    : (c : Context)
                            -> ValidInstr c F64ConvertI32U ([TI32] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI64S    : (c : Context)
                            -> ValidInstr c F64ConvertI64S ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ConvertI64U    : (c : Context)
                            -> ValidInstr c F64ConvertI64U ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64PromoteF32     : (c : Context)
                            -> ValidInstr c F64PromoteF32 ([TF32] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32ReinterpretF32 : (c : Context)
                            -> ValidInstr c I32ReinterpretF32 ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64ReinterpretF64 : (c : Context)
                            -> ValidInstr c I64ReinterpretF64 ([TF64] ->> [TI64])

    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF32ReinterpretI32 : (c : Context)
                            -> ValidInstr c F32ReinterpretI32 ([TI32] ->> [TF32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidF64ReinterpretI64 : (c : Context)
                            -> ValidInstr c F64ReinterpretI64 ([TI64] ->> [TF64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Extend8S       : (c : Context)
                            -> ValidInstr c I32Extend8S ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI32Extend16S      : (c : Context)
                            -> ValidInstr c I32Extend16S ([TI32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend8S       : (c : Context)
                            -> ValidInstr c I64Extend8S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend16S      : (c : Context)
                            -> ValidInstr c I64Extend16S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-mathsf-xref-syntax-instructions-syntax-unop-mathit-unop)
    |||
    ||| ```
    ||| -----------------------
    ||| C ⊢ t.unop : [t] -> [t]
    ||| ```
    MkValidI64Extend32S      : (c : Context)
                            -> ValidInstr c I64Extend32S ([TI64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF32S   : (c : Context)
                            -> ValidInstr c I32TruncSatF32S ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF32U   : (c : Context)
                            -> ValidInstr c I32TruncSatF32U ([TF32] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF64S   : (c : Context)
                            -> ValidInstr c I32TruncSatF64S ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI32TruncSatF64U   : (c : Context)
                            -> ValidInstr c I32TruncSatF64U ([TF64] ->> [TI32])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF32S   : (c : Context)
                            -> ValidInstr c I64TruncSatF32S ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF32U   : (c : Context)
                            -> ValidInstr c I64TruncSatF32U ([TF32] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF64S   : (c : Context)
                            -> ValidInstr c I64TruncSatF64S ([TF64] ->> [TI64])
    
    ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/instructions.html#t-2-mathsf-xref-syntax-instructions-syntax-cvtop-mathit-cvtop-mathsf-t-1-mathsf-xref-syntax-instructions-syntax-sx-mathit-sx)
    |||
    ||| ```
    ||| ----------------------------------
    ||| C ⊢ t2.cvtop_t1_sx? : [t1] -> [t2]
    ||| ```
    MkValidI64TruncSatF64U   : (c : Context)
                            -> ValidInstr c I64TruncSatF64U ([TF64] ->> [TI64])

||| [🔗Spec](https://webassembly.github.io/spec/core/valid/instructions.html#valid-constant)
public export
data ConstInstr : (c : Context) -> Instr -> Type where
  MkConstI32       : (c : Context) -> ConstInstr c (I32Const v)
  MkConstI64       : (c : Context) -> ConstInstr c (I64Const v)
  MkConstF32       : (c : Context) -> ConstInstr c (F32Const v)
  MkConstF64       : (c : Context) -> ConstInstr c (F64Const v)
  MkConstGlobalGet : (c : Context)
                  -> {auto in_bounds: InBounds x (globals c)}
                  -> (index x (globals c) = (Const, t))
                  -> ConstInstr c (GlobalGet x)

||| [🔗Spec](https://webassembly.github.io/spec/core/valid/instructions.html#valid-constant)
public export
data ConstExpr : (c : Context) -> List Instr -> Type where
  MkConstExprEmpty : (c : Context) -> ConstExpr c []
  MkConstExprCons  : (c : Context)
                  -> ConstInstr c instr
                  -> ConstExpr c expr
                  -> ConstExpr c (instr::expr)
