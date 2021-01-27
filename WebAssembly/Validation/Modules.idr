module WebAssembly.Validation.Modules

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types
import WebAssembly.Validation.Instructions

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#functions)
|||
||| ```
||| C.types[x] = [t1*] -> [t2*]    C,locals t1* t*, labels [t2*], return [t2*] ⊢ expr : [t2*]
||| -----------------------------------------------------------------------------------------
||| C ⊢ {type x, locals t*, body expr} : [t1*] -> [t2*]
||| ```
public export
data ValidFunc : (c : C) -> Func -> FuncType -> Type where
 MkValidFunc : (c : C)
            -> (func : Func)
            -> {auto in_bounds: InBounds (type func) (types c)}
            -> (index (type func) (types c) = (t1 ->> t2))
            -> ValidSequence (record {locals $= (t1 ++), labels = [t2], return = (Just t2)} c) (body func) ([] ->> t2)
            -> ValidFunc c func (t1 ->> t2)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#tables)
|||
||| ```
||| ⊢ tabletype ok
||| --------------------------------
||| C ⊢ {type tabletype} : tabletype
||| ```
public export
data ValidTable : (c : C) -> Table -> TableType -> Type where
  MkValidTable : (c : C)
              -> (table : Table)
              -> ValidTableType (type table)
              -> ValidTable c table (type table)

              
||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#memories)
|||
||| ```
||| ⊢ memtype ok
||| --------------------------------
||| C ⊢ {type memtype} : memtype
||| ```
public export
data ValidMem : (c : C) -> Mem -> MemType -> Type where
  MkValidMem : (c : C)
            -> (mem : Mem)
            -> ValidMemoryType (type mem)
            -> ValidMem c mem (type mem)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#globals)
|||
||| ```
||| ⊢ mut t ok    C ⊢ expr : [t]    C ⊢ expr const
||| ----------------------------------------------
||| C ⊢ {type mut t, init expr} : mut t
||| ```
public export
data ValidGlobal : (c : C) -> Global -> GlobalType -> Type where
  MkValidGlobal : (c : C)
               -> (global : Global)
               -> ValidGlobalType (type global)
               -> ValidSequence c (init global) ([] ->> t)
               -> ConstExpr c (init global)
               -> ValidGlobal c global (type global)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#element-segments)
|||
||| ```
||| C.tablex[x] = limits funcref    C ⊢ expr : [i32]    C ⊢ expr const    (C.funcs[y] = functype)*
||| ----------------------------------------------------------------------------------------------
||| C ⊢ {table x, offset expr, init y*} ok
||| ```
public export
data ValidElem : (c : C) -> Elem -> Type where
  MkValidElem  : (c : C)
              -> (elem : Elem)
              -> {auto in_bounds: InBounds (table elem) (tables c)}
              -> ValidSequence c (offset elem) ([] ->> [TI32])
              -> ConstExpr c (offset elem)
              -> (InBounds y (init elem) -> InBounds y (funcs c))
              -> ValidElem c elem

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#data-segments)
|||
||| ```
||| C.mems[x] = limits    C ⊢ expr : [i32]    C ⊢ expr const
||| --------------------------------------------------------
||| C ⊢ {data x, offset expr, init b*} ok
||| ```
public export
data ValidData : (c : C) -> Data -> Type where
  MkValidData  : (c : C)
              -> (d : Data)
              -> {auto in_bounds: InBounds (wdata d) (mems c)}
              -> ValidSequence c (offset d) ([] ->> [TI32])
              -> ConstExpr c (offset d)
              -> ValidData c d

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#start-function)
|||
||| ```
||| C.funcs[x] = [] -> []
||| ---------------------
||| C ⊢ {func x} ok
||| ```
public export
data ValidStart : (c : C) -> Start -> Type where
  MkValidStart : (c : C)
              -> (start : Start)
              -> {auto in_bounds: InBounds (func start) (funcs c)}
              -> (index (func start) (funcs c) = ([] ->> []))
              -> ValidStart c start

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#exports)
public export
data ValidExportDesc : (c : C) -> ExportDesc -> ExternType -> Type where

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-exportdesc-mathsf-func-x)
  |||
  ||| ```
  ||| C.funcs[x] = functype
  ||| --------------------------
  ||| C ⊢ func x : func functype
  ||| ```
  MkValidExternalFunc    : (c : C)
                        -> (x : FuncIdx)
                        -> {auto in_bounds: InBounds x (funcs c)}
                        -> ValidExportDesc c (FuncExport x) (Func (index x (funcs c)))

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-exportdesc-mathsf-table-x)
  |||
  ||| ```
  ||| C.tables[x] = tabletype
  ||| --------------------------
  ||| C ⊢ table x : table tabletype
  ||| ```
  MkValidExternalTable   : (c : C)
                        -> (x : TableIdx)
                        -> {auto in_bounds: InBounds x (tables c)}
                        -> ValidExportDesc c (TableExport x) (Table (index x (tables c)))

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-exportdesc-mathsf-mem-x)
  |||
  ||| ```
  ||| C.mems[x] = memtype
  ||| --------------------------
  ||| C ⊢ mem x : mem memtype
  ||| ```
  MkValidExternalMem     : (c : C)
                        -> (x : MemIdx)
                        -> {auto in_bounds: InBounds x (mems c)}
                        -> ValidExportDesc c (MemExport x) (Mem (index x (mems c)))
                        
  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-exportdesc-mathsf-global-x)
  |||
  ||| ```
  ||| C.globals[x] = globaltype
  ||| --------------------------
  ||| C ⊢ global x : global globaltype
  ||| ```
  MkValidExternalGlobal  : (c : C) 
                        -> (x : GlobalIdx)
                        -> {auto in_bounds: InBounds x (globals c)}
                        -> ValidExportDesc c (GlobalExport x) (Global (index x (globals c)))


||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#exports)
public export
data ValidExport : (c : C) -> Export -> ExternType -> Type where

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-export-mathsf-name-xref-syntax-values-syntax-name-mathit-name-xref-syntax-modules-syntax-export-mathsf-desc-xref-syntax-modules-syntax-exportdesc-mathit-exportdesc)
  |||
  ||| ```
  ||| C ⊢ exportdesc : externtype
  ||| ---------------------------------------------
  ||| C ⊢ {name name, desc exportdesc} : externtype
  ||| ```
  MkValidExport  : (c : C)
                -> (name : Name)
                -> (desc : ExportDesc)
                -> ValidExportDesc c desc externType
                -> ValidExport c (MkExport name desc) externType
