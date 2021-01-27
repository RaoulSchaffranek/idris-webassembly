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
data ValidFunc : Context -> Func -> FuncType -> Type where
 MkValidFunc : (c : Context)
            -> (x : TypeIdx)
            -> (t : ResultType)
            -> (t1 : ResultType)
            -> (t2 : ResultType)
            -> (expr : Expr)
            -> {auto in_bounds: InBounds x (types c)}
            -> (index x (types c) = (t1 ->> t2))
            -> ValidSequence (record {locals = (t1 ++ t), labels = [t2], return = (Just t2)} c) expr ([] ->> t2)
            -> ValidFunc c (MkFunc x t expr) (t1 ->> t2)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#tables)
|||
||| ```
||| ⊢ tabletype ok
||| --------------------------------
||| C ⊢ {type tabletype} : tabletype
||| ```
public export
data ValidTable : Context -> Table -> TableType -> Type where
  MkValidTable : (c : Context)
              -> (tabletype : TableType)
              -> ValidTableType tabletype
              -> ValidTable c (MkTable tableype) tabletype

              
||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#memories)
|||
||| ```
||| ⊢ memtype ok
||| --------------------------------
||| C ⊢ {type memtype} : memtype
||| ```
public export
data ValidMem : Context -> Mem -> MemType -> Type where
  MkValidMem : (c : Context)
            -> (memtype : MemType)
            -> ValidMemoryType memtype
            -> ValidMem c (MkMem memtype) memtype

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#globals)
|||
||| ```
||| ⊢ mut t ok    C ⊢ expr : [t]    C ⊢ expr const
||| ----------------------------------------------
||| C ⊢ {type mut t, init expr} : mut t
||| ```
public export
data ValidGlobal : Context -> Global -> GlobalType -> Type where
  MkValidGlobal : (c : Context)
               -> (mut : Mut)
               -> (t : ValType)
               -> (expr : Expr)
               -> ValidGlobalType (mut, t)
               -> ValidSequence c expr ([] ->> [t])
               -> ConstExpr c expr
               -> ValidGlobal c (MkGlobal (mut, t) expr) (mut, t)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#element-segments)
|||
||| ```
||| C.tablex[x] = limits funcref    C ⊢ expr : [i32]    C ⊢ expr const    (C.funcs[y] = functype)*
||| ----------------------------------------------------------------------------------------------
||| C ⊢ {table x, offset expr, init y*} ok
||| ```
public export
data ValidElem : (c : Context) -> Elem -> Type where
  MkValidElem  : (c : Context)
              -> (x : TableIdx)
              -> (expr : Expr)
              -> (ys : List FuncIdx)
              -> {auto in_bounds: InBounds x (tables c)}
              -> ValidSequence c expr ([] ->> [TI32])
              -> ConstExpr c expr
              -> (InBounds y ys -> InBounds y (funcs c))
              -> ValidElem c (MkElem x expr ys)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#data-segments)
|||
||| ```
||| C.mems[x] = limits    C ⊢ expr : [i32]    C ⊢ expr const
||| --------------------------------------------------------
||| C ⊢ {data x, offset expr, init b*} ok
||| ```
public export
data ValidData : (c : Context) -> Data -> Type where
  MkValidData  : (c : Context)
              -> (x : MemIdx)
              -> (expr : Expr)
              -> (bs : List Byte)
              -> {auto in_bounds: InBounds x (mems c)}
              -> ValidSequence c expr ([] ->> [TI32])
              -> ConstExpr c expr
              -> ValidData c (MkData x expr bs)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#start-function)
|||
||| ```
||| C.funcs[x] = [] -> []
||| ---------------------
||| C ⊢ {func x} ok
||| ```
public export
data ValidStart : (c : Context) -> Start -> Type where
  MkValidStart : (c : Context)
              -> (x : FuncIdx)
              -> {auto in_bounds: InBounds x (funcs c)}
              -> (index x (funcs c) = ([] ->> []))
              -> ValidStart c (MkStart x)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#exports)
public export
data ValidExportDesc : (c : Context) -> ExportDesc -> ExternType -> Type where

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-exportdesc-mathsf-func-x)
  |||
  ||| ```
  ||| C.funcs[x] = functype
  ||| --------------------------
  ||| C ⊢ func x : func functype
  ||| ```
  MkValidExternalFunc    : (c : Context)
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
  MkValidExternalTable   : (c : Context)
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
  MkValidExternalMem     : (c : Context)
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
  MkValidExternalGlobal  : (c : Context) 
                        -> (x : GlobalIdx)
                        -> {auto in_bounds: InBounds x (globals c)}
                        -> ValidExportDesc c (GlobalExport x) (Global (index x (globals c)))


||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#exports)
public export
data ValidExport : (c : Context) -> Export -> ExternType -> Type where

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-export-mathsf-name-xref-syntax-values-syntax-name-mathit-name-xref-syntax-modules-syntax-export-mathsf-desc-xref-syntax-modules-syntax-exportdesc-mathit-exportdesc)
  |||
  ||| ```
  ||| C ⊢ exportdesc : externtype
  ||| ---------------------------------------------
  ||| C ⊢ {name name, desc exportdesc} : externtype
  ||| ```
  MkValidExport  : (c : Context)
                -> (name : Name)
                -> (desc : ExportDesc)
                -> ValidExportDesc c desc externType
                -> ValidExport c (MkExport name desc) externType
