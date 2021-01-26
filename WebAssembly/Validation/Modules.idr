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
