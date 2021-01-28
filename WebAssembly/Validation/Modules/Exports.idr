module WebAssembly.Validation.Modules.Exports

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#exports)
public export
data ValidExportDesc : Context -> ExportDesc -> ExternType -> Type where

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
data ValidExport : Context -> Export -> ExternType -> Type where

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
                -> (externtype : ExternType)
                -> ValidExportDesc c desc externType
                -> ValidExport c (MkExport name desc) externType
