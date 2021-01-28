module WebAssembly.Validation.Modules.Imports

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#imports)
public export
data ValidImportDesc : Context -> ImportDesc -> ExternType -> Type where
  
  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-importdesc-mathsf-func-x)
  |||
  ||| ```
  ||| C.types[x] = [t1*] -> [t2*]
  ||| --------------------------------
  ||| C ⊢ func x : func [t1*] -> [t2*]
  ||| ```
  ValidImportFunc  : (c : Context)
                  -> (x : TypeIdx)
                  -> {auto in_bounds: InBounds x (types c)}
                  -> ValidImportDesc c (FuncImport x) (Func (index x (types c)))

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-importdesc-mathsf-table-xref-syntax-types-syntax-tabletype-mathit-tabletype)
  |||
  ||| ```
  ||| tabletype ok
  ||| -------------------------------------
  ||| C ⊢ table tabletype : table tabletype
  ||| ```
  MkValidImportTable : (c : Context)
                    -> (tabletype : TableType)
                    -> ValidTableType tabletype
                    -> ValidImportDesc c (TableImport tabletype) (Table tabletype)

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-importdesc-mathsf-mem-xref-syntax-types-syntax-memtype-mathit-memtype)
  |||
  ||| ```
  ||| memtype ok
  ||| -----------------------------
  ||| C ⊢ mem memtype : mem memtype
  ||| ```
  MkValidImportMem : (c : Context)
                  -> (memtype : MemType)
                  -> ValidMemoryType memtype
                  -> ValidImportDesc c (MemImport memtype) (Mem memtype)

  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-importdesc-mathsf-global-xref-syntax-types-syntax-globaltype-mathit-globaltype)
  |||
  ||| ```
  ||| globaltype ok
  ||| -----------------------------
  ||| C ⊢ global globaltype : global globaltype
  ||| ```
  MkValidImportGlobal  : (c : Context)
                      -> (globaltype : GlobalType)
                      -> ValidGlobalType globaltype
                      -> ValidImportDesc c (GlobalImport globaltype) (Global globaltype)

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#imports)
public export
data ValidImport : Context -> Import -> ExternType -> Type where
  ||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#xref-syntax-modules-syntax-import-mathsf-module-xref-syntax-values-syntax-name-mathit-name-1-xref-syntax-modules-syntax-import-mathsf-name-xref-syntax-values-syntax-name-mathit-name-2-xref-syntax-modules-syntax-import-mathsf-desc-xref-syntax-modules-syntax-importdesc-mathit-importdesc)
  |||
  ||| ```
  ||| C ⊢ importdesc : externtype
  ||| ------------------------------------------------------------
  ||| C ⊢ {module name1, name name2, desc importdesc} : externtype
  ||| ```
  MkValidImport  : (c : Context)
                -> (name1 : Name)
                -> (name2 : Name)
                -> (importdesc : ImportDesc)
                -> (externtype : ExternType)
                -> ValidImportDesc c importdesc externtype
                -> ValidImport c (MkImport name1 name2 importdesc) externtype
