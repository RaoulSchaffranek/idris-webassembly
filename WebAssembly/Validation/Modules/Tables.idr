module WebAssembly.Validation.Modules.Tables

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types

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
