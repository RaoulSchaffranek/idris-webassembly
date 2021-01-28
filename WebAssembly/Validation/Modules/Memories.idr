module WebAssembly.Validation.Modules.Memories

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types

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
