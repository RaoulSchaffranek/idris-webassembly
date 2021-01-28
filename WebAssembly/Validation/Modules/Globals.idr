module WebAssembly.Validation.Modules.Globals

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Instructions
import WebAssembly.Validation.Types

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
