module WebAssembly.Validation.Modules.DataSegments

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Instructions
import WebAssembly.Validation.Types

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#data-segments)
|||
||| ```
||| C.mems[x] = limits    C ⊢ expr : [i32]    C ⊢ expr const
||| --------------------------------------------------------
||| C ⊢ {data x, offset expr, init b*} ok
||| ```
public export
data ValidData : Context -> Data -> Type where
  MkValidData  : (c : Context)
              -> (x : MemIdx)
              -> (expr : Expr)
              -> (bs : List Byte)
              -> {auto in_bounds: InBounds x (mems c)}
              -> ValidSequence c expr ([] ->> [TI32])
              -> ConstExpr c expr
              -> ValidData c (MkData x expr bs)
