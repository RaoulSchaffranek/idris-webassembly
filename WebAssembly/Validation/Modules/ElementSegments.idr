module WebAssembly.Validation.Modules.ElementSegments

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Instructions
import WebAssembly.Validation.Types

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#element-segments)
|||
||| ```
||| C.tablex[x] = limits funcref    C ⊢ expr : [i32]    C ⊢ expr const    (C.funcs[y] = functype)*
||| ----------------------------------------------------------------------------------------------
||| C ⊢ {table x, offset expr, init y*} ok
||| ```
public export
data ValidElem : Context -> Elem -> Type where
  MkValidElem  : (c : Context)
              -> (x : TableIdx)
              -> (expr : Expr)
              -> (ys : List FuncIdx)
              -> {auto in_bounds: InBounds x (tables c)}
              -> ValidSequence c expr ([] ->> [TI32])
              -> ConstExpr c expr
              -> (InBounds y ys -> InBounds y (funcs c))
              -> ValidElem c (MkElem x expr ys)

