module WebAssembly.Validation.Modules.Functions

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Instructions
import WebAssembly.Validation.Types

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

