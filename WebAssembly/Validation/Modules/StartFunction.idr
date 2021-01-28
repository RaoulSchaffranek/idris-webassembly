module WebAssembly.Validation.Modules.StartFunction

import WebAssembly.Structure
import WebAssembly.Validation.Conventions
import WebAssembly.Validation.Types

||| [🔗 Spec](https://webassembly.github.io/spec/core/valid/modules.html#start-function)
|||
||| ```
||| C.funcs[x] = [] -> []
||| ---------------------
||| C ⊢ {func x} ok
||| ```
public export
data ValidStart : Context -> Start -> Type where
  MkValidStart : (c : Context)
              -> (x : FuncIdx)
              -> {auto in_bounds: InBounds x (funcs c)}
              -> (index x (funcs c) = ([] ->> []))
              -> ValidStart c (MkStart x)

