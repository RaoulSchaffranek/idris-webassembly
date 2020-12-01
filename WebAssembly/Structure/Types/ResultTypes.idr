||| Spec: http://webassembly.github.io/spec/core/syntax/types.html#result-types
module WebAssembly.Structure.Types.ResultTypes

import WebAssembly.Structure.Types.ValueTypes

public export
ResultType : Type
ResultType = List ValType
