||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#indices
module WebAssembly.Structure.Modules.Indices

import WebAssembly.Structure.Values

-- Definition

public export
TypeIdx : Type
TypeIdx = U32

public export
FuncIdx : Type
FuncIdx = U32

public export
TableIdx : Type
TableIdx = U32

public export
MemIdx : Type
MemIdx = U32

public export
GlobalIdx : Type
GlobalIdx = U32

public export
LocalIdx : Type
LocalIdx = U32

public export
LabelIdx : Type
LabelIdx = U32
