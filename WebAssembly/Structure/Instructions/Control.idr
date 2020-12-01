||| Spec: https://webassembly.github.io/spec/core/syntax/instructions.html#control-instructions
module WebAssembly.Structure.Instructions.Control

import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices

-- Definition
-- Hint: Actual control-instructions are defined in
-- WebAssembly.Structure.Instructions

public export
BlockType : Type
BlockType = Either TypeIdx (Maybe ValType)

