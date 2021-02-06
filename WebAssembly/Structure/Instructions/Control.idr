||| Spec: https://webassembly.github.io/spec/core/syntax/instructions.html#control-instructions
module WebAssembly.Structure.Instructions.Control

import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices

-- Definition
-- Hint: Actual control-instructions are defined in
-- WebAssembly.Structure.Instructions.Definitions

public export
data BlockType : Type where
  BlockTypeTypeIdx   : TypeIdx -> BlockType
  BlockTypeEmpty     : BlockType
  BlockTypeSingelton : ValType -> BlockType

total public export
lemma_blocktypetypeindex_not_blocktypeempty : ((BlockTypeTypeIdx ti) = BlockTypeEmpty) -> Void
lemma_blocktypetypeindex_not_blocktypeempty Refl impossible

total public export
lemma_blocktypetypeindex_not_blocktypesingelton : ((BlockTypeTypeIdx ti) = (BlockTypeSingelton vt)) -> Void
lemma_blocktypetypeindex_not_blocktypesingelton Refl impossible

total public export
lemma_blocktypeempty_not_blocktypesingelton : (BlockTypeEmpty = (BlockTypeSingelton vt)) -> Void
lemma_blocktypeempty_not_blocktypesingelton Refl impossible


total public export
lemma_blocktype__typeindex_injective : ((i = j) -> Void) -> (BlockTypeTypeIdx i = BlockTypeTypeIdx j) -> Void
lemma_blocktype__typeindex_injective i_not_j Refl = i_not_j Refl


total public export
lemma_blocktype__singelton_injective : ((vt1 = vt2) -> Void) -> (BlockTypeSingelton vt1 = BlockTypeSingelton vt2) -> Void
lemma_blocktype__singelton_injective vt1_not_vt2 Refl = vt1_not_vt2 Refl

-- Decidable Equality

public export
implementation DecEq BlockType where
  decEq (BlockTypeTypeIdx k)   (BlockTypeTypeIdx j) with (decEq k j)
    decEq (BlockTypeTypeIdx k)   (BlockTypeTypeIdx j) | No contra = No $ lemma_blocktype__typeindex_injective contra
    decEq (BlockTypeTypeIdx k)   (BlockTypeTypeIdx k) | Yes Refl = Yes Refl
  decEq (BlockTypeTypeIdx k)   BlockTypeEmpty         = No lemma_blocktypetypeindex_not_blocktypeempty
  decEq (BlockTypeTypeIdx k)   (BlockTypeSingelton x) = No lemma_blocktypetypeindex_not_blocktypesingelton
  decEq BlockTypeEmpty         (BlockTypeTypeIdx k)   = No $ negEqSym lemma_blocktypetypeindex_not_blocktypeempty
  decEq BlockTypeEmpty         BlockTypeEmpty         = Yes Refl
  decEq BlockTypeEmpty         (BlockTypeSingelton x) = No lemma_blocktypeempty_not_blocktypesingelton
  decEq (BlockTypeSingelton x) (BlockTypeTypeIdx k)   = No $ negEqSym lemma_blocktypetypeindex_not_blocktypesingelton
  decEq (BlockTypeSingelton x) BlockTypeEmpty         = No $ negEqSym lemma_blocktypeempty_not_blocktypesingelton
  decEq (BlockTypeSingelton x) (BlockTypeSingelton y) with (decEq x y)
    decEq (BlockTypeSingelton x) (BlockTypeSingelton y) | No contra = No $ lemma_blocktype__singelton_injective contra
    decEq (BlockTypeSingelton x) (BlockTypeSingelton x) | Yes Refl = Yes Refl
