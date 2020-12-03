||| Spec: https://webassembly.github.io/spec/core/valid/types.html#block-types
module WebAssembly.Validation.Types.BlockTypes

import WebAssembly.Structure
import WebAssembly.Validation.Conventions

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

||| Valid type-index blocks
public export
data ValidTypeIdxBlock : TypeIdx -> C -> FuncType -> Type where
  ||| Proof that a BlockType is valid for some given type-index
  |||
  |||   C.types[typeidx] = functype
  |||-----------------------------------
  |||      C ⊢ typeidx : functype
  |||
  MkValidTypeIdxBlock
    :  (i : TypeIdx)
    -> (c : C)
    -> (InBounds i (types c))
    -> ValidTypeIdxBlock i c (index i (types c))

||| Valid value-type blocks
public export
data ValidValTypeBlock : ResultType -> Type where
  ||| Proof that a BlockType is valid for a given ValType
  |||
  |||-------------------------------------
  |||   C ⊢ [valtype?] : [] -> [valtype?]
  |||
  MkValidValTypeBlock : (t: ValType) -> ValidValTypeBlock [t]

-------------------------------------------------------------------------------
-- Lemmas about blocktype validation
-------------------------------------------------------------------------------

||| If the typeIndex is not present in the context, the block is invalid
total
typeidx_out_of_bounds : (InBounds i (types c) -> Void) -> (ValidTypeIdxBlock i c t -> Void)
typeidx_out_of_bounds f (MkValidTypeIdxBlock i c x) = f x

||| The bounds-proof does not affect the result of the index-function
total
index_proof_irrelevant : (prfA : InBounds i xs) -> (prfB: InBounds i xs) -> (index i xs {ok = prfA}) = (index i xs {ok = prfB})
index_proof_irrelevant InFirst InFirst = Refl
index_proof_irrelevant (InLater prfA') (InLater prfB') = index_proof_irrelevant prfA' prfB'

||| If the FuncType in the context does not match the expected FuncType,
||| the block is invalid.
total
unexpected_func_type :
     (i : TypeIdx)
  -> (c : C)
  -> (InBounds i (types c))
  -> (unex : (t = index i (types c)) -> Void)
  -> (ValidTypeIdxBlock i c t -> Void)
unexpected_func_type i c prfA unex (MkValidTypeIdxBlock i c prfB)
  = unex (rewrite index_proof_irrelevant prfA prfB in Refl)

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

||| Decide whether a given type-index block is valid
total
public export
isTypeIdxBlockValid : (i : TypeIdx) -> (c : C) -> (t : FuncType) -> Dec (ValidTypeIdxBlock i c t)
isTypeIdxBlockValid i c t = case inBounds i (types c) of
  No out_of_bounds => No $ typeidx_out_of_bounds out_of_bounds
  Yes in_bounds    => case decEq t (index i (types c) {ok=in_bounds}) of
    No actual_type => No (unexpected_func_type i c in_bounds actual_type)
    Yes Refl       => Yes $ MkValidTypeIdxBlock i c in_bounds

||| Decide whether a given value-type block is valid
total
public export
isValTypeBlockValid : (t: ValType) -> Dec (ValidValTypeBlock [t])
isValTypeBlockValid t = Yes (MkValidValTypeBlock t)
