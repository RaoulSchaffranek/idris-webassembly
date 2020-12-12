||| Spec: https://webassembly.github.io/spec/core/valid/types.html#block-types
module WebAssembly.Validation.Types.BlockTypes

import WebAssembly.Structure
import WebAssembly.Validation.Conventions

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

||| Valid blocks
public export
data ValidBlockType : BlockType -> C -> FuncType -> Type where
  ||| Proof that a BlockType is valid for some given type-index
  |||
  |||   C.types[typeidx] = functype
  |||-----------------------------------
  |||      C ⊢ typeidx : functype
  |||
  MkValidTypeIdxBlock : (c : C) -> (i : TypeIdx)
    -> {auto in_bounds: InBounds i (types c)}
    -> ValidBlockType (Left i) c (index i (types c))
  ||| Proof that a BlockType without result-type is valid
  |||
  |||-------------------------------------
  |||   C ⊢ [] : [] -> []
  |||
  MkValidBlockWithoutResult : (c : C) -> ValidBlockType (Right Nothing) c ([] ->> [])
  ||| Proof that a BlockType with some result-type is valid
  |||
  |||-------------------------------------
  |||   C ⊢ [valtype] : [] -> [valtype]
  |||
  MkValidBlockWithResult : (c : C) -> (t : ValType) -> ValidBlockType (Right (Just t)) c ([] ->> [t])

-------------------------------------------------------------------------------
-- Type Inference
-------------------------------------------------------------------------------

||| If the typeIndex is not present in the context, the block is invalid
total
typeidx_out_of_bounds : (c : C) -> (i : TypeIdx)
  -> (out_of_bounds: InBounds i (types c) -> Void)
  -> ValidBlockType (Left i) c ft
  -> Void
typeidx_out_of_bounds c i out_of_bounds (MkValidTypeIdxBlock c i {in_bounds}) = out_of_bounds in_bounds

||| If the typeIndex is not present in the context, no type can be inferred
total
typeidx_out_of_bounds2 : (c : C) -> (i : TypeIdx)
  -> (out_of_bounds: InBounds i (types c) -> Void)
  -> (ft ** ValidBlockType (Left i) c ft)
  -> Void
typeidx_out_of_bounds2 c i out_of_bounds (x ** pf) = typeidx_out_of_bounds c i out_of_bounds pf


||| Infer the FuncType of some BlockType
total public export
inferBlockType : (c : C)
              -> (bt : BlockType)
              -> Dec (ft ** ValidBlockType bt c ft)
inferBlockType c (Right Nothing) = Yes $ ([] ->> [] ** MkValidBlockWithoutResult c)
inferBlockType c (Right (Just vt)) = Yes $ ([] ->> [vt] ** MkValidBlockWithResult c vt)
inferBlockType c (Left i) = case inBounds i (types c) of
  No out_of_bounds => No $ typeidx_out_of_bounds2 c i out_of_bounds
  Yes in_bounds    => Yes $ ((index i (types c)) ** MkValidTypeIdxBlock c i)

-------------------------------------------------------------------------------
-- Type Checking
-------------------------------------------------------------------------------

||| The bounds-proof does not affect the result of the index-function
total
index_proof_irrelevant : {i : TypeIdx, a : Type, xs : List a}
  -> (prfA : InBounds i xs)
  -> (prfB: InBounds i xs)
  -> (index i xs {ok = prfA}) = (index i xs {ok = prfB})
index_proof_irrelevant InFirst InFirst = Refl
index_proof_irrelevant (InLater prfA') (InLater prfB') = index_proof_irrelevant prfA' prfB'

||| If the FuncType in the context does not match the expected FuncType,
||| the block is invalid.
total
check_failed : (c : C) -> (i : TypeIdx)
            -> {auto prfA : InBounds i (types c)}
            -> ((ft = index i (types c)) -> Void)
            -> ValidBlockType (Left i) c ft -> Void
check_failed {prfA} c i contra (MkValidTypeIdxBlock c i {in_bounds=prfB}) = contra (rewrite index_proof_irrelevant prfA prfB in Refl)

||| If the expected type does not match the actual type, the check fails
total
valtype_without_result_check_failed : (contra : (ft = ([] ->> [])) -> Void) -> ValidBlockType (Right Nothing) c ft -> Void
valtype_without_result_check_failed contra (MkValidBlockWithoutResult c) = contra Refl

||| If the expected type does not match the actual type, the check fails
total
valtype_with_result_check_failed : (contra : (ft = ([] ->> [vt])) -> Void) -> ValidBlockType (Right (Just vt)) c ft -> Void
valtype_with_result_check_failed contra (MkValidBlockWithResult c vt) = contra Refl

||| Typecheck a BlockType
total public export
checkBlockType :  (c : C)
              -> (bt : BlockType)
              -> (ft : FuncType) 
              -> Dec (ValidBlockType bt c ft)
checkBlockType c (Right Nothing) ft = case decEq ft ([] ->> []) of
  No contra => No (valtype_without_result_check_failed contra)
  Yes Refl  => Yes $ MkValidBlockWithoutResult c
checkBlockType c (Right (Just vt)) ft = case decEq ft ([] ->> [vt]) of
  No contra => No (valtype_with_result_check_failed contra)
  Yes Refl  => Yes $ MkValidBlockWithResult c vt
checkBlockType c (Left i) ft = case inBounds i (types c) of
  No out_of_bounds => No $ typeidx_out_of_bounds c i out_of_bounds
  Yes in_bounds    => case decEq ft (index i (types c)) of
    No contra => No (check_failed c i contra)
    Yes Refl  => Yes $ MkValidTypeIdxBlock c i
