||| Spec: https://webassembly.github.io/spec/core/valid/types.html#block-types
module WebAssembly.Validation.Types.BlockTypes

import WebAssembly.Structure
import WebAssembly.Validation.Conventions

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

||| Valid type-index blocks
public export
data ValidTypeIdxBlock : BlockType -> C -> FuncType -> Type where
  ||| Proof that a BlockType is valid for some given type-index
  |||
  |||   C.types[typeidx] = functype
  |||-----------------------------------
  |||      C ⊢ typeidx : functype
  |||
  MkValidTypeIdxBlock : (c : C) -> (i : TypeIdx)
    -> {auto in_bounds: InBounds i (types c)}
    -> ValidTypeIdxBlock (Left i) c (index i (types c))

||| Valid value-type blocks
public export
data ValidValTypeBlock : BlockType -> FuncType -> Type where
  ||| Proof that a BlockType without result-type is valid
  |||
  |||-------------------------------------
  |||   C ⊢ [] : [] -> []
  |||
  MkValidBlockWithoutResult : ValidValTypeBlock (Right Nothing) ([] ->> [])
  ||| Proof that a BlockType with some result-type is valid
  |||
  |||-------------------------------------
  |||   C ⊢ [valtype] : [] -> [valtype]
  |||
  MkValidBlockWithResult : (t : ValType) -> ValidValTypeBlock (Right (Just t)) ([] ->> [t])

-------------------------------------------------------------------------------
-- Type Inference of TypeIdx-Blocks
-------------------------------------------------------------------------------

||| If the typeIndex is not present in the context, the block is invalid
total
typeidx_out_of_bounds : (c : C) -> (i : TypeIdx)
  -> (out_of_bounds: InBounds i (types c) -> Void)
  -> ValidTypeIdxBlock (Left i) c ft
  -> Void
typeidx_out_of_bounds c i out_of_bounds (MkValidTypeIdxBlock c i {in_bounds}) = out_of_bounds in_bounds

||| If the typeIndex is not present in the context, no type can be inferred
total
typeidx_out_of_bounds2 : (c : C) -> (i : TypeIdx)
  -> (out_of_bounds: InBounds i (types c) -> Void)
  -> (ft ** ValidTypeIdxBlock (Left i) c ft)
  -> Void
typeidx_out_of_bounds2 c i out_of_bounds (x ** pf) = typeidx_out_of_bounds c i out_of_bounds pf

||| ValueType-Blocks are never valid TypeIdx-Blocks
total
public export
rightTypeIdxVoid : (ValidTypeIdxBlock (Right r) c ft) -> Void
rightTypeIdxVoid (MkValidTypeIdxBlock _ _) impossible

||| ValueType-Blocks are never valid TypeIdx-Blocks for a given FuncType
total
public export
rightTypeIdxVoid2 : (ft ** ValidTypeIdxBlock (Right r) c ft) -> Void
rightTypeIdxVoid2 (ft ** bt) = rightTypeIdxVoid bt

||| Infer the FuncType of some BlockType bt, some TypeIdx i in some Context c
total
public export
inferFuncType :  (c : C)
              -> (bt : BlockType)
              -> Dec (ft ** ValidTypeIdxBlock bt c ft)
inferFuncType c (Right r) = No rightTypeIdxVoid2
inferFuncType c (Left i) = case inBounds i (types c) of
  No out_of_bounds => No $ typeidx_out_of_bounds2 c i out_of_bounds
  Yes in_bounds    => Yes $ ((index i (types c)) ** MkValidTypeIdxBlock c i)

-------------------------------------------------------------------------------
-- Type Checking of TypeIdx-Blocks
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
            -> ValidTypeIdxBlock (Left i) c ft -> Void
check_failed {prfA} c i contra (MkValidTypeIdxBlock c i {in_bounds=prfB}) = contra (rewrite index_proof_irrelevant prfA prfB in Refl)

||| Decide whether a given type-index block is valid
total
public export
checkFuncType :  (c : C)
              -> (bt : BlockType)
              -> (ft : FuncType) 
              -> Dec (ValidTypeIdxBlock bt c ft)
checkFuncType c (Right r) ft = No rightTypeIdxVoid
checkFuncType c (Left i) ft = case inBounds i (types c) of
  No out_of_bounds => No $ typeidx_out_of_bounds c i out_of_bounds
  Yes in_bounds    => case decEq ft (index i (types c)) of
    No contra => No (check_failed c i contra)
    Yes Refl  => Yes $ MkValidTypeIdxBlock c i

-------------------------------------------------------------------------------
-- Type Inference of ValType Blocks
-------------------------------------------------------------------------------

||| TypeIdx-Blocks are never valid ValType-Blocks
total
public export
leftValTypeVoid : (ValidValTypeBlock (Left l) ft) -> Void
leftValTypeVoid MkValidBlockWithoutResult impossible
leftValTypeVoid (MkValidBlockWithResult _) impossible

||| TypeIdx-Blocks are never valid ValType-Blocks for a given FuncType
total
public export
leftValTypeVoid2 : (ft : FuncType ** ValidValTypeBlock (Left l) ft) -> Void
leftValTypeVoid2 (ft ** bt) = leftValTypeVoid bt

||| Infer the FuncType of some ValType-Block
total
public export
inferValTypeBlock : (bt : BlockType) -> Dec (ft ** ValidValTypeBlock bt ft)
inferValTypeBlock (Left l) = No leftValTypeVoid2
inferValTypeBlock (Right Nothing) = Yes $ ([] ->> [] ** MkValidBlockWithoutResult)
inferValTypeBlock (Right (Just vt)) = Yes $ ([] ->> [vt] ** MkValidBlockWithResult vt)

-------------------------------------------------------------------------------
-- Type Checking of ValType Blocks
-------------------------------------------------------------------------------

||| If the expected type does not match the actual type, the check fails
valtype_without_result_check_failed : (contra : (ft = ([] ->> [])) -> Void) -> ValidValTypeBlock (Right Nothing) ft -> Void
valtype_without_result_check_failed contra MkValidBlockWithoutResult = contra Refl

||| If the expected type does not match the actual type, the check fails
valtype_with_result_check_failed : (contra : (ft = ([] ->> [vt])) -> Void) -> ValidValTypeBlock (Right (Just vt)) ft -> Void
valtype_with_result_check_failed contra (MkValidBlockWithResult vt) = contra Refl

||| Check the type of some ValType-block
total
public export
checkValTypeBlock : (bt: BlockType) -> (ft : FuncType) -> Dec (ValidValTypeBlock bt ft)
checkValTypeBlock (Left l) ft = No leftValTypeVoid
checkValTypeBlock (Right Nothing) ft = case decEq ft ([] ->> []) of
  No contra => No (valtype_without_result_check_failed contra)
  Yes Refl  => Yes $ MkValidBlockWithoutResult
checkValTypeBlock (Right (Just vt)) ft = case decEq ft ([] ->> [vt]) of
  No contra => No (valtype_with_result_check_failed contra)
  Yes Refl  => Yes $ MkValidBlockWithResult vt
