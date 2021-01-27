||| Spec: https://webassembly.github.io/spec/core/valid/conventions.html#contexts
module WebAssembly.Validation.Conventions.Contexts

import WebAssembly.Structure.Types

import Decidable.Equality

-- Definition

public export
record Context where
  constructor MkC
  types   : List FuncType
  funcs   : List FuncType
  tables  : List TableType
  mems    : List MemType
  globals : List GlobalType
  locals  : List ValType
  labels  : List ResultType
  return  : Maybe ResultType

total public export
prependTypes : List FuncType -> Context -> Context
prependTypes xs = record {types $= ((++) xs)}

total public export
prependFuncs : List FuncType -> Context -> Context
prependFuncs xs = record {funcs $= ((++) xs)}

total public export
prependTables : List TableType -> Context -> Context
prependTables xs = record {tables $= ((++) xs)}

total public export
prependMems : List MemType -> Context -> Context
prependMems xs = record {mems $= ((++) xs)}

total public export
prependGlobals : List GlobalType -> Context -> Context
prependGlobals xs = record {globals $= ((++) xs)}

total public export
prependLocals : List ValType -> Context -> Context
prependLocals xs = record {locals $= ((++) xs)}

total public export
prependLabels : List ResultType -> Context -> Context
prependLabels xs = record {labels $= ((++) xs)}

-- Equality

total public export
lemma_c__types_injective: ((ty1 = ty2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__types_injective ty1_not_ty2 Refl = ty1_not_ty2 Refl

total public export
lemma_c__funcs_injective: ((fu1 = fu2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__funcs_injective fu1_not_fu2 Refl = fu1_not_fu2 Refl

total public export
lemma_c__tables_injective: ((ta1 = ta2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__tables_injective ta1_not_ta2 Refl = ta1_not_ta2 Refl

total public export
lemma_c__mems_injective: ((me1 = me2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__mems_injective me1_not_me2 Refl = me1_not_me2 Refl

total public export
lemma_c__globals_injective: ((gl1 = gl2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__globals_injective gl1_not_gl2 Refl = gl1_not_gl2 Refl

total public export
lemma_c__locals_injective: ((lo1 = lo2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__locals_injective lo1_not_lo2 Refl = lo1_not_lo2 Refl

total public export
lemma_c__labels_injective: ((la1 = la2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__labels_injective la1_not_la2 Refl = la1_not_la2 Refl

total public export
lemma_c__return_injective: ((re1 = re2) -> Void)
  -> (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1 = MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
  -> Void
lemma_c__return_injective re1_not_re2 Refl = re1_not_re2 Refl

-- Decidable Equality

public export
implementation DecEq Context where
  decEq (MkC ty1 fu1 ta1 me1 gl1 lo1 la1 re1) (MkC ty2 fu2 ta2 me2 gl2 lo2 la2 re2)
    = case decEq ty1 ty2 of
        No ty1_not_ty2 => No $ lemma_c__types_injective ty1_not_ty2
        Yes Refl       => case decEq fu1 fu2 of
          No fu1_not_fu2 => No $ lemma_c__funcs_injective fu1_not_fu2
          Yes Refl       => case decEq ta1 ta2 of
            No ta1_not_ta2 => No $ lemma_c__tables_injective ta1_not_ta2
            Yes Refl       => case decEq me1 me2 of
              No me1_not_me2 => No $ lemma_c__mems_injective me1_not_me2
              Yes Refl       => case decEq gl1 gl2 of
                No gl1_not_gl2 => No $ lemma_c__globals_injective gl1_not_gl2
                Yes Refl       => case decEq lo1 lo2 of
                  No lo1_not_lo2 => No $ lemma_c__locals_injective lo1_not_lo2
                  Yes Refl       => case decEq la1 la2 of
                    No la1_not_la2 => No $ lemma_c__labels_injective la1_not_la2
                    Yes Refl       => case decEq re1 re2 of
                      No re1_not_re2 => No $ lemma_c__return_injective re1_not_re2
                      Yes Refl       => Yes Refl
