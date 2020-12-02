||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html
module WebAssembly.Structure.Modules

import WebAssembly.Structure.Types

import public WebAssembly.Structure.Modules.Indices
import public WebAssembly.Structure.Modules.Functions
import public WebAssembly.Structure.Modules.Tables
import public WebAssembly.Structure.Modules.Memories
import public WebAssembly.Structure.Modules.Globals
import public WebAssembly.Structure.Modules.ElementSegments
import public WebAssembly.Structure.Modules.DataSegments
import public WebAssembly.Structure.Modules.StartFunction
import public WebAssembly.Structure.Modules.Exports
import public WebAssembly.Structure.Modules.Imports

import Decidable.Equality

||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#modules
public export
record Module where 
  constructor MkModule
  types    : List FuncType
  funcs    : List Func
  tables   : List Table
  mems     : List Mem
  globals  : List Global
  elem     : List Elem
  wdata    : List Data
  start    : Maybe Start
  imports  : List Import
  exports  : List Export

-- Equality

total
public export
lemma_module__types_injective : ((ty1 = ty2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__types_injective ty1_not_ty2 Refl = ty1_not_ty2 Refl

total
public export
lemma_module__funcs_injective : ((fu1 = fu2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__funcs_injective fu1_not_fu2 Refl = fu1_not_fu2 Refl

total
public export
lemma_module__tables_injective : ((ta1 = ta2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__tables_injective ta1_not_ta2 Refl = ta1_not_ta2 Refl

total
public export
lemma_module__mems_injective : ((me1 = me2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__mems_injective me1_not_me2 Refl = me1_not_me2 Refl

total
public export
lemma_module__globals_injective : ((gl1 = gl2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__globals_injective gl1_not_gl2 Refl = gl1_not_gl2 Refl

total
public export
lemma_module__elem_injective : ((el1 = el2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__elem_injective el1_not_el2 Refl = el1_not_el2 Refl

total
public export
lemma_module__data_injective : ((da1 = da2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__data_injective da1_not_da2 Refl = da1_not_da2 Refl

total
public export
lemma_module__start_injective : ((st1 = st2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__start_injective st1_not_st2 Refl = st1_not_st2 Refl

total
public export
lemma_module__imports_injective : ((im1 = im2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__imports_injective im1_not_im2 Refl = im1_not_im2 Refl

total
public export
lemma_module__exports_injective : ((ex1 = ex2) -> Void)
  -> ( MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1
     = MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
  -> Void
lemma_module__exports_injective ex1_not_ex2 Refl = ex1_not_ex2 Refl

-- Decidable Equality

public export
implementation DecEq Module where
  decEq (MkModule ty1 fu1 ta1 me1 gl1 el1 da1 st1 im1 ex1) (MkModule ty2 fu2 ta2 me2 gl2 el2 da2 st2 im2 ex2)
    = case decEq ty1 ty2 of
      No ty1_not_ty2 => No $ lemma_module__types_injective ty1_not_ty2
      Yes Refl       => case decEq fu1 fu2 of
        No fu1_not_fu2 => No $ lemma_module__funcs_injective fu1_not_fu2
        Yes Refl       => case decEq ta1 ta2 of
          No ta1_not_ta2 => No $ lemma_module__tables_injective ta1_not_ta2
          Yes Refl       => case decEq me1 me2 of
            No me1_not_me2 => No $ lemma_module__mems_injective me1_not_me2
            Yes Refl       => case decEq gl1 gl2 of
              No gl1_not_gl2 => No $ lemma_module__globals_injective gl1_not_gl2
              Yes Refl       => case decEq el1 el2 of
                No el1_not_el2 => No $ lemma_module__elem_injective el1_not_el2
                Yes Refl       => case decEq da1 da2 of
                  No da1_not_da2 => No $ lemma_module__data_injective da1_not_da2
                  Yes Refl       => case decEq st1 st2 of
                    No st1_not_st2 => No $ lemma_module__start_injective st1_not_st2
                    Yes Refl       => case decEq im1 im2 of
                      No im1_not_im2 => No $ lemma_module__imports_injective im1_not_im2
                      Yes Refl       => case decEq ex1 ex2 of
                        No ex1_not_ex2 => No $ lemma_module__exports_injective ex1_not_ex2
                        Yes Refl      => Yes Refl
