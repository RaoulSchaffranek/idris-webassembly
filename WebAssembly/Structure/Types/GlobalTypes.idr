||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#global-types
module WebAssembly.Structure.Types.GlobalTypes

import WebAssembly.Structure.Types.ValueTypes

import Decidable.Equality

-- Definition

public export
data Mut : Type where
  Const : Mut
  Var   : Mut

public export
GlobalType : Type
GlobalType = (Mut, ValType)

-- Equality

total public export
lemma_const_not_var : (the Mut Const) = Var -> Void
lemma_const_not_var Refl impossible

total public export
lemma_var_not_const : Var = (the Mut Const) -> Void
lemma_var_not_const Refl impossible

-- Dedidable Equality

public export
implementation DecEq Mut where
  decEq Const Const = Yes Refl
  decEq Const Var = No lemma_const_not_var
  decEq Var Const = No lemma_var_not_const
  decEq Var Var = Yes Refl
