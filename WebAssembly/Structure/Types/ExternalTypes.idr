||| Spec: https://webassembly.github.io/spec/core/syntax/types.html#external-types
module WebAssembly.Structure.Types.ExternalTypes

import WebAssembly.Structure.Types.ValueTypes
import WebAssembly.Structure.Types.FunctionTypes
import WebAssembly.Structure.Types.TableTypes
import WebAssembly.Structure.Types.Limits
import WebAssembly.Structure.Types.MemoryTypes
import WebAssembly.Structure.Types.GlobalTypes

import Decidable.Equality

-- Definition

public export
data ExternType : Type where
  Func   : FuncType    -> ExternType
  Table  : TableType   -> ExternType
  Mem    : MemType     -> ExternType
  Global : GlobalType  -> ExternType

-- Equality

total public export
lemma_externtype__func_injective : ((x = y) -> Void) -> (Func x = Func y) -> Void
lemma_externtype__func_injective func_types_neq Refl = func_types_neq Refl

total public export
lemma_externtype__table_injective : ((x = y) -> Void) -> (Table x = Table y) -> Void
lemma_externtype__table_injective table_tables_neq Refl = table_tables_neq Refl

total public export
lemma_externtype__mem_injective : ((x = y) -> Void) -> (Mem x = Mem y) -> Void
lemma_externtype__mem_injective mem_types_neq Refl = mem_types_neq Refl

total public export
lemma_externtype__global_injective : ((x = y) -> Void) -> (Global x = Global y) -> Void
lemma_externtype__global_injective global_types_neq Refl = global_types_neq Refl

total public export
lemma_func_not_table : (Func x = Table y) -> Void
lemma_func_not_table Refl impossible

total public export
lemma_func_not_mem : (Func x = Mem y) -> Void
lemma_func_not_mem Refl impossible

total public export
lemma_func_not_global : (Func x = Global y) -> Void
lemma_func_not_global Refl impossible

total public export
lemma_table_not_func : (Table x = Func y) -> Void
lemma_table_not_func Refl impossible

total public export
lemma_table_not_mem : (Table x = Mem y) -> Void
lemma_table_not_mem Refl impossible

total public export
lemma_table_not_global : (Table x = Global y) -> Void
lemma_table_not_global Refl impossible

total public export
lemma_mem_not_func : (Mem x = Func y) -> Void
lemma_mem_not_func Refl impossible

total public export
lemma_mem_not_table : (Mem x = Table y) -> Void
lemma_mem_not_table Refl impossible

total public export
lemma_mem_not_global : (Mem x = Global y) -> Void
lemma_mem_not_global Refl impossible

total public export
lemma_global_not_func : (Global x = Func y) -> Void
lemma_global_not_func Refl impossible

total public export
lemma_global_not_table : (Global x = Table y) -> Void
lemma_global_not_table Refl impossible

total public export
lemma_global_not_mem : (Global x = Mem y) -> Void
lemma_global_not_mem Refl impossible

-- Decidable Equality

public export
implementation DecEq ExternType where
  decEq (Func x)   (Func y)   = case decEq x y of
    No func_types_neq => No (lemma_externtype__func_injective func_types_neq)
    Yes Refl          => Yes Refl
  decEq (Table x)  (Table y)  = case decEq x y of
    No table_tables_neq => No (lemma_externtype__table_injective table_tables_neq)
    Yes Refl            => Yes Refl
  decEq (Mem x)    (Mem y)    = case decEq x y of
    No mem_types_neq => No (lemma_externtype__mem_injective mem_types_neq)
    Yes Refl         => Yes Refl
  decEq (Global x) (Global y) = case decEq x y of
    No global_types_neq => No (lemma_externtype__global_injective global_types_neq)
    Yes Refl            => Yes Refl
  decEq (Func x)   (Table y)  = No lemma_func_not_table
  decEq (Func x)   (Mem y)    = No lemma_func_not_mem
  decEq (Func x)   (Global y) = No lemma_func_not_global
  decEq (Table x)  (Func y)   = No lemma_table_not_func
  decEq (Table x)  (Mem y)    = No lemma_table_not_mem
  decEq (Table x)  (Global y) = No lemma_table_not_global
  decEq (Mem x)    (Func y)   = No lemma_mem_not_func
  decEq (Mem x)    (Table y)  = No lemma_mem_not_table
  decEq (Mem x)    (Global y) = No lemma_mem_not_global
  decEq (Global x) (Func y)   = No lemma_global_not_func
  decEq (Global x) (Table y)  = No lemma_global_not_table
  decEq (Global x) (Mem y)    = No lemma_global_not_mem
