||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#imports
module WebAssembly.Structure.Modules.Imports

import WebAssembly.Structure.Values
import WebAssembly.Structure.Types
import WebAssembly.Structure.Modules.Indices

-- Definition

public export
data ImportDesc : Type where
  FuncImport   : TypeIdx    -> ImportDesc
  TableImport  : TableType  -> ImportDesc
  MemImport    : MemType    -> ImportDesc
  GlobalImport : GlobalType -> ImportDesc

public export
record Import where
  constructor MkImport
  wmodule : Name
  name : Name
  desc : ImportDesc

-- Equality

total public export
lemma_funcimport__injective : ((f1 = f2) -> Void) -> (FuncImport f1 = FuncImport f2) -> Void
lemma_funcimport__injective f1_not_f2 Refl = f1_not_f2 Refl

total public export
lemma_tableimport__injective : ((t1 = t2) -> Void) -> (TableImport t1 = TableImport t2) -> Void
lemma_tableimport__injective t1_not_t2 Refl = t1_not_t2 Refl

total public export
lemma_memimport__injective : ((m1 = m2) -> Void) -> (MemImport m1 = MemImport m2) -> Void
lemma_memimport__injective m1_not_m2 Refl = m1_not_m2 Refl
 
total public export
lemma_globalimport__injective : ((g1 = g2) -> Void) -> (GlobalImport g1 = GlobalImport g2) -> Void
lemma_globalimport__injective g1_not_g2 Refl = g1_not_g2 Refl

total public export
lemma_funcimport_not_tableexport : (FuncImport f = TableImport t) -> Void
lemma_funcimport_not_tableexport Refl impossible

total public export
lemma_funcimport_not_memexport : (FuncImport f = MemImport m) -> Void
lemma_funcimport_not_memexport Refl impossible

total public export
lemma_funcimport_not_globalexport : (FuncImport f = GlobalImport g) -> Void
lemma_funcimport_not_globalexport Refl impossible


total public export
lemma_tableimport_not_funcexport : (TableImport t = FuncImport f) -> Void
lemma_tableimport_not_funcexport Refl impossible

total public export
lemma_tableimport_not_memexport : (TableImport t = MemImport m) -> Void
lemma_tableimport_not_memexport Refl impossible

total public export
lemma_tableimport_not_globalexport : (TableImport t = GlobalImport g) -> Void
lemma_tableimport_not_globalexport Refl impossible


total public export
lemma_memimport_not_tableexport : (MemImport m = TableImport t) -> Void
lemma_memimport_not_tableexport Refl impossible

total public export
lemma_memimport_not_funcxport : (MemImport m = FuncImport f) -> Void
lemma_memimport_not_funcxport Refl impossible

total public export
lemma_memimport_not_globalexport : (MemImport m = GlobalImport g) -> Void
lemma_memimport_not_globalexport Refl impossible


total public export
lemma_globalimport_not_tableexport : (GlobalImport g = TableImport t) -> Void
lemma_globalimport_not_tableexport Refl impossible

total public export
lemma_globalimport_not_funcxport : (GlobalImport g = FuncImport m) -> Void
lemma_globalimport_not_funcxport Refl impossible

total public export
lemma_globalimport_not_memexport : (GlobalImport g = MemImport m) -> Void
lemma_globalimport_not_memexport Refl impossible

total public export
lemma_import__module_injective : ((m1 = m2) -> Void) -> (MkImport m1 n1 d1 = MkImport m2 n2 d2) -> Void
lemma_import__module_injective m1_not_m2 Refl = m1_not_m2 Refl

total public export
lemma_import__name_injective : ((n1 = n2) -> Void) -> (MkImport m1 n1 d1 = MkImport m2 n2 d2) -> Void
lemma_import__name_injective n1_not_n2 Refl = n1_not_n2 Refl

total public export
lemma_import__desc_injective : ((d1 = d2) -> Void) -> (MkImport m1 n1 d1 = MkImport m2 n2 d2) -> Void
lemma_import__desc_injective d1_not_d2 Refl = d1_not_d2 Refl

-- Decidable Equality

public export
implementation DecEq ImportDesc where
  decEq (FuncImport x)   (FuncImport y)   = case decEq x y of
    No x_not_y => No $ lemma_funcimport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (FuncImport x)   (TableImport y)  = No lemma_funcimport_not_tableexport
  decEq (FuncImport x)   (MemImport y)    = No lemma_funcimport_not_memexport
  decEq (FuncImport x)   (GlobalImport y) = No lemma_funcimport_not_globalexport
  decEq (TableImport x)  (FuncImport y)   = No lemma_tableimport_not_funcexport
  decEq (TableImport x)  (TableImport y)  = case decEq x y of
    No x_not_y => No $ lemma_tableimport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (TableImport x)  (MemImport y)    = No lemma_tableimport_not_memexport
  decEq (TableImport x)  (GlobalImport y) = No lemma_tableimport_not_globalexport
  decEq (MemImport x)    (FuncImport y)   = No lemma_memimport_not_funcxport
  decEq (MemImport x)    (TableImport y)  = No lemma_memimport_not_tableexport
  decEq (MemImport x)    (MemImport y)    = case decEq x y of
    No x_not_y => No $ lemma_memimport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (MemImport x)    (GlobalImport y) = No lemma_memimport_not_globalexport
  decEq (GlobalImport x) (FuncImport y)   = No lemma_globalimport_not_funcxport
  decEq (GlobalImport x) (TableImport y)  = No lemma_globalimport_not_tableexport
  decEq (GlobalImport x) (MemImport y)    = No lemma_globalimport_not_memexport
  decEq (GlobalImport x) (GlobalImport y) = case decEq x y of
    No x_not_y => No $ lemma_globalimport__injective x_not_y
    Yes Refl   => Yes Refl

public export
implementation DecEq Import where
  decEq (MkImport m1 n1 d1) (MkImport m2 n2 d2) = case decEq m1 m2 of
    No m1_not_m2 => No $ lemma_import__module_injective m1_not_m2
    Yes Refl     => case decEq n1 n2 of
      No n1_not_n2 => No $ lemma_import__name_injective n1_not_n2
      Yes Refl     => case decEq d1 d2 of
        No d1_not_d2 => No $ lemma_import__desc_injective d1_not_d2
        Yes Refl     => Yes Refl
