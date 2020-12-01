||| Spec: https://webassembly.github.io/spec/core/syntax/modules.html#exports
module WebAssembly.Structure.Modules.Exports

import WebAssembly.Structure.Values
import WebAssembly.Structure.Modules.Indices

import Decidable.Equality

-- Definition

public export
data ExportDesc : Type where
  FuncExport   : FuncIdx   -> ExportDesc
  TableExport  : TableIdx  -> ExportDesc
  MemExport    : MemIdx    -> ExportDesc
  GlobalExport : GlobalIdx -> ExportDesc

public export
record Export where
  constructor MkExport
  name : Name
  desc : ExportDesc

-- Equality

public export
lemma_funcexport__injective : ((f1 = f2) -> Void) -> (FuncExport f1 = FuncExport f2) -> Void
lemma_funcexport__injective f1_not_f2 Refl = f1_not_f2 Refl

public export
lemma_tableexport__injective : ((t1 = t2) -> Void) -> (TableExport t1 = TableExport t2) -> Void
lemma_tableexport__injective t1_not_t2 Refl = t1_not_t2 Refl

public export
lemma_memexport__injective : ((m1 = m2) -> Void) -> (MemExport m1 = MemExport m2) -> Void
lemma_memexport__injective m1_not_m2 Refl = m1_not_m2 Refl
 
public export
lemma_globalexport__injective : ((g1 = g2) -> Void) -> (GlobalExport g1 = GlobalExport g2) -> Void
lemma_globalexport__injective g1_not_g2 Refl = g1_not_g2 Refl

public export
lemma_funcexport_not_tableexport : (FuncExport f = TableExport t) -> Void
lemma_funcexport_not_tableexport Refl impossible

public export
lemma_funcexport_not_memexport : (FuncExport f = MemExport m) -> Void
lemma_funcexport_not_memexport Refl impossible

public export
lemma_funcexport_not_globalexport : (FuncExport f = GlobalExport g) -> Void
lemma_funcexport_not_globalexport Refl impossible


public export
lemma_tableexport_not_funcexport : (TableExport t = FuncExport f) -> Void
lemma_tableexport_not_funcexport Refl impossible

public export
lemma_tableexport_not_memexport : (TableExport t = MemExport m) -> Void
lemma_tableexport_not_memexport Refl impossible

public export
lemma_tableexport_not_globalexport : (TableExport t = GlobalExport g) -> Void
lemma_tableexport_not_globalexport Refl impossible


public export
lemma_memexport_not_tableexport : (MemExport m = TableExport t) -> Void
lemma_memexport_not_tableexport Refl impossible

public export
lemma_memexport_not_funcxport : (MemExport m = FuncExport f) -> Void
lemma_memexport_not_funcxport Refl impossible

public export
lemma_memexport_not_globalexport : (MemExport m = GlobalExport g) -> Void
lemma_memexport_not_globalexport Refl impossible


public export
lemma_globalexport_not_tableexport : (GlobalExport g = TableExport t) -> Void
lemma_globalexport_not_tableexport Refl impossible

public export
lemma_globalexport_not_funcxport : (GlobalExport g = FuncExport m) -> Void
lemma_globalexport_not_funcxport Refl impossible

public export
lemma_globalexport_not_memexport : (GlobalExport g = MemExport m) -> Void
lemma_globalexport_not_memexport Refl impossible

public export
lemma_export__name_injective : ((n1 = n2) -> Void) -> (MkExport n1 d1 = MkExport n2 d2) -> Void
lemma_export__name_injective n1_not_n2 Refl = n1_not_n2 Refl

public export
lemma_export__desc_injective : ((d1 = d2) -> Void) -> (MkExport n1 d1 = MkExport n2 d2) -> Void
lemma_export__desc_injective d1_not_d2 Refl = d1_not_d2 Refl

-- Decidable Equality

public export
implementation DecEq ExportDesc where
  decEq (FuncExport x)   (FuncExport y)   = case decEq x y of
    No x_not_y => No $ lemma_funcexport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (FuncExport x)   (TableExport y)  = No lemma_funcexport_not_tableexport
  decEq (FuncExport x)   (MemExport y)    = No lemma_funcexport_not_memexport
  decEq (FuncExport x)   (GlobalExport y) = No lemma_funcexport_not_globalexport
  decEq (TableExport x)  (FuncExport y)   = No lemma_tableexport_not_funcexport
  decEq (TableExport x)  (TableExport y)  = case decEq x y of
    No x_not_y => No $ lemma_tableexport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (TableExport x)  (MemExport y)    = No lemma_tableexport_not_memexport
  decEq (TableExport x)  (GlobalExport y) = No lemma_tableexport_not_globalexport
  decEq (MemExport x)    (FuncExport y)   = No lemma_memexport_not_funcxport
  decEq (MemExport x)    (TableExport y)  = No lemma_memexport_not_tableexport
  decEq (MemExport x)    (MemExport y)    = case decEq x y of
    No x_not_y => No $ lemma_memexport__injective x_not_y
    Yes Refl   => Yes Refl
  decEq (MemExport x)    (GlobalExport y) = No lemma_memexport_not_globalexport
  decEq (GlobalExport x) (FuncExport y)   = No lemma_globalexport_not_funcxport
  decEq (GlobalExport x) (TableExport y)  = No lemma_globalexport_not_tableexport
  decEq (GlobalExport x) (MemExport y)    = No lemma_globalexport_not_memexport
  decEq (GlobalExport x) (GlobalExport y) = case decEq x y of
    No x_not_y => No $ lemma_globalexport__injective x_not_y
    Yes Refl   => Yes Refl

public export
implementation DecEq Export where
  decEq (MkExport n1 d1) (MkExport n2 d2) = case decEq n1 n2 of
    No n1_not_n2 => No $ lemma_export__name_injective n1_not_n2
    Yes Refl     => case decEq d1 d2 of
      No d1_not_d2 => No $ lemma_export__desc_injective d1_not_d2
      Yes Refl     => Yes Refl
