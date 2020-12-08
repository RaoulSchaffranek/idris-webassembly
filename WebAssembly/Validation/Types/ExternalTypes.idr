||| Spec: https://webassembly.github.io/spec/core/valid/types.html#external-types
module WebAssembly.Validation.Types.ExternalTypes

import WebAssembly.Structure.Types
import WebAssembly.Validation.Types.Limits
import WebAssembly.Validation.Types.FunctionTypes
import WebAssembly.Validation.Types.TableTypes
import WebAssembly.Validation.Types.MemoryTypes
import WebAssembly.Validation.Types.GlobalTypes

-------------------------------------------------------------------------------
-- Validation Rules
-------------------------------------------------------------------------------

public export
data ValidExternalType : (externType : ExternType) -> Type where
  MkValidExternFunkType   : (externType : ExternType) -> (externType = Func funcType)     -> (ValidFunctionType funcType) -> ValidExternalType externType
  MkValidExternTableType  : (externType : ExternType) -> (externType = Table tableType)   -> (ValidTableType tableType)   -> ValidExternalType externType
  MkValidExternMemType    : (externType : ExternType) -> (externType = Mem memType)       -> (ValidMemoryType memType)    -> ValidExternalType externType
  MkValidExternGlobalType : (externType : ExternType) -> (externType = Global globalType) -> (ValidGlobalType globalType) -> ValidExternalType externType

-------------------------------------------------------------------------------
-- Lemmas about external-type validation
-------------------------------------------------------------------------------

total ext_invalid_func_type : (contra : ValidFunctionType funcType -> Void) -> ValidExternalType (Func funcType) -> Void
ext_invalid_func_type contra (MkValidExternFunkType (Func funcType) Refl x) = contra x
ext_invalid_func_type _ (MkValidExternTableType (Func _) Refl _) impossible
ext_invalid_func_type _ (MkValidExternMemType (Func _) Refl _) impossible
ext_invalid_func_type _ (MkValidExternGlobalType (Func _) Refl _) impossible

total ext_valid_func_type : (prof : ValidFunctionType funcType) -> ValidExternalType (Func funcType)
ext_valid_func_type (MkValidFunctionType funcType)
  = MkValidExternFunkType (Func funcType) Refl (MkValidFunctionType funcType)

total ext_invalid_table_type : (contra : ValidTableType tableType -> Void) -> ValidExternalType (Table tableType) -> Void
ext_invalid_table_type _ (MkValidExternFunkType (Table _) Refl _) impossible
ext_invalid_table_type contra (MkValidExternTableType (Table tableType) Refl x) = contra x
ext_invalid_table_type _ (MkValidExternMemType (Table _) Refl _) impossible
ext_invalid_table_type _ (MkValidExternGlobalType (Table _) Refl _) impossible

total ext_valid_table_type : (prof : ValidTableType tableType) -> ValidExternalType (Table tableType)
ext_valid_table_type (MkValidTableType limits elementType limits_valid)
  = MkValidExternTableType (Table (limits, elementType)) Refl (MkValidTableType limits elementType limits_valid)

total ext_invalid_mem_type : (contra : ValidMemoryType memType -> Void) -> ValidExternalType (Mem memType) -> Void
ext_invalid_mem_type _ (MkValidExternFunkType (Mem _) Refl _) impossible
ext_invalid_mem_type _ (MkValidExternTableType (Mem _) Refl _) impossible
ext_invalid_mem_type contra (MkValidExternMemType (Mem memType) Refl x) = contra x
ext_invalid_mem_type _ (MkValidExternGlobalType (Mem _) Refl _) impossible

total ext_valid_mem_type : (prof : ValidMemoryType memType) -> ValidExternalType (Mem memType)
ext_valid_mem_type (MkValidMemoryType memType limits_valid) = MkValidExternMemType (Mem memType) Refl (MkValidMemoryType memType limits_valid)

total ext_invalid_global_type : (contra : ValidGlobalType globalType -> Void) -> ValidExternalType (Global globalType) -> Void
ext_invalid_global_type _ (MkValidExternFunkType (Global _) Refl _) impossible
ext_invalid_global_type _ (MkValidExternTableType (Global _) Refl _) impossible
ext_invalid_global_type _ (MkValidExternMemType (Global _) Refl _) impossible
ext_invalid_global_type contra (MkValidExternGlobalType (Global globalType) Refl x) = contra x

total ext_valid_global_type : (prof : ValidGlobalType globalType) -> ValidExternalType (Global globalType)
ext_valid_global_type (MkGlobalValidType globalType) = MkValidExternGlobalType (Global globalType) Refl (MkGlobalValidType globalType)

-------------------------------------------------------------------------------
-- Decidablity of Validation
-------------------------------------------------------------------------------

total public export
isValidExternalType : (externType : ExternType) -> Dec (ValidExternalType externType)
isValidExternalType (Func funcType) = case (isFunctionTypeValid funcType) of
  No contra => No (ext_invalid_func_type contra)
  Yes prof  => Yes (ext_valid_func_type prof)
isValidExternalType (Table tableType) = case (isTableTypeValid tableType) of
  No contra => No (ext_invalid_table_type contra)
  Yes prof  => Yes (ext_valid_table_type prof)
isValidExternalType (Mem memType) =  case (isMemoryTypeValid memType) of
  No contra => No (ext_invalid_mem_type contra)
  Yes prof  => Yes (ext_valid_mem_type prof)
isValidExternalType (Global globalType) =  case (isGlobalTypeValid globalType) of
  No contra => No (ext_invalid_global_type contra)
  Yes prof  => Yes (ext_valid_global_type prof)
