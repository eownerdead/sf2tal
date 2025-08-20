{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.DebugInfo where

import Data.Bits (FiniteBits)
import qualified Data.Bits as Bits
import qualified Data.Ix as Ix
import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Bounded, Enum, Eq, IO, Int, Integral, Num, Ord, Read, Real, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/DebugInfo.h>\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_787cb73f091cb3d3 (void) { return LLVMDebugMetadataVersion(); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_39965e75fd77f081 (LLVMModuleRef arg1) { return LLVMGetModuleDebugMetadataVersion(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_DebugInfo_6fe20a387364257d (LLVMModuleRef arg1) { return LLVMStripModuleDebugInfo(arg1); }\nLLVMDIBuilderRef hs_bindgen_LlvmC_Raw_DebugInfo_c3b2e3431534ebde (LLVMModuleRef arg1) { return LLVMCreateDIBuilderDisallowUnresolved(arg1); }\nLLVMDIBuilderRef hs_bindgen_LlvmC_Raw_DebugInfo_d27fc68c79e3bce5 (LLVMModuleRef arg1) { return LLVMCreateDIBuilder(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_94fd70f0eb56ce04 (LLVMDIBuilderRef arg1) { LLVMDisposeDIBuilder(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_8eff6a872f81e8e3 (LLVMDIBuilderRef arg1) { LLVMDIBuilderFinalize(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_c23f6c1e410907dc (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2) { LLVMDIBuilderFinalizeSubprogram(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_87907e0449733354 (LLVMDIBuilderRef arg1, LLVMDWARFSourceLanguage arg2, LLVMMetadataRef arg3, char *arg4, size_t arg5, LLVMBool arg6, char *arg7, size_t arg8, unsigned int arg9, char *arg10, size_t arg11, LLVMDWARFEmissionKind arg12, unsigned int arg13, LLVMBool arg14, LLVMBool arg15, char *arg16, size_t arg17, char *arg18, size_t arg19) { return LLVMDIBuilderCreateCompileUnit(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16, arg17, arg18, arg19); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_ca8b08b8ff49d2e1 (LLVMDIBuilderRef arg1, char *arg2, size_t arg3, char *arg4, size_t arg5) { return LLVMDIBuilderCreateFile(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_d9e1d3ddc9515f9c (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, char *arg5, size_t arg6, char *arg7, size_t arg8, char *arg9, size_t arg10) { return LLVMDIBuilderCreateModule(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_5db196043eb0213f (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMBool arg5) { return LLVMDIBuilderCreateNameSpace(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_11056e448bdb76da (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, char *arg5, size_t arg6, LLVMMetadataRef arg7, unsigned int arg8, LLVMMetadataRef arg9, LLVMBool arg10, LLVMBool arg11, unsigned int arg12, LLVMDIFlags arg13, LLVMBool arg14) { return LLVMDIBuilderCreateFunction(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b11151275efc0e6c (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, unsigned int arg4, unsigned int arg5) { return LLVMDIBuilderCreateLexicalBlock(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_84eec52e86e42263 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, unsigned int arg4) { return LLVMDIBuilderCreateLexicalBlockFile(arg1, arg2, arg3, arg4); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_9e3837535286d89a (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, unsigned int arg5) { return LLVMDIBuilderCreateImportedModuleFromNamespace(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_322022f5c3f5490d (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, unsigned int arg5, LLVMMetadataRef *arg6, unsigned int arg7) { return LLVMDIBuilderCreateImportedModuleFromAlias(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_279dca4cc47fb9cd (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, unsigned int arg5, LLVMMetadataRef *arg6, unsigned int arg7) { return LLVMDIBuilderCreateImportedModuleFromModule(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_6c8188830565c08c (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, unsigned int arg5, char *arg6, size_t arg7, LLVMMetadataRef *arg8, unsigned int arg9) { return LLVMDIBuilderCreateImportedDeclaration(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_d1ec9832f55f850b (LLVMContextRef arg1, unsigned int arg2, unsigned int arg3, LLVMMetadataRef arg4, LLVMMetadataRef arg5) { return LLVMDIBuilderCreateDebugLocation(arg1, arg2, arg3, arg4, arg5); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_3d6346333c332746 (LLVMMetadataRef arg1) { return LLVMDILocationGetLine(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_3583118e42e6c5ba (LLVMMetadataRef arg1) { return LLVMDILocationGetColumn(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b7ed899618675b7c (LLVMMetadataRef arg1) { return LLVMDILocationGetScope(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_56c2b892cc355271 (LLVMMetadataRef arg1) { return LLVMDILocationGetInlinedAt(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_17ab0c2fef9c4303 (LLVMMetadataRef arg1) { return LLVMDIScopeGetFile(arg1); }\nchar *hs_bindgen_LlvmC_Raw_DebugInfo_c906a19ed3541f7c (LLVMMetadataRef arg1, unsigned int *arg2) { return LLVMDIFileGetDirectory(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_DebugInfo_7642de4e78ea8c21 (LLVMMetadataRef arg1, unsigned int *arg2) { return LLVMDIFileGetFilename(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_DebugInfo_cc56254c0fa8ee80 (LLVMMetadataRef arg1, unsigned int *arg2) { return LLVMDIFileGetSource(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_8afb493c726dce27 (LLVMDIBuilderRef arg1, LLVMMetadataRef *arg2, size_t arg3) { return LLVMDIBuilderGetOrCreateTypeArray(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_87a622a2909f5a81 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef *arg3, unsigned int arg4, LLVMDIFlags arg5) { return LLVMDIBuilderCreateSubroutineType(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_6c45996db8ec3c89 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, unsigned int arg3, LLVMDWARFMacinfoRecordType arg4, char *arg5, size_t arg6, char *arg7, size_t arg8) { return LLVMDIBuilderCreateMacro(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_dec3636f5bd33c57 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, unsigned int arg3, LLVMMetadataRef arg4) { return LLVMDIBuilderCreateTempMacroFile(arg1, arg2, arg3, arg4); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_dce778237ec406b0 (LLVMDIBuilderRef arg1, char *arg2, size_t arg3, int64_t arg4, LLVMBool arg5) { return LLVMDIBuilderCreateEnumerator(arg1, arg2, arg3, arg4, arg5); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_4fda52b814a740fd (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint32_t arg8, LLVMMetadataRef *arg9, unsigned int arg10, LLVMMetadataRef arg11) { return LLVMDIBuilderCreateEnumerationType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_740d2ad91c70cc11 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint32_t arg8, LLVMDIFlags arg9, LLVMMetadataRef *arg10, unsigned int arg11, unsigned int arg12, char *arg13, size_t arg14) { return LLVMDIBuilderCreateUnionType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_8661e01f3dca7a1b (LLVMDIBuilderRef arg1, uint64_t arg2, uint32_t arg3, LLVMMetadataRef arg4, LLVMMetadataRef *arg5, unsigned int arg6) { return LLVMDIBuilderCreateArrayType(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_837bab2ee420af7a (LLVMDIBuilderRef arg1, uint64_t arg2, uint32_t arg3, LLVMMetadataRef arg4, LLVMMetadataRef *arg5, unsigned int arg6) { return LLVMDIBuilderCreateVectorType(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_ed0c285e0b79db80 (LLVMDIBuilderRef arg1, char *arg2, size_t arg3) { return LLVMDIBuilderCreateUnspecifiedType(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_23867aa52822027f (LLVMDIBuilderRef arg1, char *arg2, size_t arg3, uint64_t arg4, LLVMDWARFTypeEncoding arg5, LLVMDIFlags arg6) { return LLVMDIBuilderCreateBasicType(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_1d97ac35ad4fd634 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, uint64_t arg3, uint32_t arg4, unsigned int arg5, char *arg6, size_t arg7) { return LLVMDIBuilderCreatePointerType(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_22304e0781074c67 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint32_t arg8, LLVMDIFlags arg9, LLVMMetadataRef arg10, LLVMMetadataRef *arg11, unsigned int arg12, unsigned int arg13, LLVMMetadataRef arg14, char *arg15, size_t arg16) { return LLVMDIBuilderCreateStructType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_9cf2f4b7abbe7dd8 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint32_t arg8, uint64_t arg9, LLVMDIFlags arg10, LLVMMetadataRef arg11) { return LLVMDIBuilderCreateMemberType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_5ef4e66390a11736 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, LLVMMetadataRef arg7, LLVMDIFlags arg8, LLVMValueRef arg9, uint32_t arg10) { return LLVMDIBuilderCreateStaticMemberType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_d6ea88acdadfb47c (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, uint64_t arg4, uint32_t arg5, LLVMDIFlags arg6) { return LLVMDIBuilderCreateMemberPointerType(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_d56b36d434828ac1 (LLVMDIBuilderRef arg1, char *arg2, size_t arg3, LLVMMetadataRef arg4, unsigned int arg5, uint64_t arg6, uint32_t arg7, uint64_t arg8, LLVMDIFlags arg9, LLVMMetadataRef arg10, LLVMMetadataRef arg11) { return LLVMDIBuilderCreateObjCIVar(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b3a1d90504750aee (LLVMDIBuilderRef arg1, char *arg2, size_t arg3, LLVMMetadataRef arg4, unsigned int arg5, char *arg6, size_t arg7, char *arg8, size_t arg9, unsigned int arg10, LLVMMetadataRef arg11) { return LLVMDIBuilderCreateObjCProperty(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_940e3d0e7645ab26 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2) { return LLVMDIBuilderCreateObjectPointerType(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b4a2b2e1df395677 (LLVMDIBuilderRef arg1, unsigned int arg2, LLVMMetadataRef arg3) { return LLVMDIBuilderCreateQualifiedType(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_3222fdeb16ca2626 (LLVMDIBuilderRef arg1, unsigned int arg2, LLVMMetadataRef arg3) { return LLVMDIBuilderCreateReferenceType(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_f4f2d9c4b2c01b3c (LLVMDIBuilderRef arg1) { return LLVMDIBuilderCreateNullPtrType(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_f47701375da6e977 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, LLVMMetadataRef arg7, uint32_t arg8) { return LLVMDIBuilderCreateTypedef(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_877f579083f04b41 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, LLVMMetadataRef arg3, uint64_t arg4, uint32_t arg5, LLVMDIFlags arg6) { return LLVMDIBuilderCreateInheritance(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_267b52cce1ebb156 (LLVMDIBuilderRef arg1, unsigned int arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, LLVMMetadataRef arg6, unsigned int arg7, unsigned int arg8, uint64_t arg9, uint32_t arg10, char *arg11, size_t arg12) { return LLVMDIBuilderCreateForwardDecl(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_2d792ef07748cdea (LLVMDIBuilderRef arg1, unsigned int arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, LLVMMetadataRef arg6, unsigned int arg7, unsigned int arg8, uint64_t arg9, uint32_t arg10, LLVMDIFlags arg11, char *arg12, size_t arg13) { return LLVMDIBuilderCreateReplaceableCompositeType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_807c01a6073ffbbe (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint64_t arg8, uint64_t arg9, LLVMDIFlags arg10, LLVMMetadataRef arg11) { return LLVMDIBuilderCreateBitFieldMemberType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_fec6334f3451d2b9 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, uint64_t arg7, uint32_t arg8, uint64_t arg9, LLVMDIFlags arg10, LLVMMetadataRef arg11, LLVMMetadataRef *arg12, unsigned int arg13, LLVMMetadataRef arg14, LLVMMetadataRef arg15, char *arg16, size_t arg17) { return LLVMDIBuilderCreateClassType(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13, arg14, arg15, arg16, arg17); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_59745ccf5ab9a7bf (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2) { return LLVMDIBuilderCreateArtificialType(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_DebugInfo_8c540601760e4eed (LLVMMetadataRef arg1, size_t *arg2) { return LLVMDITypeGetName(arg1, arg2); }\nuint64_t hs_bindgen_LlvmC_Raw_DebugInfo_c47eb4840e5bc1e1 (LLVMMetadataRef arg1) { return LLVMDITypeGetSizeInBits(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_DebugInfo_117343359f8230d2 (LLVMMetadataRef arg1) { return LLVMDITypeGetOffsetInBits(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_DebugInfo_aec93364237481ff (LLVMMetadataRef arg1) { return LLVMDITypeGetAlignInBits(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_3e9cffe90f482848 (LLVMMetadataRef arg1) { return LLVMDITypeGetLine(arg1); }\nLLVMDIFlags hs_bindgen_LlvmC_Raw_DebugInfo_1d0d51894b6751d8 (LLVMMetadataRef arg1) { return LLVMDITypeGetFlags(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_af03b4fa27044bed (LLVMDIBuilderRef arg1, int64_t arg2, int64_t arg3) { return LLVMDIBuilderGetOrCreateSubrange(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_10de1a021de1f4fc (LLVMDIBuilderRef arg1, LLVMMetadataRef *arg2, size_t arg3) { return LLVMDIBuilderGetOrCreateArray(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_6f27662faba44436 (LLVMDIBuilderRef arg1, uint64_t *arg2, size_t arg3) { return LLVMDIBuilderCreateExpression(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_5af35a1d710c1454 (LLVMDIBuilderRef arg1, uint64_t arg2) { return LLVMDIBuilderCreateConstantValueExpression(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_6a6a85cb32df431c (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, char *arg5, size_t arg6, LLVMMetadataRef arg7, unsigned int arg8, LLVMMetadataRef arg9, LLVMBool arg10, LLVMMetadataRef arg11, LLVMMetadataRef arg12, uint32_t arg13) { return LLVMDIBuilderCreateGlobalVariableExpression(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12, arg13); }\nuint16_t hs_bindgen_LlvmC_Raw_DebugInfo_af36162e136daea5 (LLVMMetadataRef arg1) { return LLVMGetDINodeTag(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_9231cbac798c279d (LLVMMetadataRef arg1) { return LLVMDIGlobalVariableExpressionGetVariable(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_14474716f47560e9 (LLVMMetadataRef arg1) { return LLVMDIGlobalVariableExpressionGetExpression(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_9f0273cbf2b99834 (LLVMMetadataRef arg1) { return LLVMDIVariableGetFile(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b7f722c9f60b7bc7 (LLVMMetadataRef arg1) { return LLVMDIVariableGetScope(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_eb3f151da8829447 (LLVMMetadataRef arg1) { return LLVMDIVariableGetLine(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_75927bb6e41253ce (LLVMContextRef arg1, LLVMMetadataRef *arg2, size_t arg3) { return LLVMTemporaryMDNode(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_51240435f56e93ad (LLVMMetadataRef arg1) { LLVMDisposeTemporaryMDNode(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_79ba16a1007a76a1 (LLVMMetadataRef arg1, LLVMMetadataRef arg2) { LLVMMetadataReplaceAllUsesWith(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_14d7b98648c79a23 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, char *arg5, size_t arg6, LLVMMetadataRef arg7, unsigned int arg8, LLVMMetadataRef arg9, LLVMBool arg10, LLVMMetadataRef arg11, uint32_t arg12) { return LLVMDIBuilderCreateTempGlobalVariableFwdDecl(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11, arg12); }\nLLVMDbgRecordRef hs_bindgen_LlvmC_Raw_DebugInfo_060c9789b2099755 (LLVMDIBuilderRef arg1, LLVMValueRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, LLVMMetadataRef arg5, LLVMValueRef arg6) { return LLVMDIBuilderInsertDeclareRecordBefore(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMDbgRecordRef hs_bindgen_LlvmC_Raw_DebugInfo_434e7771f3f70cc2 (LLVMDIBuilderRef arg1, LLVMValueRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, LLVMMetadataRef arg5, LLVMBasicBlockRef arg6) { return LLVMDIBuilderInsertDeclareRecordAtEnd(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMDbgRecordRef hs_bindgen_LlvmC_Raw_DebugInfo_102f9fd605fac304 (LLVMDIBuilderRef arg1, LLVMValueRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, LLVMMetadataRef arg5, LLVMValueRef arg6) { return LLVMDIBuilderInsertDbgValueRecordBefore(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMDbgRecordRef hs_bindgen_LlvmC_Raw_DebugInfo_414842503b14ea27 (LLVMDIBuilderRef arg1, LLVMValueRef arg2, LLVMMetadataRef arg3, LLVMMetadataRef arg4, LLVMMetadataRef arg5, LLVMBasicBlockRef arg6) { return LLVMDIBuilderInsertDbgValueRecordAtEnd(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_bfaa0c781d1646c8 (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5, unsigned int arg6, LLVMMetadataRef arg7, LLVMBool arg8, LLVMDIFlags arg9, uint32_t arg10) { return LLVMDIBuilderCreateAutoVariable(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_b8b550d5bd22b91a (LLVMDIBuilderRef arg1, LLVMMetadataRef arg2, char *arg3, size_t arg4, unsigned int arg5, LLVMMetadataRef arg6, unsigned int arg7, LLVMMetadataRef arg8, LLVMBool arg9, LLVMDIFlags arg10) { return LLVMDIBuilderCreateParameterVariable(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_7f536a0ca9acd316 (LLVMValueRef arg1) { return LLVMGetSubprogram(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_f58c1aaff3446ea6 (LLVMValueRef arg1, LLVMMetadataRef arg2) { LLVMSetSubprogram(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_DebugInfo_e8a868b63de238ad (LLVMMetadataRef arg1) { return LLVMDISubprogramGetLine(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_DebugInfo_82097bdfa33ada6b (LLVMValueRef arg1) { return LLVMInstructionGetDebugLoc(arg1); }\nvoid hs_bindgen_LlvmC_Raw_DebugInfo_b258290996a2cb3e (LLVMValueRef arg1, LLVMMetadataRef arg2) { LLVMInstructionSetDebugLoc(arg1, arg2); }\nLLVMMetadataKind hs_bindgen_LlvmC_Raw_DebugInfo_6f0f718bc7677368 (LLVMMetadataRef arg1) { return LLVMGetMetadataKind(arg1); }\n")

newtype DIFlags = DIFlags
  { un_DIFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DIFlags where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DIFlags
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DIFlags un_DIFlags2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DIFlags2

instance HsBindgen.Runtime.CEnum.CEnum DIFlags where

  type CEnumZ DIFlags = FC.CUInt

  toCEnum = DIFlags

  fromCEnum = un_DIFlags

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DIFlagZero")
                                                     , (1, Data.List.NonEmpty.singleton "DIFlagPrivate")
                                                     , (2, Data.List.NonEmpty.singleton "DIFlagProtected")
                                                     , (3, ("DIFlagPublic" Data.List.NonEmpty.:| ["DIFlagAccessibility"]))
                                                     , (4, Data.List.NonEmpty.singleton "DIFlagFwdDecl")
                                                     , (8, Data.List.NonEmpty.singleton "DIFlagAppleBlock")
                                                     , (16, Data.List.NonEmpty.singleton "DIFlagReservedBit4")
                                                     , (32, Data.List.NonEmpty.singleton "DIFlagVirtual")
                                                     , (36, Data.List.NonEmpty.singleton "DIFlagIndirectVirtualBase")
                                                     , (64, Data.List.NonEmpty.singleton "DIFlagArtificial")
                                                     , (128, Data.List.NonEmpty.singleton "DIFlagExplicit")
                                                     , (256, Data.List.NonEmpty.singleton "DIFlagPrototyped")
                                                     , (512, Data.List.NonEmpty.singleton "DIFlagObjcClassComplete")
                                                     , (1024, Data.List.NonEmpty.singleton "DIFlagObjectPointer")
                                                     , (2048, Data.List.NonEmpty.singleton "DIFlagVector")
                                                     , (4096, Data.List.NonEmpty.singleton "DIFlagStaticMember")
                                                     , (8192, Data.List.NonEmpty.singleton "DIFlagLValueReference")
                                                     , (16384, Data.List.NonEmpty.singleton "DIFlagRValueReference")
                                                     , (32768, Data.List.NonEmpty.singleton "DIFlagReserved")
                                                     , (65536, Data.List.NonEmpty.singleton "DIFlagSingleInheritance")
                                                     , (131072, Data.List.NonEmpty.singleton "DIFlagMultipleInheritance")
                                                     , ( 196608
                                                       , ("DIFlagVirtualInheritance" Data.List.NonEmpty.:| ["DIFlagPtrToMemberRep"])
                                                       )
                                                     , (262144, Data.List.NonEmpty.singleton "DIFlagIntroducedVirtual")
                                                     , (524288, Data.List.NonEmpty.singleton "DIFlagBitField")
                                                     , (1048576, Data.List.NonEmpty.singleton "DIFlagNoReturn")
                                                     , (4194304, Data.List.NonEmpty.singleton "DIFlagTypePassByValue")
                                                     , (8388608, Data.List.NonEmpty.singleton "DIFlagTypePassByReference")
                                                     , (16777216, ("DIFlagEnumClass" Data.List.NonEmpty.:| ["DIFlagFixedEnum"]))
                                                     , (33554432, Data.List.NonEmpty.singleton "DIFlagThunk")
                                                     , (67108864, Data.List.NonEmpty.singleton "DIFlagNonTrivial")
                                                     , (134217728, Data.List.NonEmpty.singleton "DIFlagBigEndian")
                                                     , (268435456, Data.List.NonEmpty.singleton "DIFlagLittleEndian")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DIFlags"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DIFlags"

instance Show DIFlags where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DIFlags where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DIFlagZero :: DIFlags
pattern DIFlagZero = DIFlags 0

pattern DIFlagPrivate :: DIFlags
pattern DIFlagPrivate = DIFlags 1

pattern DIFlagProtected :: DIFlags
pattern DIFlagProtected = DIFlags 2

pattern DIFlagPublic :: DIFlags
pattern DIFlagPublic = DIFlags 3

pattern DIFlagFwdDecl :: DIFlags
pattern DIFlagFwdDecl = DIFlags 4

pattern DIFlagAppleBlock :: DIFlags
pattern DIFlagAppleBlock = DIFlags 8

pattern DIFlagReservedBit4 :: DIFlags
pattern DIFlagReservedBit4 = DIFlags 16

pattern DIFlagVirtual :: DIFlags
pattern DIFlagVirtual = DIFlags 32

pattern DIFlagArtificial :: DIFlags
pattern DIFlagArtificial = DIFlags 64

pattern DIFlagExplicit :: DIFlags
pattern DIFlagExplicit = DIFlags 128

pattern DIFlagPrototyped :: DIFlags
pattern DIFlagPrototyped = DIFlags 256

pattern DIFlagObjcClassComplete :: DIFlags
pattern DIFlagObjcClassComplete = DIFlags 512

pattern DIFlagObjectPointer :: DIFlags
pattern DIFlagObjectPointer = DIFlags 1024

pattern DIFlagVector :: DIFlags
pattern DIFlagVector = DIFlags 2048

pattern DIFlagStaticMember :: DIFlags
pattern DIFlagStaticMember = DIFlags 4096

pattern DIFlagLValueReference :: DIFlags
pattern DIFlagLValueReference = DIFlags 8192

pattern DIFlagRValueReference :: DIFlags
pattern DIFlagRValueReference = DIFlags 16384

pattern DIFlagReserved :: DIFlags
pattern DIFlagReserved = DIFlags 32768

pattern DIFlagSingleInheritance :: DIFlags
pattern DIFlagSingleInheritance = DIFlags 65536

pattern DIFlagMultipleInheritance :: DIFlags
pattern DIFlagMultipleInheritance = DIFlags 131072

pattern DIFlagVirtualInheritance :: DIFlags
pattern DIFlagVirtualInheritance = DIFlags 196608

pattern DIFlagIntroducedVirtual :: DIFlags
pattern DIFlagIntroducedVirtual = DIFlags 262144

pattern DIFlagBitField :: DIFlags
pattern DIFlagBitField = DIFlags 524288

pattern DIFlagNoReturn :: DIFlags
pattern DIFlagNoReturn = DIFlags 1048576

pattern DIFlagTypePassByValue :: DIFlags
pattern DIFlagTypePassByValue = DIFlags 4194304

pattern DIFlagTypePassByReference :: DIFlags
pattern DIFlagTypePassByReference = DIFlags 8388608

pattern DIFlagEnumClass :: DIFlags
pattern DIFlagEnumClass = DIFlags 16777216

pattern DIFlagFixedEnum :: DIFlags
pattern DIFlagFixedEnum = DIFlags 16777216

pattern DIFlagThunk :: DIFlags
pattern DIFlagThunk = DIFlags 33554432

pattern DIFlagNonTrivial :: DIFlags
pattern DIFlagNonTrivial = DIFlags 67108864

pattern DIFlagBigEndian :: DIFlags
pattern DIFlagBigEndian = DIFlags 134217728

pattern DIFlagLittleEndian :: DIFlags
pattern DIFlagLittleEndian = DIFlags 268435456

pattern DIFlagIndirectVirtualBase :: DIFlags
pattern DIFlagIndirectVirtualBase = DIFlags 36

pattern DIFlagAccessibility :: DIFlags
pattern DIFlagAccessibility = DIFlags 3

pattern DIFlagPtrToMemberRep :: DIFlags
pattern DIFlagPtrToMemberRep = DIFlags 196608

newtype DWARFSourceLanguage = DWARFSourceLanguage
  { un_DWARFSourceLanguage :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DWARFSourceLanguage where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DWARFSourceLanguage
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DWARFSourceLanguage un_DWARFSourceLanguage2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DWARFSourceLanguage2

instance HsBindgen.Runtime.CEnum.CEnum DWARFSourceLanguage where

  type CEnumZ DWARFSourceLanguage = FC.CUInt

  toCEnum = DWARFSourceLanguage

  fromCEnum = un_DWARFSourceLanguage

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DWARFSourceLanguageC89")
                                                     , (1, Data.List.NonEmpty.singleton "DWARFSourceLanguageC")
                                                     , (2, Data.List.NonEmpty.singleton "DWARFSourceLanguageAda83")
                                                     , (3, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus")
                                                     , (4, Data.List.NonEmpty.singleton "DWARFSourceLanguageCobol74")
                                                     , (5, Data.List.NonEmpty.singleton "DWARFSourceLanguageCobol85")
                                                     , (6, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran77")
                                                     , (7, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran90")
                                                     , (8, Data.List.NonEmpty.singleton "DWARFSourceLanguagePascal83")
                                                     , (9, Data.List.NonEmpty.singleton "DWARFSourceLanguageModula2")
                                                     , (10, Data.List.NonEmpty.singleton "DWARFSourceLanguageJava")
                                                     , (11, Data.List.NonEmpty.singleton "DWARFSourceLanguageC99")
                                                     , (12, Data.List.NonEmpty.singleton "DWARFSourceLanguageAda95")
                                                     , (13, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran95")
                                                     , (14, Data.List.NonEmpty.singleton "DWARFSourceLanguagePLI")
                                                     , (15, Data.List.NonEmpty.singleton "DWARFSourceLanguageObjC")
                                                     , (16, Data.List.NonEmpty.singleton "DWARFSourceLanguageObjC_plus_plus")
                                                     , (17, Data.List.NonEmpty.singleton "DWARFSourceLanguageUPC")
                                                     , (18, Data.List.NonEmpty.singleton "DWARFSourceLanguageD")
                                                     , (19, Data.List.NonEmpty.singleton "DWARFSourceLanguagePython")
                                                     , (20, Data.List.NonEmpty.singleton "DWARFSourceLanguageOpenCL")
                                                     , (21, Data.List.NonEmpty.singleton "DWARFSourceLanguageGo")
                                                     , (22, Data.List.NonEmpty.singleton "DWARFSourceLanguageModula3")
                                                     , (23, Data.List.NonEmpty.singleton "DWARFSourceLanguageHaskell")
                                                     , (24, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus_03")
                                                     , (25, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus_11")
                                                     , (26, Data.List.NonEmpty.singleton "DWARFSourceLanguageOCaml")
                                                     , (27, Data.List.NonEmpty.singleton "DWARFSourceLanguageRust")
                                                     , (28, Data.List.NonEmpty.singleton "DWARFSourceLanguageC11")
                                                     , (29, Data.List.NonEmpty.singleton "DWARFSourceLanguageSwift")
                                                     , (30, Data.List.NonEmpty.singleton "DWARFSourceLanguageJulia")
                                                     , (31, Data.List.NonEmpty.singleton "DWARFSourceLanguageDylan")
                                                     , (32, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus_14")
                                                     , (33, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran03")
                                                     , (34, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran08")
                                                     , (35, Data.List.NonEmpty.singleton "DWARFSourceLanguageRenderScript")
                                                     , (36, Data.List.NonEmpty.singleton "DWARFSourceLanguageBLISS")
                                                     , (37, Data.List.NonEmpty.singleton "DWARFSourceLanguageKotlin")
                                                     , (38, Data.List.NonEmpty.singleton "DWARFSourceLanguageZig")
                                                     , (39, Data.List.NonEmpty.singleton "DWARFSourceLanguageCrystal")
                                                     , (40, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus_17")
                                                     , (41, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_plus_plus_20")
                                                     , (42, Data.List.NonEmpty.singleton "DWARFSourceLanguageC17")
                                                     , (43, Data.List.NonEmpty.singleton "DWARFSourceLanguageFortran18")
                                                     , (44, Data.List.NonEmpty.singleton "DWARFSourceLanguageAda2005")
                                                     , (45, Data.List.NonEmpty.singleton "DWARFSourceLanguageAda2012")
                                                     , (46, Data.List.NonEmpty.singleton "DWARFSourceLanguageHIP")
                                                     , (47, Data.List.NonEmpty.singleton "DWARFSourceLanguageAssembly")
                                                     , (48, Data.List.NonEmpty.singleton "DWARFSourceLanguageC_sharp")
                                                     , (49, Data.List.NonEmpty.singleton "DWARFSourceLanguageMojo")
                                                     , (50, Data.List.NonEmpty.singleton "DWARFSourceLanguageGLSL")
                                                     , (51, Data.List.NonEmpty.singleton "DWARFSourceLanguageGLSL_ES")
                                                     , (52, Data.List.NonEmpty.singleton "DWARFSourceLanguageHLSL")
                                                     , (53, Data.List.NonEmpty.singleton "DWARFSourceLanguageOpenCL_CPP")
                                                     , (54, Data.List.NonEmpty.singleton "DWARFSourceLanguageCPP_for_OpenCL")
                                                     , (55, Data.List.NonEmpty.singleton "DWARFSourceLanguageSYCL")
                                                     , (56, Data.List.NonEmpty.singleton "DWARFSourceLanguageRuby")
                                                     , (57, Data.List.NonEmpty.singleton "DWARFSourceLanguageMove")
                                                     , (58, Data.List.NonEmpty.singleton "DWARFSourceLanguageHylo")
                                                     , (59, Data.List.NonEmpty.singleton "DWARFSourceLanguageMips_Assembler")
                                                     , (60, Data.List.NonEmpty.singleton "DWARFSourceLanguageGOOGLE_RenderScript")
                                                     , (61, Data.List.NonEmpty.singleton "DWARFSourceLanguageBORLAND_Delphi")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DWARFSourceLanguage"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DWARFSourceLanguage"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum DWARFSourceLanguage where

  minDeclaredValue = DWARFSourceLanguageC89

  maxDeclaredValue = DWARFSourceLanguageBORLAND_Delphi

instance Show DWARFSourceLanguage where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DWARFSourceLanguage where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DWARFSourceLanguageC89 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC89 = DWARFSourceLanguage 0

pattern DWARFSourceLanguageC :: DWARFSourceLanguage
pattern DWARFSourceLanguageC = DWARFSourceLanguage 1

pattern DWARFSourceLanguageAda83 :: DWARFSourceLanguage
pattern DWARFSourceLanguageAda83 = DWARFSourceLanguage 2

pattern DWARFSourceLanguageC_plus_plus :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus = DWARFSourceLanguage 3

pattern DWARFSourceLanguageCobol74 :: DWARFSourceLanguage
pattern DWARFSourceLanguageCobol74 = DWARFSourceLanguage 4

pattern DWARFSourceLanguageCobol85 :: DWARFSourceLanguage
pattern DWARFSourceLanguageCobol85 = DWARFSourceLanguage 5

pattern DWARFSourceLanguageFortran77 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran77 = DWARFSourceLanguage 6

pattern DWARFSourceLanguageFortran90 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran90 = DWARFSourceLanguage 7

pattern DWARFSourceLanguagePascal83 :: DWARFSourceLanguage
pattern DWARFSourceLanguagePascal83 = DWARFSourceLanguage 8

pattern DWARFSourceLanguageModula2 :: DWARFSourceLanguage
pattern DWARFSourceLanguageModula2 = DWARFSourceLanguage 9

pattern DWARFSourceLanguageJava :: DWARFSourceLanguage
pattern DWARFSourceLanguageJava = DWARFSourceLanguage 10

pattern DWARFSourceLanguageC99 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC99 = DWARFSourceLanguage 11

pattern DWARFSourceLanguageAda95 :: DWARFSourceLanguage
pattern DWARFSourceLanguageAda95 = DWARFSourceLanguage 12

pattern DWARFSourceLanguageFortran95 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran95 = DWARFSourceLanguage 13

pattern DWARFSourceLanguagePLI :: DWARFSourceLanguage
pattern DWARFSourceLanguagePLI = DWARFSourceLanguage 14

pattern DWARFSourceLanguageObjC :: DWARFSourceLanguage
pattern DWARFSourceLanguageObjC = DWARFSourceLanguage 15

pattern DWARFSourceLanguageObjC_plus_plus :: DWARFSourceLanguage
pattern DWARFSourceLanguageObjC_plus_plus = DWARFSourceLanguage 16

pattern DWARFSourceLanguageUPC :: DWARFSourceLanguage
pattern DWARFSourceLanguageUPC = DWARFSourceLanguage 17

pattern DWARFSourceLanguageD :: DWARFSourceLanguage
pattern DWARFSourceLanguageD = DWARFSourceLanguage 18

pattern DWARFSourceLanguagePython :: DWARFSourceLanguage
pattern DWARFSourceLanguagePython = DWARFSourceLanguage 19

pattern DWARFSourceLanguageOpenCL :: DWARFSourceLanguage
pattern DWARFSourceLanguageOpenCL = DWARFSourceLanguage 20

pattern DWARFSourceLanguageGo :: DWARFSourceLanguage
pattern DWARFSourceLanguageGo = DWARFSourceLanguage 21

pattern DWARFSourceLanguageModula3 :: DWARFSourceLanguage
pattern DWARFSourceLanguageModula3 = DWARFSourceLanguage 22

pattern DWARFSourceLanguageHaskell :: DWARFSourceLanguage
pattern DWARFSourceLanguageHaskell = DWARFSourceLanguage 23

pattern DWARFSourceLanguageC_plus_plus_03 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus_03 = DWARFSourceLanguage 24

pattern DWARFSourceLanguageC_plus_plus_11 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus_11 = DWARFSourceLanguage 25

pattern DWARFSourceLanguageOCaml :: DWARFSourceLanguage
pattern DWARFSourceLanguageOCaml = DWARFSourceLanguage 26

pattern DWARFSourceLanguageRust :: DWARFSourceLanguage
pattern DWARFSourceLanguageRust = DWARFSourceLanguage 27

pattern DWARFSourceLanguageC11 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC11 = DWARFSourceLanguage 28

pattern DWARFSourceLanguageSwift :: DWARFSourceLanguage
pattern DWARFSourceLanguageSwift = DWARFSourceLanguage 29

pattern DWARFSourceLanguageJulia :: DWARFSourceLanguage
pattern DWARFSourceLanguageJulia = DWARFSourceLanguage 30

pattern DWARFSourceLanguageDylan :: DWARFSourceLanguage
pattern DWARFSourceLanguageDylan = DWARFSourceLanguage 31

pattern DWARFSourceLanguageC_plus_plus_14 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus_14 = DWARFSourceLanguage 32

pattern DWARFSourceLanguageFortran03 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran03 = DWARFSourceLanguage 33

pattern DWARFSourceLanguageFortran08 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran08 = DWARFSourceLanguage 34

pattern DWARFSourceLanguageRenderScript :: DWARFSourceLanguage
pattern DWARFSourceLanguageRenderScript = DWARFSourceLanguage 35

pattern DWARFSourceLanguageBLISS :: DWARFSourceLanguage
pattern DWARFSourceLanguageBLISS = DWARFSourceLanguage 36

pattern DWARFSourceLanguageKotlin :: DWARFSourceLanguage
pattern DWARFSourceLanguageKotlin = DWARFSourceLanguage 37

pattern DWARFSourceLanguageZig :: DWARFSourceLanguage
pattern DWARFSourceLanguageZig = DWARFSourceLanguage 38

pattern DWARFSourceLanguageCrystal :: DWARFSourceLanguage
pattern DWARFSourceLanguageCrystal = DWARFSourceLanguage 39

pattern DWARFSourceLanguageC_plus_plus_17 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus_17 = DWARFSourceLanguage 40

pattern DWARFSourceLanguageC_plus_plus_20 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_plus_plus_20 = DWARFSourceLanguage 41

pattern DWARFSourceLanguageC17 :: DWARFSourceLanguage
pattern DWARFSourceLanguageC17 = DWARFSourceLanguage 42

pattern DWARFSourceLanguageFortran18 :: DWARFSourceLanguage
pattern DWARFSourceLanguageFortran18 = DWARFSourceLanguage 43

pattern DWARFSourceLanguageAda2005 :: DWARFSourceLanguage
pattern DWARFSourceLanguageAda2005 = DWARFSourceLanguage 44

pattern DWARFSourceLanguageAda2012 :: DWARFSourceLanguage
pattern DWARFSourceLanguageAda2012 = DWARFSourceLanguage 45

pattern DWARFSourceLanguageHIP :: DWARFSourceLanguage
pattern DWARFSourceLanguageHIP = DWARFSourceLanguage 46

pattern DWARFSourceLanguageAssembly :: DWARFSourceLanguage
pattern DWARFSourceLanguageAssembly = DWARFSourceLanguage 47

pattern DWARFSourceLanguageC_sharp :: DWARFSourceLanguage
pattern DWARFSourceLanguageC_sharp = DWARFSourceLanguage 48

pattern DWARFSourceLanguageMojo :: DWARFSourceLanguage
pattern DWARFSourceLanguageMojo = DWARFSourceLanguage 49

pattern DWARFSourceLanguageGLSL :: DWARFSourceLanguage
pattern DWARFSourceLanguageGLSL = DWARFSourceLanguage 50

pattern DWARFSourceLanguageGLSL_ES :: DWARFSourceLanguage
pattern DWARFSourceLanguageGLSL_ES = DWARFSourceLanguage 51

pattern DWARFSourceLanguageHLSL :: DWARFSourceLanguage
pattern DWARFSourceLanguageHLSL = DWARFSourceLanguage 52

pattern DWARFSourceLanguageOpenCL_CPP :: DWARFSourceLanguage
pattern DWARFSourceLanguageOpenCL_CPP = DWARFSourceLanguage 53

pattern DWARFSourceLanguageCPP_for_OpenCL :: DWARFSourceLanguage
pattern DWARFSourceLanguageCPP_for_OpenCL = DWARFSourceLanguage 54

pattern DWARFSourceLanguageSYCL :: DWARFSourceLanguage
pattern DWARFSourceLanguageSYCL = DWARFSourceLanguage 55

pattern DWARFSourceLanguageRuby :: DWARFSourceLanguage
pattern DWARFSourceLanguageRuby = DWARFSourceLanguage 56

pattern DWARFSourceLanguageMove :: DWARFSourceLanguage
pattern DWARFSourceLanguageMove = DWARFSourceLanguage 57

pattern DWARFSourceLanguageHylo :: DWARFSourceLanguage
pattern DWARFSourceLanguageHylo = DWARFSourceLanguage 58

pattern DWARFSourceLanguageMips_Assembler :: DWARFSourceLanguage
pattern DWARFSourceLanguageMips_Assembler = DWARFSourceLanguage 59

pattern DWARFSourceLanguageGOOGLE_RenderScript :: DWARFSourceLanguage
pattern DWARFSourceLanguageGOOGLE_RenderScript = DWARFSourceLanguage 60

pattern DWARFSourceLanguageBORLAND_Delphi :: DWARFSourceLanguage
pattern DWARFSourceLanguageBORLAND_Delphi = DWARFSourceLanguage 61

newtype DWARFEmissionKind = DWARFEmissionKind
  { un_DWARFEmissionKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DWARFEmissionKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DWARFEmissionKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DWARFEmissionKind un_DWARFEmissionKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DWARFEmissionKind2

instance HsBindgen.Runtime.CEnum.CEnum DWARFEmissionKind where

  type CEnumZ DWARFEmissionKind = FC.CUInt

  toCEnum = DWARFEmissionKind

  fromCEnum = un_DWARFEmissionKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DWARFEmissionNone")
                                                     , (1, Data.List.NonEmpty.singleton "DWARFEmissionFull")
                                                     , (2, Data.List.NonEmpty.singleton "DWARFEmissionLineTablesOnly")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DWARFEmissionKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DWARFEmissionKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum DWARFEmissionKind where

  minDeclaredValue = DWARFEmissionNone

  maxDeclaredValue = DWARFEmissionLineTablesOnly

instance Show DWARFEmissionKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DWARFEmissionKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DWARFEmissionNone :: DWARFEmissionKind
pattern DWARFEmissionNone = DWARFEmissionKind 0

pattern DWARFEmissionFull :: DWARFEmissionKind
pattern DWARFEmissionFull = DWARFEmissionKind 1

pattern DWARFEmissionLineTablesOnly :: DWARFEmissionKind
pattern DWARFEmissionLineTablesOnly = DWARFEmissionKind 2

newtype MetadataKind = MetadataKind
  { un_MetadataKind :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype DWARFTypeEncoding = DWARFTypeEncoding
  { un_DWARFTypeEncoding :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype DWARFMacinfoRecordType = DWARFMacinfoRecordType
  { un_DWARFMacinfoRecordType :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DWARFMacinfoRecordType where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DWARFMacinfoRecordType
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DWARFMacinfoRecordType un_DWARFMacinfoRecordType2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DWARFMacinfoRecordType2

instance HsBindgen.Runtime.CEnum.CEnum DWARFMacinfoRecordType where

  type CEnumZ DWARFMacinfoRecordType = FC.CUInt

  toCEnum = DWARFMacinfoRecordType

  fromCEnum = un_DWARFMacinfoRecordType

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (1, Data.List.NonEmpty.singleton "DWARFMacinfoRecordTypeDefine")
                                                     , (2, Data.List.NonEmpty.singleton "DWARFMacinfoRecordTypeMacro")
                                                     , (3, Data.List.NonEmpty.singleton "DWARFMacinfoRecordTypeStartFile")
                                                     , (4, Data.List.NonEmpty.singleton "DWARFMacinfoRecordTypeEndFile")
                                                     , (255, Data.List.NonEmpty.singleton "DWARFMacinfoRecordTypeVendorExt")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DWARFMacinfoRecordType"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DWARFMacinfoRecordType"

instance Show DWARFMacinfoRecordType where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DWARFMacinfoRecordType where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DWARFMacinfoRecordTypeDefine :: DWARFMacinfoRecordType
pattern DWARFMacinfoRecordTypeDefine = DWARFMacinfoRecordType 1

pattern DWARFMacinfoRecordTypeMacro :: DWARFMacinfoRecordType
pattern DWARFMacinfoRecordTypeMacro = DWARFMacinfoRecordType 2

pattern DWARFMacinfoRecordTypeStartFile :: DWARFMacinfoRecordType
pattern DWARFMacinfoRecordTypeStartFile = DWARFMacinfoRecordType 3

pattern DWARFMacinfoRecordTypeEndFile :: DWARFMacinfoRecordType
pattern DWARFMacinfoRecordTypeEndFile = DWARFMacinfoRecordType 4

pattern DWARFMacinfoRecordTypeVendorExt :: DWARFMacinfoRecordType
pattern DWARFMacinfoRecordTypeVendorExt = DWARFMacinfoRecordType 255

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_787cb73f091cb3d3" debugMetadataVersion
  :: IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_39965e75fd77f081" getModuleDebugMetadataVersion
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @module'@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6fe20a387364257d" stripModuleDebugInfo
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @module'@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_c3b2e3431534ebde" createDIBuilderDisallowUnresolved
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.DIBuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_d27fc68c79e3bce5" createDIBuilder
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.DIBuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_94fd70f0eb56ce04" disposeDIBuilder
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_8eff6a872f81e8e3" dIBuilderFinalize
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_c23f6c1e410907dc" dIBuilderFinalizeSubprogram
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @subprogram@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_87907e0449733354" dIBuilderCreateCompileUnit
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> DWARFSourceLanguage
     {- ^ __from C:__ @lang@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @fileRef@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @producer@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @producerLen@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isOptimized@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @flags@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @flagsLen@ -}
  -> FC.CUInt
     {- ^ __from C:__ @runtimeVer@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @splitName@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @splitNameLen@ -}
  -> DWARFEmissionKind
     {- ^ __from C:__ @kind@ -}
  -> FC.CUInt
     {- ^ __from C:__ @dWOId@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @splitDebugInlining@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @debugInfoForProfiling@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @sysRoot@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sysRootLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @sDK@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sDKLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_ca8b08b8ff49d2e1" dIBuilderCreateFile
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @filename@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @filenameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @directory@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @directoryLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_d9e1d3ddc9515f9c" dIBuilderCreateModule
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @parentScope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @configMacros@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @configMacrosLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @includePath@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @includePathLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @aPINotesFile@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @aPINotesFileLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_5db196043eb0213f" dIBuilderCreateNameSpace
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @parentScope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @exportSymbols@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_11056e448bdb76da" dIBuilderCreateFunction
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @linkageName@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @linkageNameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isLocalToUnit@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isDefinition@ -}
  -> FC.CUInt
     {- ^ __from C:__ @scopeLine@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isOptimized@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b11151275efc0e6c" dIBuilderCreateLexicalBlock
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> FC.CUInt
     {- ^ __from C:__ @column@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_84eec52e86e42263" dIBuilderCreateLexicalBlockFile
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @discriminator@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_9e3837535286d89a" dIBuilderCreateImportedModuleFromNamespace
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @nS@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_322022f5c3f5490d" dIBuilderCreateImportedModuleFromAlias
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @importedEntity@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_279dca4cc47fb9cd" dIBuilderCreateImportedModuleFromModule
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @m@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6c8188830565c08c" dIBuilderCreateImportedDeclaration
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @decl@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_d1ec9832f55f850b" dIBuilderCreateDebugLocation
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @ctx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> FC.CUInt
     {- ^ __from C:__ @column@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @inlinedAt@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_3d6346333c332746" dILocationGetLine
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @location@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_3583118e42e6c5ba" dILocationGetColumn
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @location@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b7ed899618675b7c" dILocationGetScope
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @location@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_56c2b892cc355271" dILocationGetInlinedAt
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @location@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_17ab0c2fef9c4303" dIScopeGetFile
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_c906a19ed3541f7c" dIFileGetDirectory
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_7642de4e78ea8c21" dIFileGetFilename
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_cc56254c0fa8ee80" dIFileGetSource
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_8afb493c726dce27" dIBuilderGetOrCreateTypeArray
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @data'@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_87a622a2909f5a81" dIBuilderCreateSubroutineType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @parameterTypes@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numParameterTypes@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6c45996db8ec3c89" dIBuilderCreateMacro
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @parentMacroFile@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> DWARFMacinfoRecordType
     {- ^ __from C:__ @recordType@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @value@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @valueLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_dec3636f5bd33c57" dIBuilderCreateTempMacroFile
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @parentMacroFile@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_dce778237ec406b0" dIBuilderCreateEnumerator
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> HsBindgen.Runtime.Prelude.Int64
     {- ^ __from C:__ @value@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isUnsigned@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_4fda52b814a740fd" dIBuilderCreateEnumerationType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @classTy@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_740d2ad91c70cc11" dIBuilderCreateUnionType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @runTimeLang@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @uniqueId@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @uniqueIdLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_8661e01f3dca7a1b" dIBuilderCreateArrayType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @size@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @subscripts@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numSubscripts@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_837bab2ee420af7a" dIBuilderCreateVectorType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @size@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @subscripts@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numSubscripts@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_ed0c285e0b79db80" dIBuilderCreateUnspecifiedType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_23867aa52822027f" dIBuilderCreateBasicType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> DWARFTypeEncoding
     {- ^ __from C:__ @encoding@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_1d97ac35ad4fd634" dIBuilderCreatePointerType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @pointeeTy@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addressSpace@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_22304e0781074c67" dIBuilderCreateStructType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @derivedFrom@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @runTimeLang@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @vTableHolder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @uniqueId@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @uniqueIdLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_9cf2f4b7abbe7dd8" dIBuilderCreateMemberType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @offsetInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_5ef4e66390a11736" dIBuilderCreateStaticMemberType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_d6ea88acdadfb47c" dIBuilderCreateMemberPointerType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @pointeeType@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @classType@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_d56b36d434828ac1" dIBuilderCreateObjCIVar
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @offsetInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @propertyNode@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b3a1d90504750aee" dIBuilderCreateObjCProperty
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @getterName@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @getterNameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @setterName@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @setterNameLen@ -}
  -> FC.CUInt
     {- ^ __from C:__ @propertyAttributes@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_940e3d0e7645ab26" dIBuilderCreateObjectPointerType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b4a2b2e1df395677" dIBuilderCreateQualifiedType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> FC.CUInt
     {- ^ __from C:__ @tag@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_3222fdeb16ca2626" dIBuilderCreateReferenceType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> FC.CUInt
     {- ^ __from C:__ @tag@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_f4f2d9c4b2c01b3c" dIBuilderCreateNullPtrType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_f47701375da6e977" dIBuilderCreateTypedef
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_877f579083f04b41" dIBuilderCreateInheritance
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @baseTy@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @baseOffset@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @vBPtrOffset@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_267b52cce1ebb156" dIBuilderCreateForwardDecl
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> FC.CUInt
     {- ^ __from C:__ @tag@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> FC.CUInt
     {- ^ __from C:__ @runtimeLang@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @uniqueIdentifier@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @uniqueIdentifierLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_2d792ef07748cdea" dIBuilderCreateReplaceableCompositeType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> FC.CUInt
     {- ^ __from C:__ @tag@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @line@ -}
  -> FC.CUInt
     {- ^ __from C:__ @runtimeLang@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @uniqueIdentifier@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @uniqueIdentifierLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_807c01a6073ffbbe" dIBuilderCreateBitFieldMemberType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @offsetInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @storageOffsetInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_fec6334f3451d2b9" dIBuilderCreateClassType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNumber@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @sizeInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @offsetInBits@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @derivedFrom@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @elements@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numElements@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @vTableHolder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @templateParamsNode@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @uniqueIdentifier@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @uniqueIdentifierLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_59745ccf5ab9a7bf" dIBuilderCreateArtificialType
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @type'@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_8c540601760e4eed" dITypeGetName
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_c47eb4840e5bc1e1" dITypeGetSizeInBits
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_117343359f8230d2" dITypeGetOffsetInBits
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_aec93364237481ff" dITypeGetAlignInBits
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> IO HsBindgen.Runtime.Prelude.Word32

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_3e9cffe90f482848" dITypeGetLine
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_1d0d51894b6751d8" dITypeGetFlags
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @dType@ -}
  -> IO DIFlags

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_af03b4fa27044bed" dIBuilderGetOrCreateSubrange
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> HsBindgen.Runtime.Prelude.Int64
     {- ^ __from C:__ @lowerBound@ -}
  -> HsBindgen.Runtime.Prelude.Int64
     {- ^ __from C:__ @count@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_10de1a021de1f4fc" dIBuilderGetOrCreateArray
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @data'@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6f27662faba44436" dIBuilderCreateExpression
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @addr@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_5af35a1d710c1454" dIBuilderCreateConstantValueExpression
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @value@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6a6a85cb32df431c" dIBuilderCreateGlobalVariableExpression
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @linkage@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @linkLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @localToUnit@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @expr@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @decl@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_af36162e136daea5" getDINodeTag
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @mD@ -}
  -> IO HsBindgen.Runtime.Prelude.Word16

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_9231cbac798c279d" dIGlobalVariableExpressionGetVariable
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @gVE@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_14474716f47560e9" dIGlobalVariableExpressionGetExpression
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @gVE@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_9f0273cbf2b99834" dIVariableGetFile
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @var@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b7f722c9f60b7bc7" dIVariableGetScope
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @var@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_eb3f151da8829447" dIVariableGetLine
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @var@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_75927bb6e41253ce" temporaryMDNode
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @ctx@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @data'@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numElements@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_51240435f56e93ad" disposeTemporaryMDNode
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @tempNode@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_79ba16a1007a76a1" metadataReplaceAllUsesWith
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @tempTargetMetadata@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @replacement@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_14d7b98648c79a23" dIBuilderCreateTempGlobalVariableFwdDecl
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @linkage@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @lnkLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @localToUnit@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @decl@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_060c9789b2099755" dIBuilderInsertDeclareRecordBefore
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @storage@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @varInfo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @expr@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @debugLoc@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO LlvmC.Raw.Types.DbgRecordRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_434e7771f3f70cc2" dIBuilderInsertDeclareRecordAtEnd
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @storage@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @varInfo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @expr@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @debugLoc@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> IO LlvmC.Raw.Types.DbgRecordRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_102f9fd605fac304" dIBuilderInsertDbgValueRecordBefore
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @varInfo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @expr@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @debugLoc@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO LlvmC.Raw.Types.DbgRecordRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_414842503b14ea27" dIBuilderInsertDbgValueRecordAtEnd
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @varInfo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @expr@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @debugLoc@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> IO LlvmC.Raw.Types.DbgRecordRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_bfaa0c781d1646c8" dIBuilderCreateAutoVariable
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @alwaysPreserve@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> HsBindgen.Runtime.Prelude.Word32
     {- ^ __from C:__ @alignInBits@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b8b550d5bd22b91a" dIBuilderCreateParameterVariable
  :: LlvmC.Raw.Types.DIBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @scope@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> FC.CUInt
     {- ^ __from C:__ @argNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @file@ -}
  -> FC.CUInt
     {- ^ __from C:__ @lineNo@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @alwaysPreserve@ -}
  -> DIFlags
     {- ^ __from C:__ @flags@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_7f536a0ca9acd316" getSubprogram
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @func@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_f58c1aaff3446ea6" setSubprogram
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @func@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @sP@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_e8a868b63de238ad" dISubprogramGetLine
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @subprogram@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_82097bdfa33ada6b" instructionGetDebugLoc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_b258290996a2cb3e" instructionSetDebugLoc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @loc@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_DebugInfo_6f0f718bc7677368" getMetadataKind
  :: LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @metadata@ -}
  -> IO MetadataKind
