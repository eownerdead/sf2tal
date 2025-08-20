{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Core where

import Data.Bits (FiniteBits)
import qualified Data.Bits as Bits
import qualified Data.Ix as Ix
import qualified Data.List.NonEmpty
import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.IncompleteArray
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Bounded, Enum, Eq, IO, Int, Integral, Num, Ord, Read, Real, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Core.h>\nvoid hs_bindgen_LlvmC_Raw_Core_c660ef7eea24d4ba (void) { LLVMShutdown(); }\nvoid hs_bindgen_LlvmC_Raw_Core_65bd57ec4fa83523 (unsigned int *arg1, unsigned int *arg2, unsigned int *arg3) { LLVMGetVersion(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_0c750bb2f74dfbe2 (char *arg1) { return LLVMCreateMessage(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_e858bd253ce566b7 (char *arg1) { LLVMDisposeMessage(arg1); }\nLLVMContextRef hs_bindgen_LlvmC_Raw_Core_0c9df8eae2f4ed4b (void) { return LLVMContextCreate(); }\nLLVMContextRef hs_bindgen_LlvmC_Raw_Core_18ae1ccbad5f2575 (void) { return LLVMGetGlobalContext(); }\nvoid hs_bindgen_LlvmC_Raw_Core_76e8b923e53eacae (LLVMContextRef arg1, LLVMDiagnosticHandler arg2, void *arg3) { LLVMContextSetDiagnosticHandler(arg1, arg2, arg3); }\nLLVMDiagnosticHandler hs_bindgen_LlvmC_Raw_Core_d6356c1c87d9824f (LLVMContextRef arg1) { return LLVMContextGetDiagnosticHandler(arg1); }\nvoid *hs_bindgen_LlvmC_Raw_Core_fcdf8cdafe22920a (LLVMContextRef arg1) { return LLVMContextGetDiagnosticContext(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_44a29e30928bfb1c (LLVMContextRef arg1, LLVMYieldCallback arg2, void *arg3) { LLVMContextSetYieldCallback(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_adb890434595dc0c (LLVMContextRef arg1) { return LLVMContextShouldDiscardValueNames(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_f62afd7a02a5db37 (LLVMContextRef arg1, LLVMBool arg2) { LLVMContextSetDiscardValueNames(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_8349f73c4278d19a (LLVMContextRef arg1) { LLVMContextDispose(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_fe151e2c3e2269dc (LLVMDiagnosticInfoRef arg1) { return LLVMGetDiagInfoDescription(arg1); }\nLLVMDiagnosticSeverity hs_bindgen_LlvmC_Raw_Core_c97f46e70b7073f1 (LLVMDiagnosticInfoRef arg1) { return LLVMGetDiagInfoSeverity(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_8157ad9d51a3f412 (LLVMContextRef arg1, char *arg2, unsigned int arg3) { return LLVMGetMDKindIDInContext(arg1, arg2, arg3); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_750e3a5fae5b81b7 (char *arg1, unsigned int arg2) { return LLVMGetMDKindID(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_c05f8c2fa2dd3e12 (char *arg1, size_t arg2) { return LLVMGetEnumAttributeKindForName(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_b5ba7a777d43f573 (void) { return LLVMGetLastEnumAttributeKind(); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_9654080d23156fa8 (LLVMContextRef arg1, unsigned int arg2, uint64_t arg3) { return LLVMCreateEnumAttribute(arg1, arg2, arg3); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d1989db82f2761b3 (LLVMAttributeRef arg1) { return LLVMGetEnumAttributeKind(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Core_5035083b24abe2ab (LLVMAttributeRef arg1) { return LLVMGetEnumAttributeValue(arg1); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_44e1a613a5383292 (LLVMContextRef arg1, unsigned int arg2, LLVMTypeRef arg3) { return LLVMCreateTypeAttribute(arg1, arg2, arg3); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_0b40aa19331ffa62 (LLVMAttributeRef arg1) { return LLVMGetTypeAttributeValue(arg1); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_ff1208296dede47c (LLVMContextRef arg1, unsigned int arg2, unsigned int arg3, uint64_t *arg4, uint64_t *arg5) { return LLVMCreateConstantRangeAttribute(arg1, arg2, arg3, arg4, arg5); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_f8e9c8ffcc09cf00 (LLVMContextRef arg1, char *arg2, unsigned int arg3, char *arg4, unsigned int arg5) { return LLVMCreateStringAttribute(arg1, arg2, arg3, arg4, arg5); }\nchar *hs_bindgen_LlvmC_Raw_Core_dd5c313e42c91f52 (LLVMAttributeRef arg1, unsigned int *arg2) { return LLVMGetStringAttributeKind(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_51644d0e228d0322 (LLVMAttributeRef arg1, unsigned int *arg2) { return LLVMGetStringAttributeValue(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_143f4c5d7f274333 (LLVMAttributeRef arg1) { return LLVMIsEnumAttribute(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_2b4daeffe9f11e06 (LLVMAttributeRef arg1) { return LLVMIsStringAttribute(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_848e08677fe0d625 (LLVMAttributeRef arg1) { return LLVMIsTypeAttribute(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_dfc4c1791a068431 (LLVMContextRef arg1, char *arg2) { return LLVMGetTypeByName2(arg1, arg2); }\nLLVMModuleRef hs_bindgen_LlvmC_Raw_Core_f40ed84793bcdd42 (char *arg1) { return LLVMModuleCreateWithName(arg1); }\nLLVMModuleRef hs_bindgen_LlvmC_Raw_Core_acfea95b7084d9b6 (char *arg1, LLVMContextRef arg2) { return LLVMModuleCreateWithNameInContext(arg1, arg2); }\nLLVMModuleRef hs_bindgen_LlvmC_Raw_Core_22fbe3b7a5adf598 (LLVMModuleRef arg1) { return LLVMCloneModule(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_c5aeb649e812136f (LLVMModuleRef arg1) { LLVMDisposeModule(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_1e34c5eb772741c3 (LLVMModuleRef arg1) { return LLVMIsNewDbgInfoFormat(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_0a084eab7853647b (LLVMModuleRef arg1, LLVMBool arg2) { LLVMSetIsNewDbgInfoFormat(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_62a1a7a021bed926 (LLVMModuleRef arg1, size_t *arg2) { return LLVMGetModuleIdentifier(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_0a044135c3a6f6ff (LLVMModuleRef arg1, char *arg2, size_t arg3) { LLVMSetModuleIdentifier(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_6fe89a53d6e25a99 (LLVMModuleRef arg1, size_t *arg2) { return LLVMGetSourceFileName(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_6e8359baecfc2cc3 (LLVMModuleRef arg1, char *arg2, size_t arg3) { LLVMSetSourceFileName(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_00e761614662d2d5 (LLVMModuleRef arg1) { return LLVMGetDataLayoutStr(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_2166c0a9376344b2 (LLVMModuleRef arg1) { return LLVMGetDataLayout(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_02ae7ee7042e39c1 (LLVMModuleRef arg1, char *arg2) { LLVMSetDataLayout(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_2b9ed971c1e70b57 (LLVMModuleRef arg1) { return LLVMGetTarget(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_91740f25aa89d887 (LLVMModuleRef arg1, char *arg2) { LLVMSetTarget(arg1, arg2); }\nLLVMModuleFlagEntry *hs_bindgen_LlvmC_Raw_Core_2231710eba76cc3b (LLVMModuleRef arg1, size_t *arg2) { return LLVMCopyModuleFlagsMetadata(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_fbcad408e7306486 (LLVMModuleFlagEntry *arg1) { LLVMDisposeModuleFlagsMetadata(arg1); }\nLLVMModuleFlagBehavior hs_bindgen_LlvmC_Raw_Core_16044f3a918f7707 (LLVMModuleFlagEntry *arg1, unsigned int arg2) { return LLVMModuleFlagEntriesGetFlagBehavior(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_14643efd62786c2d (LLVMModuleFlagEntry *arg1, unsigned int arg2, size_t *arg3) { return LLVMModuleFlagEntriesGetKey(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_4a2c85205a7ca551 (LLVMModuleFlagEntry *arg1, unsigned int arg2) { return LLVMModuleFlagEntriesGetMetadata(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_da17c373b29963af (LLVMModuleRef arg1, char *arg2, size_t arg3) { return LLVMGetModuleFlag(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_17088b876c779629 (LLVMModuleRef arg1, LLVMModuleFlagBehavior arg2, char *arg3, size_t arg4, LLVMMetadataRef arg5) { LLVMAddModuleFlag(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_Core_9b46a35a39b6ca28 (LLVMModuleRef arg1) { LLVMDumpModule(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_94be70b47353d6e1 (LLVMModuleRef arg1, char *arg2, char **arg3) { return LLVMPrintModuleToFile(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_12e37236b5591bc6 (LLVMModuleRef arg1) { return LLVMPrintModuleToString(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_6a4fc8f47316e2ab (LLVMModuleRef arg1, size_t *arg2) { return LLVMGetModuleInlineAsm(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_34ce0af1a30dbce8 (LLVMModuleRef arg1, char *arg2, size_t arg3) { LLVMSetModuleInlineAsm2(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_db696627d92aa83c (LLVMModuleRef arg1, char *arg2, size_t arg3) { LLVMAppendModuleInlineAsm(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_34cce480519419db (LLVMTypeRef arg1, char *arg2, size_t arg3, char *arg4, size_t arg5, LLVMBool arg6, LLVMBool arg7, LLVMInlineAsmDialect arg8, LLVMBool arg9) { return LLVMGetInlineAsm(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9); }\nchar *hs_bindgen_LlvmC_Raw_Core_763cb22942ec872e (LLVMValueRef arg1, size_t *arg2) { return LLVMGetInlineAsmAsmString(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_8f78269a6c4c7984 (LLVMValueRef arg1, size_t *arg2) { return LLVMGetInlineAsmConstraintString(arg1, arg2); }\nLLVMInlineAsmDialect hs_bindgen_LlvmC_Raw_Core_3ddb5c48e6f23785 (LLVMValueRef arg1) { return LLVMGetInlineAsmDialect(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_0cbe6c1452db36fd (LLVMValueRef arg1) { return LLVMGetInlineAsmFunctionType(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_2bce8800f6386f8b (LLVMValueRef arg1) { return LLVMGetInlineAsmHasSideEffects(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_a788ada940375dde (LLVMValueRef arg1) { return LLVMGetInlineAsmNeedsAlignedStack(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_7e7178d53c22ea9d (LLVMValueRef arg1) { return LLVMGetInlineAsmCanUnwind(arg1); }\nLLVMContextRef hs_bindgen_LlvmC_Raw_Core_3fa834032b26ea51 (LLVMModuleRef arg1) { return LLVMGetModuleContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_8a4a2487dcaa15f4 (LLVMModuleRef arg1, char *arg2) { return LLVMGetTypeByName(arg1, arg2); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_cf761402d484ee76 (LLVMModuleRef arg1) { return LLVMGetFirstNamedMetadata(arg1); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_3ba47055a92c2e12 (LLVMModuleRef arg1) { return LLVMGetLastNamedMetadata(arg1); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_f80acaf202bed5ae (LLVMNamedMDNodeRef arg1) { return LLVMGetNextNamedMetadata(arg1); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_811ace267229591c (LLVMNamedMDNodeRef arg1) { return LLVMGetPreviousNamedMetadata(arg1); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_8cf1573206a8038a (LLVMModuleRef arg1, char *arg2, size_t arg3) { return LLVMGetNamedMetadata(arg1, arg2, arg3); }\nLLVMNamedMDNodeRef hs_bindgen_LlvmC_Raw_Core_233ee9fea637a3ea (LLVMModuleRef arg1, char *arg2, size_t arg3) { return LLVMGetOrInsertNamedMetadata(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_e7b3858bac64c88c (LLVMNamedMDNodeRef arg1, size_t *arg2) { return LLVMGetNamedMetadataName(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_110d8a5ec22c60c6 (LLVMModuleRef arg1, char *arg2) { return LLVMGetNamedMetadataNumOperands(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_ad1d6c09f035029c (LLVMModuleRef arg1, char *arg2, LLVMValueRef *arg3) { LLVMGetNamedMetadataOperands(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_557ae7ece7419218 (LLVMModuleRef arg1, char *arg2, LLVMValueRef arg3) { LLVMAddNamedMetadataOperand(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_decdded8ea4e10e0 (LLVMValueRef arg1, unsigned int *arg2) { return LLVMGetDebugLocDirectory(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_5b30737776c61e94 (LLVMValueRef arg1, unsigned int *arg2) { return LLVMGetDebugLocFilename(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_e8a705caecb7613e (LLVMValueRef arg1) { return LLVMGetDebugLocLine(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_2459f0b6e7f6b30a (LLVMValueRef arg1) { return LLVMGetDebugLocColumn(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_34adef42c3b9bc83 (LLVMModuleRef arg1, char *arg2, LLVMTypeRef arg3) { return LLVMAddFunction(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_36a0fc333f895125 (LLVMModuleRef arg1, char *arg2) { return LLVMGetNamedFunction(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_aa2fd2d9f9b6f45a (LLVMModuleRef arg1) { return LLVMGetFirstFunction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f187758219370b71 (LLVMModuleRef arg1) { return LLVMGetLastFunction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_763ca186883b97b7 (LLVMValueRef arg1) { return LLVMGetNextFunction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_72e81560dbd8f811 (LLVMValueRef arg1) { return LLVMGetPreviousFunction(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_bed40cbecdad0a4a (LLVMModuleRef arg1, char *arg2) { LLVMSetModuleInlineAsm(arg1, arg2); }\nLLVMTypeKind hs_bindgen_LlvmC_Raw_Core_6efc04a8142542f5 (LLVMTypeRef arg1) { return LLVMGetTypeKind(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_596f3252c558b37b (LLVMTypeRef arg1) { return LLVMTypeIsSized(arg1); }\nLLVMContextRef hs_bindgen_LlvmC_Raw_Core_66baf11867a251e6 (LLVMTypeRef arg1) { return LLVMGetTypeContext(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_fdf7ed1a5dbea855 (LLVMTypeRef arg1) { LLVMDumpType(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_21c3b6c66a3125d1 (LLVMTypeRef arg1) { return LLVMPrintTypeToString(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_5b47a43c46c71996 (LLVMContextRef arg1) { return LLVMInt1TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_81b45eba83cb4686 (LLVMContextRef arg1) { return LLVMInt8TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_2b80ffe01d952a00 (LLVMContextRef arg1) { return LLVMInt16TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_5554c58cfccc7842 (LLVMContextRef arg1) { return LLVMInt32TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_1645be95b2999a27 (LLVMContextRef arg1) { return LLVMInt64TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_9d37dd31fe9ed00f (LLVMContextRef arg1) { return LLVMInt128TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_8662c58e34e524a2 (LLVMContextRef arg1, unsigned int arg2) { return LLVMIntTypeInContext(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_3048d3db949b8d90 (void) { return LLVMInt1Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_9401a3794e6e0fbe (void) { return LLVMInt8Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_a6b48d0af55a2a6f (void) { return LLVMInt16Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_7b99fb943d4feb98 (void) { return LLVMInt32Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b6b714cbacaff1b1 (void) { return LLVMInt64Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_ea7a26825a49b747 (void) { return LLVMInt128Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_a50353e0b58836a9 (unsigned int arg1) { return LLVMIntType(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_4b74a3228f8825b7 (LLVMTypeRef arg1) { return LLVMGetIntTypeWidth(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_7249cd3ef56add0f (LLVMContextRef arg1) { return LLVMHalfTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_8c7f43aa8bcf0af8 (LLVMContextRef arg1) { return LLVMBFloatTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_af6f4a1cbbf4f1c5 (LLVMContextRef arg1) { return LLVMFloatTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_3372128e23b9358b (LLVMContextRef arg1) { return LLVMDoubleTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b2030c19a72cb5f1 (LLVMContextRef arg1) { return LLVMX86FP80TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_72bbef3fb8a90bed (LLVMContextRef arg1) { return LLVMFP128TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_c0593b6725b4442e (LLVMContextRef arg1) { return LLVMPPCFP128TypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_dbe2f77aca7bd008 (void) { return LLVMHalfType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_e8ae3dc235e4ccaa (void) { return LLVMBFloatType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_41d1a296ff6808c4 (void) { return LLVMFloatType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_116ab54ba727009b (void) { return LLVMDoubleType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_df014ebd7ce2b0bd (void) { return LLVMX86FP80Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_049b89b8b6d0331b (void) { return LLVMFP128Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_9abf5b0574fef014 (void) { return LLVMPPCFP128Type(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_6d91c0302192801c (LLVMTypeRef arg1, LLVMTypeRef *arg2, unsigned int arg3, LLVMBool arg4) { return LLVMFunctionType(arg1, arg2, arg3, arg4); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_4d9be33b4643917e (LLVMTypeRef arg1) { return LLVMIsFunctionVarArg(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_810909d4cfc04ffb (LLVMTypeRef arg1) { return LLVMGetReturnType(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_2b5c4a5166648b87 (LLVMTypeRef arg1) { return LLVMCountParamTypes(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_2fa6b88fb873d810 (LLVMTypeRef arg1, LLVMTypeRef *arg2) { LLVMGetParamTypes(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_7d5670a5232a409d (LLVMContextRef arg1, LLVMTypeRef *arg2, unsigned int arg3, LLVMBool arg4) { return LLVMStructTypeInContext(arg1, arg2, arg3, arg4); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_7ed42f9c9689f856 (LLVMTypeRef *arg1, unsigned int arg2, LLVMBool arg3) { return LLVMStructType(arg1, arg2, arg3); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_fb9ae856f933ce3c (LLVMContextRef arg1, char *arg2) { return LLVMStructCreateNamed(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_ad97c14b347fa0f2 (LLVMTypeRef arg1) { return LLVMGetStructName(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_59ad629727e32cae (LLVMTypeRef arg1, LLVMTypeRef *arg2, unsigned int arg3, LLVMBool arg4) { LLVMStructSetBody(arg1, arg2, arg3, arg4); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_bf3b3bfacf5c212d (LLVMTypeRef arg1) { return LLVMCountStructElementTypes(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4becc113fd41d964 (LLVMTypeRef arg1, LLVMTypeRef *arg2) { LLVMGetStructElementTypes(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_280946a8aadd95b8 (LLVMTypeRef arg1, unsigned int arg2) { return LLVMStructGetTypeAtIndex(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_9a67cf6d2d16526e (LLVMTypeRef arg1) { return LLVMIsPackedStruct(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_d05cf09de3330c37 (LLVMTypeRef arg1) { return LLVMIsOpaqueStruct(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_b45fc300305f28d7 (LLVMTypeRef arg1) { return LLVMIsLiteralStruct(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_71d7175693fe8526 (LLVMTypeRef arg1) { return LLVMGetElementType(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_3adbd41c35bcf167 (LLVMTypeRef arg1, LLVMTypeRef *arg2) { LLVMGetSubtypes(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_a470af21593a3265 (LLVMTypeRef arg1) { return LLVMGetNumContainedTypes(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_26029a112be6d9c6 (LLVMTypeRef arg1, unsigned int arg2) { return LLVMArrayType(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_c36f5c47a241db50 (LLVMTypeRef arg1, uint64_t arg2) { return LLVMArrayType2(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_694d35caa5e31295 (LLVMTypeRef arg1) { return LLVMGetArrayLength(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Core_75f5f14e1aff88d9 (LLVMTypeRef arg1) { return LLVMGetArrayLength2(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_5c752a4ad5987419 (LLVMTypeRef arg1, unsigned int arg2) { return LLVMPointerType(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_46edaefee3535cc7 (LLVMTypeRef arg1) { return LLVMPointerTypeIsOpaque(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b88846597f730531 (LLVMContextRef arg1, unsigned int arg2) { return LLVMPointerTypeInContext(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_027b06ec7f026acb (LLVMTypeRef arg1) { return LLVMGetPointerAddressSpace(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_2ff503d6ebb9d8dc (LLVMTypeRef arg1, unsigned int arg2) { return LLVMVectorType(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_fd2438f820e045f5 (LLVMTypeRef arg1, unsigned int arg2) { return LLVMScalableVectorType(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_4a835958c61c9318 (LLVMTypeRef arg1) { return LLVMGetVectorSize(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cb6cca4b7cda1dba (LLVMValueRef arg1) { return LLVMGetConstantPtrAuthPointer(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cd5236f22ff5006c (LLVMValueRef arg1) { return LLVMGetConstantPtrAuthKey(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6f2a22af1e59dd01 (LLVMValueRef arg1) { return LLVMGetConstantPtrAuthDiscriminator(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3045aec7fe57a584 (LLVMValueRef arg1) { return LLVMGetConstantPtrAuthAddrDiscriminator(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_83f7c7e2402321bf (LLVMContextRef arg1) { return LLVMVoidTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_2946d9fe32f41791 (LLVMContextRef arg1) { return LLVMLabelTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_dafc8fda8254262d (LLVMContextRef arg1) { return LLVMX86MMXTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_9d548e8842b9b518 (LLVMContextRef arg1) { return LLVMX86AMXTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b16feff443526a6e (LLVMContextRef arg1) { return LLVMTokenTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_fb1c9d12de1e9e1a (LLVMContextRef arg1) { return LLVMMetadataTypeInContext(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b0df5ee069fe99e5 (void) { return LLVMVoidType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_a75cdea0f88aca88 (void) { return LLVMLabelType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_8287bfbdcfcc51b6 (void) { return LLVMX86MMXType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_31ec7704f9ae0db5 (void) { return LLVMX86AMXType(); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_b74edcd44f2ab284 (LLVMContextRef arg1, char *arg2, LLVMTypeRef *arg3, unsigned int arg4, unsigned int *arg5, unsigned int arg6) { return LLVMTargetExtTypeInContext(arg1, arg2, arg3, arg4, arg5, arg6); }\nchar *hs_bindgen_LlvmC_Raw_Core_c4213d772e69970e (LLVMTypeRef arg1) { return LLVMGetTargetExtTypeName(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d0a4f76b249cf2e9 (LLVMTypeRef arg1) { return LLVMGetTargetExtTypeNumTypeParams(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_e5ddd30fd79df35c (LLVMTypeRef arg1, unsigned int arg2) { return LLVMGetTargetExtTypeTypeParam(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_7a362586c264faf4 (LLVMTypeRef arg1) { return LLVMGetTargetExtTypeNumIntParams(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_2156e1007893eb35 (LLVMTypeRef arg1, unsigned int arg2) { return LLVMGetTargetExtTypeIntParam(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_6949e588426b685b (LLVMValueRef arg1) { return LLVMTypeOf(arg1); }\nLLVMValueKind hs_bindgen_LlvmC_Raw_Core_160161bb05117d76 (LLVMValueRef arg1) { return LLVMGetValueKind(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_40b32422b547ee1a (LLVMValueRef arg1, size_t *arg2) { return LLVMGetValueName2(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_9ad4f0f4db7e00ba (LLVMValueRef arg1, char *arg2, size_t arg3) { LLVMSetValueName2(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_0660aefb99e00360 (LLVMValueRef arg1) { LLVMDumpValue(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_8187c8cbc9c35391 (LLVMValueRef arg1) { return LLVMPrintValueToString(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_360a6008feee9751 (LLVMDbgRecordRef arg1) { return LLVMPrintDbgRecordToString(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_910f87142dfe4d3a (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMReplaceAllUsesWith(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_2feb13a1d9ec7785 (LLVMValueRef arg1) { return LLVMIsConstant(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_ba47f497cb3553cc (LLVMValueRef arg1) { return LLVMIsUndef(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_24230734e77ee572 (LLVMValueRef arg1) { return LLVMIsPoison(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_81d80c8190a951b2 (LLVMValueRef arg1) { return LLVMIsAArgument(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_bff99ee872b624d9 (LLVMValueRef arg1) { return LLVMIsABasicBlock(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_426e30e449bae6c2 (LLVMValueRef arg1) { return LLVMIsAInlineAsm(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cc13a7160000b971 (LLVMValueRef arg1) { return LLVMIsAUser(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_bf6964d78b71d113 (LLVMValueRef arg1) { return LLVMIsAConstant(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_df9c6089b5db2a0b (LLVMValueRef arg1) { return LLVMIsABlockAddress(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e83826a32a4ca01a (LLVMValueRef arg1) { return LLVMIsAConstantAggregateZero(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_51da9e38cd7beb6f (LLVMValueRef arg1) { return LLVMIsAConstantArray(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_776cb3244575331b (LLVMValueRef arg1) { return LLVMIsAConstantDataSequential(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f4e59c470e7910f8 (LLVMValueRef arg1) { return LLVMIsAConstantDataArray(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_01ddfe2d1619a80d (LLVMValueRef arg1) { return LLVMIsAConstantDataVector(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f09da101ad4d0918 (LLVMValueRef arg1) { return LLVMIsAConstantExpr(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_bcebac0703c9339c (LLVMValueRef arg1) { return LLVMIsAConstantFP(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cc2a3902c68cff38 (LLVMValueRef arg1) { return LLVMIsAConstantInt(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2bf21db1ceb950f9 (LLVMValueRef arg1) { return LLVMIsAConstantPointerNull(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9b968107e9b368e0 (LLVMValueRef arg1) { return LLVMIsAConstantStruct(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b775af0cfe332ead (LLVMValueRef arg1) { return LLVMIsAConstantTokenNone(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_43031181e7214dc8 (LLVMValueRef arg1) { return LLVMIsAConstantVector(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c569999e022bc42d (LLVMValueRef arg1) { return LLVMIsAConstantPtrAuth(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_bf5d44837f2084f1 (LLVMValueRef arg1) { return LLVMIsAGlobalValue(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a418b870d0c1cdb9 (LLVMValueRef arg1) { return LLVMIsAGlobalAlias(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1f5fe63908fe62f2 (LLVMValueRef arg1) { return LLVMIsAGlobalObject(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_eab190632c144f3a (LLVMValueRef arg1) { return LLVMIsAFunction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f39a91f5c8a8240c (LLVMValueRef arg1) { return LLVMIsAGlobalVariable(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_97bbb74ade678b02 (LLVMValueRef arg1) { return LLVMIsAGlobalIFunc(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d253e396588805d4 (LLVMValueRef arg1) { return LLVMIsAUndefValue(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a9462edb64581228 (LLVMValueRef arg1) { return LLVMIsAPoisonValue(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f5af237c77ded862 (LLVMValueRef arg1) { return LLVMIsAInstruction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e4332882abe13019 (LLVMValueRef arg1) { return LLVMIsAUnaryOperator(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_547529aa128078cb (LLVMValueRef arg1) { return LLVMIsABinaryOperator(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_48bc770fadb28368 (LLVMValueRef arg1) { return LLVMIsACallInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fb93c13779ab2f60 (LLVMValueRef arg1) { return LLVMIsAIntrinsicInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1d183980f090a895 (LLVMValueRef arg1) { return LLVMIsADbgInfoIntrinsic(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ff9def3b64ae241a (LLVMValueRef arg1) { return LLVMIsADbgVariableIntrinsic(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3b081c6472306889 (LLVMValueRef arg1) { return LLVMIsADbgDeclareInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9300ff7ed1555055 (LLVMValueRef arg1) { return LLVMIsADbgLabelInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_dd0b6ecd48835efb (LLVMValueRef arg1) { return LLVMIsAMemIntrinsic(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e3b157303c86c7d9 (LLVMValueRef arg1) { return LLVMIsAMemCpyInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c185a7fadb16e29d (LLVMValueRef arg1) { return LLVMIsAMemMoveInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_59360f8d765051d3 (LLVMValueRef arg1) { return LLVMIsAMemSetInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1d9411a28c5551ab (LLVMValueRef arg1) { return LLVMIsACmpInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3a2d046f07d9b1d9 (LLVMValueRef arg1) { return LLVMIsAFCmpInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f56642cd72af69e3 (LLVMValueRef arg1) { return LLVMIsAICmpInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_180d6dabe728f4c5 (LLVMValueRef arg1) { return LLVMIsAExtractElementInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d818ae7ee1f12b51 (LLVMValueRef arg1) { return LLVMIsAGetElementPtrInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_59afafe0f8d34336 (LLVMValueRef arg1) { return LLVMIsAInsertElementInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4ae690f2eac242b1 (LLVMValueRef arg1) { return LLVMIsAInsertValueInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2e088ac81cefb800 (LLVMValueRef arg1) { return LLVMIsALandingPadInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_968f66b82f09e9d8 (LLVMValueRef arg1) { return LLVMIsAPHINode(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2152d07fc4205deb (LLVMValueRef arg1) { return LLVMIsASelectInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_abeaac9c3af81c1f (LLVMValueRef arg1) { return LLVMIsAShuffleVectorInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7d1a32a38ac221cd (LLVMValueRef arg1) { return LLVMIsAStoreInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_030ed5cb98ff35bd (LLVMValueRef arg1) { return LLVMIsABranchInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_698fc003189adb06 (LLVMValueRef arg1) { return LLVMIsAIndirectBrInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4998d932d15205a8 (LLVMValueRef arg1) { return LLVMIsAInvokeInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_62d5637f5b31c758 (LLVMValueRef arg1) { return LLVMIsAReturnInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f13ce1e12fc81a20 (LLVMValueRef arg1) { return LLVMIsASwitchInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6e219b36ae63aded (LLVMValueRef arg1) { return LLVMIsAUnreachableInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7acffaa87a148429 (LLVMValueRef arg1) { return LLVMIsAResumeInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f58ae8ee91f9f19b (LLVMValueRef arg1) { return LLVMIsACleanupReturnInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cb7093faa6206529 (LLVMValueRef arg1) { return LLVMIsACatchReturnInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b13c14403b761165 (LLVMValueRef arg1) { return LLVMIsACatchSwitchInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_5f5c0286f27c3221 (LLVMValueRef arg1) { return LLVMIsACallBrInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_18544ec766f3542a (LLVMValueRef arg1) { return LLVMIsAFuncletPadInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_27eb2287a832704b (LLVMValueRef arg1) { return LLVMIsACatchPadInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d2e9824c14ccc592 (LLVMValueRef arg1) { return LLVMIsACleanupPadInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9a1ff3d576a39730 (LLVMValueRef arg1) { return LLVMIsAUnaryInstruction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2d14eb4bf8dc8964 (LLVMValueRef arg1) { return LLVMIsAAllocaInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0d0d66083f456bf3 (LLVMValueRef arg1) { return LLVMIsACastInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0573663220b74681 (LLVMValueRef arg1) { return LLVMIsAAddrSpaceCastInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_338014e0dd67d012 (LLVMValueRef arg1) { return LLVMIsABitCastInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_548b8735a3719185 (LLVMValueRef arg1) { return LLVMIsAFPExtInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9c45b2328a838d85 (LLVMValueRef arg1) { return LLVMIsAFPToSIInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6a8b23a80dce2723 (LLVMValueRef arg1) { return LLVMIsAFPToUIInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_99f2df36b122b08d (LLVMValueRef arg1) { return LLVMIsAFPTruncInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b2468dd1a762babf (LLVMValueRef arg1) { return LLVMIsAIntToPtrInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4691475c0e23723e (LLVMValueRef arg1) { return LLVMIsAPtrToIntInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9e67234be595e3b8 (LLVMValueRef arg1) { return LLVMIsASExtInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_abae807e489af4c3 (LLVMValueRef arg1) { return LLVMIsASIToFPInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_93862148876fa07c (LLVMValueRef arg1) { return LLVMIsATruncInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ff55f5c06d759c77 (LLVMValueRef arg1) { return LLVMIsAUIToFPInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f6d988e404470765 (LLVMValueRef arg1) { return LLVMIsAZExtInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e8d77b1c4c3cf727 (LLVMValueRef arg1) { return LLVMIsAExtractValueInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_44116c5f4cccc1c5 (LLVMValueRef arg1) { return LLVMIsALoadInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_598b4596261af7ec (LLVMValueRef arg1) { return LLVMIsAVAArgInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f5f19bf7c13847df (LLVMValueRef arg1) { return LLVMIsAFreezeInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ea5f13aa3a074a5b (LLVMValueRef arg1) { return LLVMIsAAtomicCmpXchgInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_51a5ed4ed5a0fa57 (LLVMValueRef arg1) { return LLVMIsAAtomicRMWInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a57263187d69c785 (LLVMValueRef arg1) { return LLVMIsAFenceInst(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_baa46b4187501c24 (LLVMValueRef arg1) { return LLVMIsAMDNode(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_29b9107dfa2b037f (LLVMValueRef arg1) { return LLVMIsAValueAsMetadata(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_195d52cd38746e76 (LLVMValueRef arg1) { return LLVMIsAMDString(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_a0abc80364768961 (LLVMValueRef arg1) { return LLVMGetValueName(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_d2d842cd38927ad6 (LLVMValueRef arg1, char *arg2) { LLVMSetValueName(arg1, arg2); }\nLLVMUseRef hs_bindgen_LlvmC_Raw_Core_bb63a93399ba0c08 (LLVMValueRef arg1) { return LLVMGetFirstUse(arg1); }\nLLVMUseRef hs_bindgen_LlvmC_Raw_Core_19f4a6f8b56e4fb1 (LLVMUseRef arg1) { return LLVMGetNextUse(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b530f5a40491854d (LLVMUseRef arg1) { return LLVMGetUser(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_87e7d32c7298155f (LLVMUseRef arg1) { return LLVMGetUsedValue(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_38241c8f083615c9 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetOperand(arg1, arg2); }\nLLVMUseRef hs_bindgen_LlvmC_Raw_Core_db48b7b15953e4d5 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetOperandUse(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_00472a7129e576f1 (LLVMValueRef arg1, unsigned int arg2, LLVMValueRef arg3) { LLVMSetOperand(arg1, arg2, arg3); }\nsigned int hs_bindgen_LlvmC_Raw_Core_d8939614db5be876 (LLVMValueRef arg1) { return LLVMGetNumOperands(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a7a825b7e07c6920 (LLVMTypeRef arg1) { return LLVMConstNull(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_06b7bd1735a84cbf (LLVMTypeRef arg1) { return LLVMConstAllOnes(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0a6f1cab329086e6 (LLVMTypeRef arg1) { return LLVMGetUndef(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1e28be075fdcbadb (LLVMTypeRef arg1) { return LLVMGetPoison(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_91e5cfdbce21298a (LLVMValueRef arg1) { return LLVMIsNull(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9f5bc935f3c9ccef (LLVMTypeRef arg1) { return LLVMConstPointerNull(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cd69f898b240a3b6 (LLVMTypeRef arg1, unsigned long long arg2, LLVMBool arg3) { return LLVMConstInt(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a08dfdee4e5fb51d (LLVMTypeRef arg1, unsigned int arg2, uint64_t *arg3) { return LLVMConstIntOfArbitraryPrecision(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_49dffd7555089af6 (LLVMTypeRef arg1, char *arg2, uint8_t arg3) { return LLVMConstIntOfString(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_dbbae2f2ed044a31 (LLVMTypeRef arg1, char *arg2, unsigned int arg3, uint8_t arg4) { return LLVMConstIntOfStringAndSize(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4d76dac773ebf346 (LLVMTypeRef arg1, double arg2) { return LLVMConstReal(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_5ed898540a4e301b (LLVMTypeRef arg1, char *arg2) { return LLVMConstRealOfString(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4103f46d3643be5c (LLVMTypeRef arg1, char *arg2, unsigned int arg3) { return LLVMConstRealOfStringAndSize(arg1, arg2, arg3); }\nunsigned long long hs_bindgen_LlvmC_Raw_Core_065b72f9693e046e (LLVMValueRef arg1) { return LLVMConstIntGetZExtValue(arg1); }\nsigned long long hs_bindgen_LlvmC_Raw_Core_84ae878f19b72216 (LLVMValueRef arg1) { return LLVMConstIntGetSExtValue(arg1); }\ndouble hs_bindgen_LlvmC_Raw_Core_0028efcaf9839842 (LLVMValueRef arg1, LLVMBool *arg2) { return LLVMConstRealGetDouble(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f80c98e38481d491 (LLVMContextRef arg1, char *arg2, unsigned int arg3, LLVMBool arg4) { return LLVMConstStringInContext(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ceb68e644873e95d (LLVMContextRef arg1, char *arg2, size_t arg3, LLVMBool arg4) { return LLVMConstStringInContext2(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e706f63a354d0ee2 (char *arg1, unsigned int arg2, LLVMBool arg3) { return LLVMConstString(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_e24d465b8b605b0b (LLVMValueRef arg1) { return LLVMIsConstantString(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_05cdfb60c8bd7d10 (LLVMValueRef arg1, size_t *arg2) { return LLVMGetAsString(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6b56ecc70339b8a1 (LLVMContextRef arg1, LLVMValueRef *arg2, unsigned int arg3, LLVMBool arg4) { return LLVMConstStructInContext(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_205434094c784e16 (LLVMValueRef *arg1, unsigned int arg2, LLVMBool arg3) { return LLVMConstStruct(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_bbae4588d3e9c66c (LLVMTypeRef arg1, LLVMValueRef *arg2, unsigned int arg3) { return LLVMConstArray(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4ab1a1e23a0153ac (LLVMTypeRef arg1, LLVMValueRef *arg2, uint64_t arg3) { return LLVMConstArray2(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4220ba983a31afe3 (LLVMTypeRef arg1, LLVMValueRef *arg2, unsigned int arg3) { return LLVMConstNamedStruct(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f119a1a823a93231 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetAggregateElement(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_14b8e3c154371f0e (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetElementAsConstant(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b41294b940318c9e (LLVMValueRef *arg1, unsigned int arg2) { return LLVMConstVector(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_08c4590699ccccbd (LLVMValueRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4) { return LLVMConstantPtrAuth(arg1, arg2, arg3, arg4); }\nLLVMOpcode hs_bindgen_LlvmC_Raw_Core_11d087b19b9c25c4 (LLVMValueRef arg1) { return LLVMGetConstOpcode(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f8076cd114ecc0a0 (LLVMTypeRef arg1) { return LLVMAlignOf(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cac24ad7369fa2a1 (LLVMTypeRef arg1) { return LLVMSizeOf(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c929918d5ed7b095 (LLVMValueRef arg1) { return LLVMConstNeg(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0f699a53f4aa6920 (LLVMValueRef arg1) { return LLVMConstNSWNeg(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9736a246c4d45b93 (LLVMValueRef arg1) { return LLVMConstNUWNeg(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_080378937434c0eb (LLVMValueRef arg1) { return LLVMConstNot(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0e57ac84c08f78e1 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstAdd(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_17836442429b1048 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNSWAdd(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2ff9241e8a83bcc1 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNUWAdd(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e6a70386a6dcc12b (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstSub(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_860b940b6308467d (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNSWSub(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d2b9f64985736168 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNUWSub(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_860457d769e5b66f (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstMul(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6dda81d468ab1591 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNSWMul(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0f194320874dfc20 (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstNUWMul(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_8eda015c9f50ca3e (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstXor(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1c06b5d226579727 (LLVMTypeRef arg1, LLVMValueRef arg2, LLVMValueRef *arg3, unsigned int arg4) { return LLVMConstGEP2(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_57000d6968127c8c (LLVMTypeRef arg1, LLVMValueRef arg2, LLVMValueRef *arg3, unsigned int arg4) { return LLVMConstInBoundsGEP2(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_499c7b0e9f8fb7d7 (LLVMTypeRef arg1, LLVMValueRef arg2, LLVMValueRef *arg3, unsigned int arg4, LLVMGEPNoWrapFlags arg5) { return LLVMConstGEPWithNoWrapFlags(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e671d06eb9b7c5fb (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstTrunc(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c80f24f304384bc3 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstPtrToInt(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a7a22e22ffacc167 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstIntToPtr(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_310b773e7fd171d9 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstBitCast(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c47980cbf77a9258 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstAddrSpaceCast(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_5bb63a9e00b51011 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstTruncOrBitCast(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_5c5de024f900e6e9 (LLVMValueRef arg1, LLVMTypeRef arg2) { return LLVMConstPointerCast(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d18df2ea0e5cefbc (LLVMValueRef arg1, LLVMValueRef arg2) { return LLVMConstExtractElement(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a1de64dc381aae3d (LLVMValueRef arg1, LLVMValueRef arg2, LLVMValueRef arg3) { return LLVMConstInsertElement(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c1127a57f6d8b9d3 (LLVMValueRef arg1, LLVMValueRef arg2, LLVMValueRef arg3) { return LLVMConstShuffleVector(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_05d360b6e838ece0 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { return LLVMBlockAddress(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_42ac282cfaa9fc50 (LLVMValueRef arg1) { return LLVMGetBlockAddressFunction(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_c311e8a0d4d99b21 (LLVMValueRef arg1) { return LLVMGetBlockAddressBasicBlock(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b82f9f7e6c457467 (LLVMTypeRef arg1, char *arg2, char *arg3, LLVMBool arg4, LLVMBool arg5) { return LLVMConstInlineAsm(arg1, arg2, arg3, arg4, arg5); }\nLLVMModuleRef hs_bindgen_LlvmC_Raw_Core_5d84d67916fe2414 (LLVMValueRef arg1) { return LLVMGetGlobalParent(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_47ee9d3a8491fa0e (LLVMValueRef arg1) { return LLVMIsDeclaration(arg1); }\nLLVMLinkage hs_bindgen_LlvmC_Raw_Core_e369134559ea51a8 (LLVMValueRef arg1) { return LLVMGetLinkage(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_a8a118e6012cec39 (LLVMValueRef arg1, LLVMLinkage arg2) { LLVMSetLinkage(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_669ecc0330111487 (LLVMValueRef arg1) { return LLVMGetSection(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_97b8f577f1f1f818 (LLVMValueRef arg1, char *arg2) { LLVMSetSection(arg1, arg2); }\nLLVMVisibility hs_bindgen_LlvmC_Raw_Core_f352ccc3f318c498 (LLVMValueRef arg1) { return LLVMGetVisibility(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_109faa626f3ec0a5 (LLVMValueRef arg1, LLVMVisibility arg2) { LLVMSetVisibility(arg1, arg2); }\nLLVMDLLStorageClass hs_bindgen_LlvmC_Raw_Core_01acbf4fbd01d46c (LLVMValueRef arg1) { return LLVMGetDLLStorageClass(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_9e04be30a35070bb (LLVMValueRef arg1, LLVMDLLStorageClass arg2) { LLVMSetDLLStorageClass(arg1, arg2); }\nLLVMUnnamedAddr hs_bindgen_LlvmC_Raw_Core_db72f3f32f26d8e7 (LLVMValueRef arg1) { return LLVMGetUnnamedAddress(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_47207d0d84119b7d (LLVMValueRef arg1, LLVMUnnamedAddr arg2) { LLVMSetUnnamedAddress(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_c7fae327629d97af (LLVMValueRef arg1) { return LLVMGlobalGetValueType(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_526253c0d6b6616f (LLVMValueRef arg1) { return LLVMHasUnnamedAddr(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_9f3e9b49184541fd (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetUnnamedAddr(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_c3d8b3831f434d29 (LLVMValueRef arg1) { return LLVMGetAlignment(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_6e708f0a1d621cec (LLVMValueRef arg1, unsigned int arg2) { LLVMSetAlignment(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_b132e3e4383021e8 (LLVMValueRef arg1, unsigned int arg2, LLVMMetadataRef arg3) { LLVMGlobalSetMetadata(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_3f8755e6c2dfb6c9 (LLVMValueRef arg1, unsigned int arg2) { LLVMGlobalEraseMetadata(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_df1e2afebb8b80ed (LLVMValueRef arg1) { LLVMGlobalClearMetadata(arg1); }\nLLVMValueMetadataEntry *hs_bindgen_LlvmC_Raw_Core_a71b22cbdfaea9c0 (LLVMValueRef arg1, size_t *arg2) { return LLVMGlobalCopyAllMetadata(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_032b7cfdc192e6f0 (LLVMValueMetadataEntry *arg1) { LLVMDisposeValueMetadataEntries(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_e38dacc26b323c7a (LLVMValueMetadataEntry *arg1, unsigned int arg2) { return LLVMValueMetadataEntriesGetKind(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_6a5062c98e9bd70f (LLVMValueMetadataEntry *arg1, unsigned int arg2) { return LLVMValueMetadataEntriesGetMetadata(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_288620c4c2ece5f9 (LLVMModuleRef arg1, LLVMTypeRef arg2, char *arg3) { return LLVMAddGlobal(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9fb91e46ed811984 (LLVMModuleRef arg1, LLVMTypeRef arg2, char *arg3, unsigned int arg4) { return LLVMAddGlobalInAddressSpace(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_397cec9bbdfc0385 (LLVMModuleRef arg1, char *arg2) { return LLVMGetNamedGlobal(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c8ba526992b93237 (LLVMModuleRef arg1) { return LLVMGetFirstGlobal(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0393b8bd3f3d76b1 (LLVMModuleRef arg1) { return LLVMGetLastGlobal(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d7f26074e434d94c (LLVMValueRef arg1) { return LLVMGetNextGlobal(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c82bd6d905d15dac (LLVMValueRef arg1) { return LLVMGetPreviousGlobal(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_ab3ba6aef4a985e4 (LLVMValueRef arg1) { LLVMDeleteGlobal(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_714d3cf3611a5fd2 (LLVMValueRef arg1) { return LLVMGetInitializer(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_518bf57d32a5c832 (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetInitializer(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_e448e5a56db28b3a (LLVMValueRef arg1) { return LLVMIsThreadLocal(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_627b7b102b31de05 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetThreadLocal(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_1ce19ea9f3f1993d (LLVMValueRef arg1) { return LLVMIsGlobalConstant(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_356b78b4aef978aa (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetGlobalConstant(arg1, arg2); }\nLLVMThreadLocalMode hs_bindgen_LlvmC_Raw_Core_1af3e12cceffceea (LLVMValueRef arg1) { return LLVMGetThreadLocalMode(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_6ab1129a4cebba99 (LLVMValueRef arg1, LLVMThreadLocalMode arg2) { LLVMSetThreadLocalMode(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_51d4acf224bc8dfa (LLVMValueRef arg1) { return LLVMIsExternallyInitialized(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_8cd153cbbdf610db (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetExternallyInitialized(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f731078614a84dea (LLVMModuleRef arg1, LLVMTypeRef arg2, unsigned int arg3, LLVMValueRef arg4, char *arg5) { return LLVMAddAlias2(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0759173336db5c1d (LLVMModuleRef arg1, char *arg2, size_t arg3) { return LLVMGetNamedGlobalAlias(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4e1e21751f05bc08 (LLVMModuleRef arg1) { return LLVMGetFirstGlobalAlias(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9b24814c501221e9 (LLVMModuleRef arg1) { return LLVMGetLastGlobalAlias(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_23adaa4b7d55ec18 (LLVMValueRef arg1) { return LLVMGetNextGlobalAlias(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2189c193f4734dde (LLVMValueRef arg1) { return LLVMGetPreviousGlobalAlias(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_da07743384b52343 (LLVMValueRef arg1) { return LLVMAliasGetAliasee(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_1f1285d7eb86ad88 (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMAliasSetAliasee(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_ca075570966d4a71 (LLVMValueRef arg1) { LLVMDeleteFunction(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_3db773fac6d1e0be (LLVMValueRef arg1) { return LLVMHasPersonalityFn(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_93e45136f168b8f7 (LLVMValueRef arg1) { return LLVMGetPersonalityFn(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_d706ed1eb309d23f (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetPersonalityFn(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_95a458fe969f89b5 (char *arg1, size_t arg2) { return LLVMLookupIntrinsicID(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_c3f90de1017ffb50 (LLVMValueRef arg1) { return LLVMGetIntrinsicID(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b933b652895f0f08 (LLVMModuleRef arg1, unsigned int arg2, LLVMTypeRef *arg3, size_t arg4) { return LLVMGetIntrinsicDeclaration(arg1, arg2, arg3, arg4); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_af4ff83f902f0c03 (LLVMContextRef arg1, unsigned int arg2, LLVMTypeRef *arg3, size_t arg4) { return LLVMIntrinsicGetType(arg1, arg2, arg3, arg4); }\nchar *hs_bindgen_LlvmC_Raw_Core_9d9d1344497770bf (unsigned int arg1, size_t *arg2) { return LLVMIntrinsicGetName(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_eec3ab68a8419ba3 (unsigned int arg1, LLVMTypeRef *arg2, size_t arg3, size_t *arg4) { return LLVMIntrinsicCopyOverloadedName(arg1, arg2, arg3, arg4); }\nchar *hs_bindgen_LlvmC_Raw_Core_92e697c6cbbb6b91 (LLVMModuleRef arg1, unsigned int arg2, LLVMTypeRef *arg3, size_t arg4, size_t *arg5) { return LLVMIntrinsicCopyOverloadedName2(arg1, arg2, arg3, arg4, arg5); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_64a2b93f760180e5 (unsigned int arg1) { return LLVMIntrinsicIsOverloaded(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d9759510b28a2957 (LLVMValueRef arg1) { return LLVMGetFunctionCallConv(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4ad0b2920a8d06c6 (LLVMValueRef arg1, unsigned int arg2) { LLVMSetFunctionCallConv(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Core_586c6781c74db06c (LLVMValueRef arg1) { return LLVMGetGC(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_a793c3f8a8a70189 (LLVMValueRef arg1, char *arg2) { LLVMSetGC(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6af5b4865bc4e408 (LLVMValueRef arg1) { return LLVMGetPrefixData(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_2d316301bf8e2be3 (LLVMValueRef arg1) { return LLVMHasPrefixData(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_9941cc08beb73ad9 (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetPrefixData(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b0fa3210bf612b72 (LLVMValueRef arg1) { return LLVMGetPrologueData(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_5785b8178e777b69 (LLVMValueRef arg1) { return LLVMHasPrologueData(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_9818d3592abf56ba (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetPrologueData(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_5d0a271fd82aa638 (LLVMValueRef arg1, LLVMAttributeIndex arg2, LLVMAttributeRef arg3) { LLVMAddAttributeAtIndex(arg1, arg2, arg3); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_e59b3ce7a1452c58 (LLVMValueRef arg1, LLVMAttributeIndex arg2) { return LLVMGetAttributeCountAtIndex(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_50b2297d0f89a550 (LLVMValueRef arg1, LLVMAttributeIndex arg2, LLVMAttributeRef *arg3) { LLVMGetAttributesAtIndex(arg1, arg2, arg3); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_5cde0d1ca4d4ce73 (LLVMValueRef arg1, LLVMAttributeIndex arg2, unsigned int arg3) { return LLVMGetEnumAttributeAtIndex(arg1, arg2, arg3); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_39b770b39e58c4ad (LLVMValueRef arg1, LLVMAttributeIndex arg2, char *arg3, unsigned int arg4) { return LLVMGetStringAttributeAtIndex(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Core_b66c7cbce40cf56c (LLVMValueRef arg1, LLVMAttributeIndex arg2, unsigned int arg3) { LLVMRemoveEnumAttributeAtIndex(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_7e42e94d44a29e28 (LLVMValueRef arg1, LLVMAttributeIndex arg2, char *arg3, unsigned int arg4) { LLVMRemoveStringAttributeAtIndex(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Core_0dd5e2d357517413 (LLVMValueRef arg1, char *arg2, char *arg3) { LLVMAddTargetDependentFunctionAttr(arg1, arg2, arg3); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_28501baf0bdc3b47 (LLVMValueRef arg1) { return LLVMCountParams(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_9faf1968f9cf86db (LLVMValueRef arg1, LLVMValueRef *arg2) { LLVMGetParams(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6628bbab070a58a8 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetParam(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4ceb1ff5b83b74f3 (LLVMValueRef arg1) { return LLVMGetParamParent(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a0169a1aa0eb57ce (LLVMValueRef arg1) { return LLVMGetFirstParam(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_86757ba56825e78c (LLVMValueRef arg1) { return LLVMGetLastParam(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e3202f6cad386149 (LLVMValueRef arg1) { return LLVMGetNextParam(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6435b441c8bc26a5 (LLVMValueRef arg1) { return LLVMGetPreviousParam(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_c7876cf8e3d28ee7 (LLVMValueRef arg1, unsigned int arg2) { LLVMSetParamAlignment(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_42594e0c518fc409 (LLVMModuleRef arg1, char *arg2, size_t arg3, LLVMTypeRef arg4, unsigned int arg5, LLVMValueRef arg6) { return LLVMAddGlobalIFunc(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7cb876fe578b6720 (LLVMModuleRef arg1, char *arg2, size_t arg3) { return LLVMGetNamedGlobalIFunc(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cf1e1d180ae62318 (LLVMModuleRef arg1) { return LLVMGetFirstGlobalIFunc(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3b3e9f5e7ef47667 (LLVMModuleRef arg1) { return LLVMGetLastGlobalIFunc(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_df26490d2fc2e1a4 (LLVMValueRef arg1) { return LLVMGetNextGlobalIFunc(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9a4193523a20973d (LLVMValueRef arg1) { return LLVMGetPreviousGlobalIFunc(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f8bccc0a9f9d5939 (LLVMValueRef arg1) { return LLVMGetGlobalIFuncResolver(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_55b07f7853fbb81f (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetGlobalIFuncResolver(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_dd0f5d9d3789098e (LLVMValueRef arg1) { LLVMEraseGlobalIFunc(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_74528152d3585c97 (LLVMValueRef arg1) { LLVMRemoveGlobalIFunc(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_065ea37750a748fa (LLVMContextRef arg1, char *arg2, size_t arg3) { return LLVMMDStringInContext2(arg1, arg2, arg3); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_cdaa8984f26ab3bc (LLVMContextRef arg1, LLVMMetadataRef *arg2, size_t arg3) { return LLVMMDNodeInContext2(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9cef587073f6eae1 (LLVMContextRef arg1, LLVMMetadataRef arg2) { return LLVMMetadataAsValue(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_c234653b5244073a (LLVMValueRef arg1) { return LLVMValueAsMetadata(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_d36718d80de80d14 (LLVMValueRef arg1, unsigned int *arg2) { return LLVMGetMDString(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_0e79e43f7411053d (LLVMValueRef arg1) { return LLVMGetMDNodeNumOperands(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_76d203b6b254448e (LLVMValueRef arg1, LLVMValueRef *arg2) { LLVMGetMDNodeOperands(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_53a56672f1144046 (LLVMValueRef arg1, unsigned int arg2, LLVMMetadataRef arg3) { LLVMReplaceMDNodeOperandWith(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_65ba968aca6561c9 (LLVMContextRef arg1, char *arg2, unsigned int arg3) { return LLVMMDStringInContext(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_31b7e57012d86650 (char *arg1, unsigned int arg2) { return LLVMMDString(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6e0aaa7377dfee90 (LLVMContextRef arg1, LLVMValueRef *arg2, unsigned int arg3) { return LLVMMDNodeInContext(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ac9689b684cc9ab6 (LLVMValueRef *arg1, unsigned int arg2) { return LLVMMDNode(arg1, arg2); }\nLLVMOperandBundleRef hs_bindgen_LlvmC_Raw_Core_3a357528457413b9 (char *arg1, size_t arg2, LLVMValueRef *arg3, unsigned int arg4) { return LLVMCreateOperandBundle(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Core_800e61b0d63495bc (LLVMOperandBundleRef arg1) { LLVMDisposeOperandBundle(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_3f5dc1971561f683 (LLVMOperandBundleRef arg1, size_t *arg2) { return LLVMGetOperandBundleTag(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_7d471aa962c59f66 (LLVMOperandBundleRef arg1) { return LLVMGetNumOperandBundleArgs(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0c3018e06392f68b (LLVMOperandBundleRef arg1, unsigned int arg2) { return LLVMGetOperandBundleArgAtIndex(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f744a9d55578fdbd (LLVMBasicBlockRef arg1) { return LLVMBasicBlockAsValue(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_00ab3ff6293a05d0 (LLVMValueRef arg1) { return LLVMValueIsBasicBlock(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_f4af41e81fce4de9 (LLVMValueRef arg1) { return LLVMValueAsBasicBlock(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Core_53576b191565cfad (LLVMBasicBlockRef arg1) { return LLVMGetBasicBlockName(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3d4bfd21345463a5 (LLVMBasicBlockRef arg1) { return LLVMGetBasicBlockParent(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b2b95e4509d8c019 (LLVMBasicBlockRef arg1) { return LLVMGetBasicBlockTerminator(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d868c01183de77cc (LLVMValueRef arg1) { return LLVMCountBasicBlocks(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4877809763f3196e (LLVMValueRef arg1, LLVMBasicBlockRef *arg2) { LLVMGetBasicBlocks(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_dcb6bf6ac5a05b10 (LLVMValueRef arg1) { return LLVMGetFirstBasicBlock(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_95b6b22fbec1acd6 (LLVMValueRef arg1) { return LLVMGetLastBasicBlock(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_42f6a4edc6cecd7b (LLVMBasicBlockRef arg1) { return LLVMGetNextBasicBlock(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_693b4a012e63f54b (LLVMBasicBlockRef arg1) { return LLVMGetPreviousBasicBlock(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_c8b71174fd6c3451 (LLVMValueRef arg1) { return LLVMGetEntryBasicBlock(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_ae6ea771f3d60964 (LLVMBuilderRef arg1, LLVMBasicBlockRef arg2) { LLVMInsertExistingBasicBlockAfterInsertBlock(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_de78078738ae0787 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { LLVMAppendExistingBasicBlock(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_0ee960f878a4e207 (LLVMContextRef arg1, char *arg2) { return LLVMCreateBasicBlockInContext(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_03f817b3a6ca9324 (LLVMContextRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMAppendBasicBlockInContext(arg1, arg2, arg3); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_9676c4627f4d4ab7 (LLVMValueRef arg1, char *arg2) { return LLVMAppendBasicBlock(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_d8d9338148f77185 (LLVMContextRef arg1, LLVMBasicBlockRef arg2, char *arg3) { return LLVMInsertBasicBlockInContext(arg1, arg2, arg3); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_f5742313815c2402 (LLVMBasicBlockRef arg1, char *arg2) { return LLVMInsertBasicBlock(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_7425c5388647ae2e (LLVMBasicBlockRef arg1) { LLVMDeleteBasicBlock(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_ad87a06d0e0e5535 (LLVMBasicBlockRef arg1) { LLVMRemoveBasicBlockFromParent(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_e896df6a6808549a (LLVMBasicBlockRef arg1, LLVMBasicBlockRef arg2) { LLVMMoveBasicBlockBefore(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_0854c728c6320b6a (LLVMBasicBlockRef arg1, LLVMBasicBlockRef arg2) { LLVMMoveBasicBlockAfter(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_558fee18c06332e0 (LLVMBasicBlockRef arg1) { return LLVMGetFirstInstruction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_06ab487fae1cb9f8 (LLVMBasicBlockRef arg1) { return LLVMGetLastInstruction(arg1); }\nsigned int hs_bindgen_LlvmC_Raw_Core_41dce98bd6aca2af (LLVMValueRef arg1) { return LLVMHasMetadata(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ef82aa0a71f9b75e (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetMetadata(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_179b7e139066f223 (LLVMValueRef arg1, unsigned int arg2, LLVMValueRef arg3) { LLVMSetMetadata(arg1, arg2, arg3); }\nLLVMValueMetadataEntry *hs_bindgen_LlvmC_Raw_Core_0808868eca5c7a3a (LLVMValueRef arg1, size_t *arg2) { return LLVMInstructionGetAllMetadataOtherThanDebugLoc(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_849a63d461b40fd3 (LLVMValueRef arg1) { return LLVMGetInstructionParent(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_043ce7ac1bbb24bd (LLVMValueRef arg1) { return LLVMGetNextInstruction(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2129d9c7f6461dd2 (LLVMValueRef arg1) { return LLVMGetPreviousInstruction(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_a25bfe5504a269d2 (LLVMValueRef arg1) { LLVMInstructionRemoveFromParent(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_1e521b9d49b6fef4 (LLVMValueRef arg1) { LLVMInstructionEraseFromParent(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4cec2095dc4318db (LLVMValueRef arg1) { LLVMDeleteInstruction(arg1); }\nLLVMOpcode hs_bindgen_LlvmC_Raw_Core_53561d8e9a27ff4a (LLVMValueRef arg1) { return LLVMGetInstructionOpcode(arg1); }\nLLVMIntPredicate hs_bindgen_LlvmC_Raw_Core_ddc537c097c921c1 (LLVMValueRef arg1) { return LLVMGetICmpPredicate(arg1); }\nLLVMRealPredicate hs_bindgen_LlvmC_Raw_Core_b9c63ef6620e9f03 (LLVMValueRef arg1) { return LLVMGetFCmpPredicate(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_74d56cbf53b9c711 (LLVMValueRef arg1) { return LLVMInstructionClone(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d7985fb75a1bc6ac (LLVMValueRef arg1) { return LLVMIsATerminatorInst(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_109f3ed805cc4a2c (LLVMValueRef arg1) { return LLVMGetNumArgOperands(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_03f6e383fc89adbe (LLVMValueRef arg1, unsigned int arg2) { LLVMSetInstructionCallConv(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_026534c3e046d6d0 (LLVMValueRef arg1) { return LLVMGetInstructionCallConv(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_dbf522754a8480be (LLVMValueRef arg1, LLVMAttributeIndex arg2, unsigned int arg3) { LLVMSetInstrParamAlignment(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_91a288dd88cf9609 (LLVMValueRef arg1, LLVMAttributeIndex arg2, LLVMAttributeRef arg3) { LLVMAddCallSiteAttribute(arg1, arg2, arg3); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_6fc08a9feec65346 (LLVMValueRef arg1, LLVMAttributeIndex arg2) { return LLVMGetCallSiteAttributeCount(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_90ea0e9cb7630aad (LLVMValueRef arg1, LLVMAttributeIndex arg2, LLVMAttributeRef *arg3) { LLVMGetCallSiteAttributes(arg1, arg2, arg3); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_00161941bc7334ed (LLVMValueRef arg1, LLVMAttributeIndex arg2, unsigned int arg3) { return LLVMGetCallSiteEnumAttribute(arg1, arg2, arg3); }\nLLVMAttributeRef hs_bindgen_LlvmC_Raw_Core_64eaa8c3dd2f887c (LLVMValueRef arg1, LLVMAttributeIndex arg2, char *arg3, unsigned int arg4) { return LLVMGetCallSiteStringAttribute(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Core_9efa3a24e0e365e8 (LLVMValueRef arg1, LLVMAttributeIndex arg2, unsigned int arg3) { LLVMRemoveCallSiteEnumAttribute(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_6e586b7b9711840a (LLVMValueRef arg1, LLVMAttributeIndex arg2, char *arg3, unsigned int arg4) { LLVMRemoveCallSiteStringAttribute(arg1, arg2, arg3, arg4); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_42a37773d3e2187c (LLVMValueRef arg1) { return LLVMGetCalledFunctionType(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2ab0172af8808ebd (LLVMValueRef arg1) { return LLVMGetCalledValue(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_e4c9ccb2ee9e076c (LLVMValueRef arg1) { return LLVMGetNumOperandBundles(arg1); }\nLLVMOperandBundleRef hs_bindgen_LlvmC_Raw_Core_b83194ae3b84465d (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetOperandBundleAtIndex(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_4f0a291f7a41c9be (LLVMValueRef arg1) { return LLVMIsTailCall(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_ece03577efebab76 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetTailCall(arg1, arg2); }\nLLVMTailCallKind hs_bindgen_LlvmC_Raw_Core_fb031a68e54ddc8e (LLVMValueRef arg1) { return LLVMGetTailCallKind(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_cfb5c9a12860cd93 (LLVMValueRef arg1, LLVMTailCallKind arg2) { LLVMSetTailCallKind(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_dcf566ecaff920f5 (LLVMValueRef arg1) { return LLVMGetNormalDest(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_f0398d6b213479ed (LLVMValueRef arg1) { return LLVMGetUnwindDest(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_8a432b71271d6dd9 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { LLVMSetNormalDest(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_aaffc61b434e10e5 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { LLVMSetUnwindDest(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_52a6f15727ccd2b0 (LLVMValueRef arg1) { return LLVMGetCallBrDefaultDest(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_393abadc7633580c (LLVMValueRef arg1) { return LLVMGetCallBrNumIndirectDests(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_48947787134ea08b (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetCallBrIndirectDest(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_294495d191927c85 (LLVMValueRef arg1) { return LLVMGetNumSuccessors(arg1); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_f5b65efe65518929 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetSuccessor(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_3352be654c5d9c8e (LLVMValueRef arg1, unsigned int arg2, LLVMBasicBlockRef arg3) { LLVMSetSuccessor(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_927c538bca435149 (LLVMValueRef arg1) { return LLVMIsConditional(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fb3ffdc7783cb43c (LLVMValueRef arg1) { return LLVMGetCondition(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_5ac68299ab3f205d (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetCondition(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_485e79c39015ed8b (LLVMValueRef arg1) { return LLVMGetSwitchDefaultDest(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_08e8e6e7269e46fa (LLVMValueRef arg1) { return LLVMGetAllocatedType(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_ea195328ce0f69f5 (LLVMValueRef arg1) { return LLVMIsInBounds(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_0248a0d510aa6631 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetIsInBounds(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Core_fb05c6bf9535fd94 (LLVMValueRef arg1) { return LLVMGetGEPSourceElementType(arg1); }\nLLVMGEPNoWrapFlags hs_bindgen_LlvmC_Raw_Core_d2c4dc26b152c64a (LLVMValueRef arg1) { return LLVMGEPGetNoWrapFlags(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_a1aebcf4671a8868 (LLVMValueRef arg1, LLVMGEPNoWrapFlags arg2) { LLVMGEPSetNoWrapFlags(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_d49e3423586d215a (LLVMValueRef arg1, LLVMValueRef *arg2, LLVMBasicBlockRef *arg3, unsigned int arg4) { LLVMAddIncoming(arg1, arg2, arg3, arg4); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d766a5b11252f220 (LLVMValueRef arg1) { return LLVMCountIncoming(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_abac6210e7528a1d (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetIncomingValue(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_6ab3a8c16be589ad (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetIncomingBlock(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_dbf17899e24af082 (LLVMValueRef arg1) { return LLVMGetNumIndices(arg1); }\nunsigned int *hs_bindgen_LlvmC_Raw_Core_b8b0223806e50a09 (LLVMValueRef arg1) { return LLVMGetIndices(arg1); }\nLLVMBuilderRef hs_bindgen_LlvmC_Raw_Core_c569c2c67a56a1fd (LLVMContextRef arg1) { return LLVMCreateBuilderInContext(arg1); }\nLLVMBuilderRef hs_bindgen_LlvmC_Raw_Core_843f37f9d6106bb8 (void) { return LLVMCreateBuilder(); }\nvoid hs_bindgen_LlvmC_Raw_Core_244b46ac8e56b7b9 (LLVMBuilderRef arg1, LLVMBasicBlockRef arg2, LLVMValueRef arg3) { LLVMPositionBuilder(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_ed151682b3996383 (LLVMBuilderRef arg1, LLVMBasicBlockRef arg2, LLVMValueRef arg3) { LLVMPositionBuilderBeforeDbgRecords(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_1a76e85cc468ab0a (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMPositionBuilderBefore(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_f04218b15eb51b0b (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMPositionBuilderBeforeInstrAndDbgRecords(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_8f92d748f0b73f5a (LLVMBuilderRef arg1, LLVMBasicBlockRef arg2) { LLVMPositionBuilderAtEnd(arg1, arg2); }\nLLVMBasicBlockRef hs_bindgen_LlvmC_Raw_Core_9b3d8831f416dc6c (LLVMBuilderRef arg1) { return LLVMGetInsertBlock(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_fc3a137466fd5e4f (LLVMBuilderRef arg1) { LLVMClearInsertionPosition(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_c0122eee6510c727 (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMInsertIntoBuilder(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_ec62e7a065aaebf6 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { LLVMInsertIntoBuilderWithName(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_ff90b921dc8486c8 (LLVMBuilderRef arg1) { LLVMDisposeBuilder(arg1); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_eeb4fb6e93262d96 (LLVMBuilderRef arg1) { return LLVMGetCurrentDebugLocation2(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4a4e25b6db15c8b2 (LLVMBuilderRef arg1, LLVMMetadataRef arg2) { LLVMSetCurrentDebugLocation2(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_567da7b4bc1ed0cb (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMSetInstDebugLocation(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_28351862e74a5113 (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMAddMetadataToInst(arg1, arg2); }\nLLVMMetadataRef hs_bindgen_LlvmC_Raw_Core_597699c997b3c9df (LLVMBuilderRef arg1) { return LLVMBuilderGetDefaultFPMathTag(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_3b768efb0750bb29 (LLVMBuilderRef arg1, LLVMMetadataRef arg2) { LLVMBuilderSetDefaultFPMathTag(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_5f1d18caa017e0d5 (LLVMBuilderRef arg1, LLVMValueRef arg2) { LLVMSetCurrentDebugLocation(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_8ff54557f0e5a944 (LLVMBuilderRef arg1) { return LLVMGetCurrentDebugLocation(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_325efb3a07aeb128 (LLVMBuilderRef arg1) { return LLVMBuildRetVoid(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d08a10eca7bb99fb (LLVMBuilderRef arg1, LLVMValueRef arg2) { return LLVMBuildRet(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_6eb9d0d8ba63ef90 (LLVMBuilderRef arg1, LLVMValueRef *arg2, unsigned int arg3) { return LLVMBuildAggregateRet(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3cc88f79d6240bfe (LLVMBuilderRef arg1, LLVMBasicBlockRef arg2) { return LLVMBuildBr(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cb143e559105c68b (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3, LLVMBasicBlockRef arg4) { return LLVMBuildCondBr(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_88cf88935f2556a8 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3, unsigned int arg4) { return LLVMBuildSwitch(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2af79ecdbafaa96e (LLVMBuilderRef arg1, LLVMValueRef arg2, unsigned int arg3) { return LLVMBuildIndirectBr(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_201662f4b9cd0537 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMBasicBlockRef arg4, LLVMBasicBlockRef *arg5, unsigned int arg6, LLVMValueRef *arg7, unsigned int arg8, LLVMOperandBundleRef *arg9, unsigned int arg10, char *arg11) { return LLVMBuildCallBr(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10, arg11); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_842346fb62c01943 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, LLVMBasicBlockRef arg6, LLVMBasicBlockRef arg7, char *arg8) { return LLVMBuildInvoke2(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_729af12eeef24f18 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, LLVMBasicBlockRef arg6, LLVMBasicBlockRef arg7, LLVMOperandBundleRef *arg8, unsigned int arg9, char *arg10) { return LLVMBuildInvokeWithOperandBundles(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8, arg9, arg10); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_333988f2e3450c43 (LLVMBuilderRef arg1) { return LLVMBuildUnreachable(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_04e448541569ef7f (LLVMBuilderRef arg1, LLVMValueRef arg2) { return LLVMBuildResume(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cdfd371a8a1a6587 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, unsigned int arg4, char *arg5) { return LLVMBuildLandingPad(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e26de1581b7214c1 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3) { return LLVMBuildCleanupRet(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_8751efb9234f5c5e (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3) { return LLVMBuildCatchRet(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0051c09e15fa56cb (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef *arg3, unsigned int arg4, char *arg5) { return LLVMBuildCatchPad(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0b596d553b7ff700 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef *arg3, unsigned int arg4, char *arg5) { return LLVMBuildCleanupPad(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2c8772cc71dbc292 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3, unsigned int arg4, char *arg5) { return LLVMBuildCatchSwitch(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_Core_624111495f97a907 (LLVMValueRef arg1, LLVMValueRef arg2, LLVMBasicBlockRef arg3) { LLVMAddCase(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Core_1865906a479681f3 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { LLVMAddDestination(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_e822e3b9475aebe2 (LLVMValueRef arg1) { return LLVMGetNumClauses(arg1); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_25cb5d9e236228b7 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetClause(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_1eff582d7a9f0ac4 (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMAddClause(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_7eeec7ddfad59b1f (LLVMValueRef arg1) { return LLVMIsCleanup(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_600e8f135db0044b (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetCleanup(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_f58f63393c923653 (LLVMValueRef arg1, LLVMBasicBlockRef arg2) { LLVMAddHandler(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_82f547d4ee424e8f (LLVMValueRef arg1) { return LLVMGetNumHandlers(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_f1c6c682e68be3f1 (LLVMValueRef arg1, LLVMBasicBlockRef *arg2) { LLVMGetHandlers(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ee6878a7bfcfbeb1 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetArgOperand(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Core_26f1bf6b6d074d3c (LLVMValueRef arg1, unsigned int arg2, LLVMValueRef arg3) { LLVMSetArgOperand(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_40b8b751ac5ec18d (LLVMValueRef arg1) { return LLVMGetParentCatchSwitch(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_0037aa1dbb43f2d1 (LLVMValueRef arg1, LLVMValueRef arg2) { LLVMSetParentCatchSwitch(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0dcc6b09937cb05e (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildAdd(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ccb289d54de75229 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNSWAdd(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e049bd7d6d8b73b5 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNUWAdd(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b8cfe58f7937b990 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildFAdd(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e289e75b0e2aa58a (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildSub(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_21cf8bf5da366b70 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNSWSub(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a6995596c6a76185 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNUWSub(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_dddbfbb144a76c78 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildFSub(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_8e963dd25412fe6d (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildMul(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1757eed728974cab (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNSWMul(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_43ac4dc258dfb231 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildNUWMul(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fa8297838021149f (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildFMul(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_cc21b2c74a1b88a0 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildUDiv(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ef7f2523fb06c256 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildExactUDiv(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3e407169ab75322f (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildSDiv(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c822c620ce2061ea (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildExactSDiv(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_360127de42034b14 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildFDiv(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_aac3d2ca75de39f1 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildURem(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_763372ef455d4e7a (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildSRem(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d67c529000984ff4 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildFRem(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_96934186c80667cc (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildShl(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4cbe1ade8e0324f3 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildLShr(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ab9212590b99447c (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildAShr(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_dc6761ce5285c498 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildAnd(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ac18de78f76e53ca (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildOr(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9201833edc8056f3 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildXor(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2169c42d262a8f46 (LLVMBuilderRef arg1, LLVMOpcode arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildBinOp(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_14330cfec8bee4e8 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildNeg(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_08359b3f8159eb39 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildNSWNeg(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d812b26a7f1476f2 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildNUWNeg(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ee636ef711b1ea35 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildFNeg(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b433897a818efdca (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildNot(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_a82611cc68e67094 (LLVMValueRef arg1) { return LLVMGetNUW(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_0cbc06a85c4253fe (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetNUW(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_a43c6653450c2fb8 (LLVMValueRef arg1) { return LLVMGetNSW(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_b28e767daa13a883 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetNSW(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_531818db083da26d (LLVMValueRef arg1) { return LLVMGetExact(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_369750e3b54cd5a0 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetExact(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_ac32991ae4505b76 (LLVMValueRef arg1) { return LLVMGetNNeg(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_dd9782c6008fadfd (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetNNeg(arg1, arg2); }\nLLVMFastMathFlags hs_bindgen_LlvmC_Raw_Core_c3b8e1e358b402a5 (LLVMValueRef arg1) { return LLVMGetFastMathFlags(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_d196b883f2240889 (LLVMValueRef arg1, LLVMFastMathFlags arg2) { LLVMSetFastMathFlags(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_f51ddb0a0bcc013b (LLVMValueRef arg1) { return LLVMCanValueUseFastMathFlags(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_92881b4629119435 (LLVMValueRef arg1) { return LLVMGetIsDisjoint(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_884ff60905732e85 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetIsDisjoint(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_52792f6fc7f3f48c (LLVMBuilderRef arg1, LLVMTypeRef arg2, char *arg3) { return LLVMBuildMalloc(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_4c17f03cd6470ae5 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildArrayMalloc(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a5bd0922c385ae1f (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, unsigned int arg5) { return LLVMBuildMemSet(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_a23f8bdac4c2052e (LLVMBuilderRef arg1, LLVMValueRef arg2, unsigned int arg3, LLVMValueRef arg4, unsigned int arg5, LLVMValueRef arg6) { return LLVMBuildMemCpy(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7fe4adf90f6e4211 (LLVMBuilderRef arg1, LLVMValueRef arg2, unsigned int arg3, LLVMValueRef arg4, unsigned int arg5, LLVMValueRef arg6) { return LLVMBuildMemMove(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_31fcc31371fa1948 (LLVMBuilderRef arg1, LLVMTypeRef arg2, char *arg3) { return LLVMBuildAlloca(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_666a355e2dfb0ff0 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildArrayAlloca(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3ec2c9d38799806d (LLVMBuilderRef arg1, LLVMValueRef arg2) { return LLVMBuildFree(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7e864a9307b5d4df (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildLoad2(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7b110c2acb2747d3 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3) { return LLVMBuildStore(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_192779ee468424a7 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, char *arg6) { return LLVMBuildGEP2(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e55144b722df4050 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, char *arg6) { return LLVMBuildInBoundsGEP2(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0e87c4058347c660 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, char *arg6, LLVMGEPNoWrapFlags arg7) { return LLVMBuildGEPWithNoWrapFlags(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_5f43c372159f995f (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, unsigned int arg4, char *arg5) { return LLVMBuildStructGEP2(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fa667a4fd7ab2967 (LLVMBuilderRef arg1, char *arg2, char *arg3) { return LLVMBuildGlobalString(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e6a98b746e50f0ef (LLVMBuilderRef arg1, char *arg2, char *arg3) { return LLVMBuildGlobalStringPtr(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_a315d01d7f4fe85b (LLVMValueRef arg1) { return LLVMGetVolatile(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4daf5a46d6de4bca (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetVolatile(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_725b05468ae49a6c (LLVMValueRef arg1) { return LLVMGetWeak(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_4a4bb4123e920536 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetWeak(arg1, arg2); }\nLLVMAtomicOrdering hs_bindgen_LlvmC_Raw_Core_ffb37cb280a33267 (LLVMValueRef arg1) { return LLVMGetOrdering(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_1182d20b1e52177a (LLVMValueRef arg1, LLVMAtomicOrdering arg2) { LLVMSetOrdering(arg1, arg2); }\nLLVMAtomicRMWBinOp hs_bindgen_LlvmC_Raw_Core_7e7c3c9705076f73 (LLVMValueRef arg1) { return LLVMGetAtomicRMWBinOp(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_c9e00df3eb6267ce (LLVMValueRef arg1, LLVMAtomicRMWBinOp arg2) { LLVMSetAtomicRMWBinOp(arg1, arg2); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3cf467f0742a264d (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildTrunc(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_c53cd680954d894e (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildZExt(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ae0d3d6c31dbd2aa (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildSExt(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3949fca4697a4ffa (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildFPToUI(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_2b8de607781909b3 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildFPToSI(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_80c46b09f2a6a0e8 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildUIToFP(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_536c0cae55b8f17c (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildSIToFP(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ab034615839bbddf (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildFPTrunc(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_b833e0f6759f2800 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildFPExt(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ef0c5d14ff34e7c0 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildPtrToInt(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_0ddd25b3a188c6a2 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildIntToPtr(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_94d27ff47e4d29a1 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildBitCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fbe1f98301b4865a (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildAddrSpaceCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ad645a13da2cfc34 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildZExtOrBitCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_9a2757f21ca1ec24 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildSExtOrBitCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_819041ac26b2a6b5 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildTruncOrBitCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_95d96719fd55dcc9 (LLVMBuilderRef arg1, LLVMOpcode arg2, LLVMValueRef arg3, LLVMTypeRef arg4, char *arg5) { return LLVMBuildCast(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_7acfdaf04d72c2c0 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildPointerCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f16281631d992ae6 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, LLVMBool arg4, char *arg5) { return LLVMBuildIntCast2(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_67e348107824f7d1 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildFPCast(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_066ac1af426404db (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildIntCast(arg1, arg2, arg3, arg4); }\nLLVMOpcode hs_bindgen_LlvmC_Raw_Core_abadb523dd883c16 (LLVMValueRef arg1, LLVMBool arg2, LLVMTypeRef arg3, LLVMBool arg4) { return LLVMGetCastOpcode(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3857d5fc396ca8a1 (LLVMBuilderRef arg1, LLVMIntPredicate arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildICmp(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d305171a5b5a3e32 (LLVMBuilderRef arg1, LLVMRealPredicate arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildFCmp(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_3e46f4863c463cba (LLVMBuilderRef arg1, LLVMTypeRef arg2, char *arg3) { return LLVMBuildPhi(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_50bda63288a943b4 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, char *arg6) { return LLVMBuildCall2(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_19118da636f83b60 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef *arg4, unsigned int arg5, LLVMOperandBundleRef *arg6, unsigned int arg7, char *arg8) { return LLVMBuildCallWithOperandBundles(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_845f3692c6d70f16 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildSelect(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_1b6ed73dda5328d8 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMTypeRef arg3, char *arg4) { return LLVMBuildVAArg(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_f61fa0514b09b62f (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, char *arg4) { return LLVMBuildExtractElement(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d0c583c6061c4c89 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildInsertElement(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_54e31949b22804fe (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildShuffleVector(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_d1d145fddf42a438 (LLVMBuilderRef arg1, LLVMValueRef arg2, unsigned int arg3, char *arg4) { return LLVMBuildExtractValue(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_504d1bc4a6217d27 (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, unsigned int arg4, char *arg5) { return LLVMBuildInsertValue(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ff1013ecd1a71d74 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildFreeze(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_007b5ac9933336fb (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildIsNull(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_669e66ba3bc8e642 (LLVMBuilderRef arg1, LLVMValueRef arg2, char *arg3) { return LLVMBuildIsNotNull(arg1, arg2, arg3); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_ce73263b8e75bb58 (LLVMBuilderRef arg1, LLVMTypeRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, char *arg5) { return LLVMBuildPtrDiff2(arg1, arg2, arg3, arg4, arg5); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_fc1a2c4084f519d2 (LLVMBuilderRef arg1, LLVMAtomicOrdering arg2, LLVMBool arg3, char *arg4) { return LLVMBuildFence(arg1, arg2, arg3, arg4); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_e941ffadc15c355e (LLVMBuilderRef arg1, LLVMAtomicRMWBinOp arg2, LLVMValueRef arg3, LLVMValueRef arg4, LLVMAtomicOrdering arg5, LLVMBool arg6) { return LLVMBuildAtomicRMW(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMValueRef hs_bindgen_LlvmC_Raw_Core_558848291a2679aa (LLVMBuilderRef arg1, LLVMValueRef arg2, LLVMValueRef arg3, LLVMValueRef arg4, LLVMAtomicOrdering arg5, LLVMAtomicOrdering arg6, LLVMBool arg7) { return LLVMBuildAtomicCmpXchg(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nunsigned int hs_bindgen_LlvmC_Raw_Core_d450ebe4bef70d15 (LLVMValueRef arg1) { return LLVMGetNumMaskElements(arg1); }\nsigned int hs_bindgen_LlvmC_Raw_Core_f721215878af6a85 (void) { return LLVMGetUndefMaskElem(); }\nsigned int hs_bindgen_LlvmC_Raw_Core_15329a12a80b7929 (LLVMValueRef arg1, unsigned int arg2) { return LLVMGetMaskValue(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_1a39dc74a1a0be3d (LLVMValueRef arg1) { return LLVMIsAtomicSingleThread(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_69065eb8cd0e7b53 (LLVMValueRef arg1, LLVMBool arg2) { LLVMSetAtomicSingleThread(arg1, arg2); }\nLLVMAtomicOrdering hs_bindgen_LlvmC_Raw_Core_98bb9e133646a940 (LLVMValueRef arg1) { return LLVMGetCmpXchgSuccessOrdering(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_fa98f838fdf3c762 (LLVMValueRef arg1, LLVMAtomicOrdering arg2) { LLVMSetCmpXchgSuccessOrdering(arg1, arg2); }\nLLVMAtomicOrdering hs_bindgen_LlvmC_Raw_Core_710308e58a8ab176 (LLVMValueRef arg1) { return LLVMGetCmpXchgFailureOrdering(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_945a173ce985b76d (LLVMValueRef arg1, LLVMAtomicOrdering arg2) { LLVMSetCmpXchgFailureOrdering(arg1, arg2); }\nLLVMModuleProviderRef hs_bindgen_LlvmC_Raw_Core_f8d9a0f182e5c7d6 (LLVMModuleRef arg1) { return LLVMCreateModuleProviderForExistingModule(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_15cade3b085564ea (LLVMModuleProviderRef arg1) { LLVMDisposeModuleProvider(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_bb6d2ae6549eb8c0 (char *arg1, LLVMMemoryBufferRef *arg2, char **arg3) { return LLVMCreateMemoryBufferWithContentsOfFile(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_26e2ed0f271c2e02 (LLVMMemoryBufferRef *arg1, char **arg2) { return LLVMCreateMemoryBufferWithSTDIN(arg1, arg2); }\nLLVMMemoryBufferRef hs_bindgen_LlvmC_Raw_Core_a7231fd877d6bb43 (char *arg1, size_t arg2, char *arg3, LLVMBool arg4) { return LLVMCreateMemoryBufferWithMemoryRange(arg1, arg2, arg3, arg4); }\nLLVMMemoryBufferRef hs_bindgen_LlvmC_Raw_Core_dbd4c8d10bd921b6 (char *arg1, size_t arg2, char *arg3) { return LLVMCreateMemoryBufferWithMemoryRangeCopy(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_Core_d75a6950e604e0e8 (LLVMMemoryBufferRef arg1) { return LLVMGetBufferStart(arg1); }\nsize_t hs_bindgen_LlvmC_Raw_Core_3ccf1d8ad2bac6aa (LLVMMemoryBufferRef arg1) { return LLVMGetBufferSize(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_563c1b8da589dd00 (LLVMMemoryBufferRef arg1) { LLVMDisposeMemoryBuffer(arg1); }\nLLVMPassManagerRef hs_bindgen_LlvmC_Raw_Core_885ed76658a29788 (void) { return LLVMCreatePassManager(); }\nLLVMPassManagerRef hs_bindgen_LlvmC_Raw_Core_2e384bff9f05324c (LLVMModuleRef arg1) { return LLVMCreateFunctionPassManagerForModule(arg1); }\nLLVMPassManagerRef hs_bindgen_LlvmC_Raw_Core_64c672d789861eed (LLVMModuleProviderRef arg1) { return LLVMCreateFunctionPassManager(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_b3b247c48d0fd4fc (LLVMPassManagerRef arg1, LLVMModuleRef arg2) { return LLVMRunPassManager(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_a3d26c7cd111f1b7 (LLVMPassManagerRef arg1) { return LLVMInitializeFunctionPassManager(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_d5cfd1926a6d2fa9 (LLVMPassManagerRef arg1, LLVMValueRef arg2) { return LLVMRunFunctionPassManager(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_4eeeb2cbd8257d9d (LLVMPassManagerRef arg1) { return LLVMFinalizeFunctionPassManager(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Core_c427c93c1f7ed6c8 (LLVMPassManagerRef arg1) { LLVMDisposePassManager(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_d2c64545ef0a5d40 (void) { return LLVMStartMultithreaded(); }\nvoid hs_bindgen_LlvmC_Raw_Core_09aa9c20ab5ebe85 (void) { LLVMStopMultithreaded(); }\nLLVMBool hs_bindgen_LlvmC_Raw_Core_34a9924e757d71c6 (void) { return LLVMIsMultithreaded(); }\n")

newtype ValueMetadataEntry = ValueMetadataEntry
  { un_ValueMetadataEntry :: LlvmC.Raw.Types.ValueMetadataEntry
  }

newtype ModuleFlagEntry = ModuleFlagEntry
  { un_ModuleFlagEntry :: LlvmC.Raw.Types.ModuleFlagEntry
  }

newtype Opcode = Opcode
  { un_Opcode :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Opcode where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Opcode
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Opcode un_Opcode2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Opcode2

instance HsBindgen.Runtime.CEnum.CEnum Opcode where

  type CEnumZ Opcode = FC.CUInt

  toCEnum = Opcode

  fromCEnum = un_Opcode

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (1, Data.List.NonEmpty.singleton "Ret")
                                                     , (2, Data.List.NonEmpty.singleton "Br")
                                                     , (3, Data.List.NonEmpty.singleton "Switch")
                                                     , (4, Data.List.NonEmpty.singleton "IndirectBr")
                                                     , (5, Data.List.NonEmpty.singleton "Invoke")
                                                     , (7, Data.List.NonEmpty.singleton "Unreachable")
                                                     , (8, Data.List.NonEmpty.singleton "Add")
                                                     , (9, Data.List.NonEmpty.singleton "FAdd")
                                                     , (10, Data.List.NonEmpty.singleton "Sub")
                                                     , (11, Data.List.NonEmpty.singleton "FSub")
                                                     , (12, Data.List.NonEmpty.singleton "Mul")
                                                     , (13, Data.List.NonEmpty.singleton "FMul")
                                                     , (14, Data.List.NonEmpty.singleton "UDiv")
                                                     , (15, Data.List.NonEmpty.singleton "SDiv")
                                                     , (16, Data.List.NonEmpty.singleton "FDiv")
                                                     , (17, Data.List.NonEmpty.singleton "URem")
                                                     , (18, Data.List.NonEmpty.singleton "SRem")
                                                     , (19, Data.List.NonEmpty.singleton "FRem")
                                                     , (20, Data.List.NonEmpty.singleton "Shl")
                                                     , (21, Data.List.NonEmpty.singleton "LShr")
                                                     , (22, Data.List.NonEmpty.singleton "AShr")
                                                     , (23, Data.List.NonEmpty.singleton "And")
                                                     , (24, Data.List.NonEmpty.singleton "Or")
                                                     , (25, Data.List.NonEmpty.singleton "Xor")
                                                     , (26, Data.List.NonEmpty.singleton "Alloca")
                                                     , (27, Data.List.NonEmpty.singleton "Load")
                                                     , (28, Data.List.NonEmpty.singleton "Store")
                                                     , (29, Data.List.NonEmpty.singleton "GetElementPtr")
                                                     , (30, Data.List.NonEmpty.singleton "Trunc")
                                                     , (31, Data.List.NonEmpty.singleton "ZExt")
                                                     , (32, Data.List.NonEmpty.singleton "SExt")
                                                     , (33, Data.List.NonEmpty.singleton "FPToUI")
                                                     , (34, Data.List.NonEmpty.singleton "FPToSI")
                                                     , (35, Data.List.NonEmpty.singleton "UIToFP")
                                                     , (36, Data.List.NonEmpty.singleton "SIToFP")
                                                     , (37, Data.List.NonEmpty.singleton "FPTrunc")
                                                     , (38, Data.List.NonEmpty.singleton "FPExt")
                                                     , (39, Data.List.NonEmpty.singleton "PtrToInt")
                                                     , (40, Data.List.NonEmpty.singleton "IntToPtr")
                                                     , (41, Data.List.NonEmpty.singleton "BitCast")
                                                     , (42, Data.List.NonEmpty.singleton "ICmp")
                                                     , (43, Data.List.NonEmpty.singleton "FCmp")
                                                     , (44, Data.List.NonEmpty.singleton "PHI")
                                                     , (45, Data.List.NonEmpty.singleton "Call")
                                                     , (46, Data.List.NonEmpty.singleton "Select")
                                                     , (47, Data.List.NonEmpty.singleton "UserOp1")
                                                     , (48, Data.List.NonEmpty.singleton "UserOp2")
                                                     , (49, Data.List.NonEmpty.singleton "VAArg")
                                                     , (50, Data.List.NonEmpty.singleton "ExtractElement")
                                                     , (51, Data.List.NonEmpty.singleton "InsertElement")
                                                     , (52, Data.List.NonEmpty.singleton "ShuffleVector")
                                                     , (53, Data.List.NonEmpty.singleton "ExtractValue")
                                                     , (54, Data.List.NonEmpty.singleton "InsertValue")
                                                     , (55, Data.List.NonEmpty.singleton "Fence")
                                                     , (56, Data.List.NonEmpty.singleton "AtomicCmpXchg")
                                                     , (57, Data.List.NonEmpty.singleton "AtomicRMW")
                                                     , (58, Data.List.NonEmpty.singleton "Resume")
                                                     , (59, Data.List.NonEmpty.singleton "LandingPad")
                                                     , (60, Data.List.NonEmpty.singleton "AddrSpaceCast")
                                                     , (61, Data.List.NonEmpty.singleton "CleanupRet")
                                                     , (62, Data.List.NonEmpty.singleton "CatchRet")
                                                     , (63, Data.List.NonEmpty.singleton "CatchPad")
                                                     , (64, Data.List.NonEmpty.singleton "CleanupPad")
                                                     , (65, Data.List.NonEmpty.singleton "CatchSwitch")
                                                     , (66, Data.List.NonEmpty.singleton "FNeg")
                                                     , (67, Data.List.NonEmpty.singleton "CallBr")
                                                     , (68, Data.List.NonEmpty.singleton "Freeze")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Opcode"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Opcode"

instance Show Opcode where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Opcode where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern Ret :: Opcode
pattern Ret = Opcode 1

pattern Br :: Opcode
pattern Br = Opcode 2

pattern Switch :: Opcode
pattern Switch = Opcode 3

pattern IndirectBr :: Opcode
pattern IndirectBr = Opcode 4

pattern Invoke :: Opcode
pattern Invoke = Opcode 5

pattern Unreachable :: Opcode
pattern Unreachable = Opcode 7

pattern CallBr :: Opcode
pattern CallBr = Opcode 67

pattern FNeg :: Opcode
pattern FNeg = Opcode 66

pattern Add :: Opcode
pattern Add = Opcode 8

pattern FAdd :: Opcode
pattern FAdd = Opcode 9

pattern Sub :: Opcode
pattern Sub = Opcode 10

pattern FSub :: Opcode
pattern FSub = Opcode 11

pattern Mul :: Opcode
pattern Mul = Opcode 12

pattern FMul :: Opcode
pattern FMul = Opcode 13

pattern UDiv :: Opcode
pattern UDiv = Opcode 14

pattern SDiv :: Opcode
pattern SDiv = Opcode 15

pattern FDiv :: Opcode
pattern FDiv = Opcode 16

pattern URem :: Opcode
pattern URem = Opcode 17

pattern SRem :: Opcode
pattern SRem = Opcode 18

pattern FRem :: Opcode
pattern FRem = Opcode 19

pattern Shl :: Opcode
pattern Shl = Opcode 20

pattern LShr :: Opcode
pattern LShr = Opcode 21

pattern AShr :: Opcode
pattern AShr = Opcode 22

pattern And :: Opcode
pattern And = Opcode 23

pattern Or :: Opcode
pattern Or = Opcode 24

pattern Xor :: Opcode
pattern Xor = Opcode 25

pattern Alloca :: Opcode
pattern Alloca = Opcode 26

pattern Load :: Opcode
pattern Load = Opcode 27

pattern Store :: Opcode
pattern Store = Opcode 28

pattern GetElementPtr :: Opcode
pattern GetElementPtr = Opcode 29

pattern Trunc :: Opcode
pattern Trunc = Opcode 30

pattern ZExt :: Opcode
pattern ZExt = Opcode 31

pattern SExt :: Opcode
pattern SExt = Opcode 32

pattern FPToUI :: Opcode
pattern FPToUI = Opcode 33

pattern FPToSI :: Opcode
pattern FPToSI = Opcode 34

pattern UIToFP :: Opcode
pattern UIToFP = Opcode 35

pattern SIToFP :: Opcode
pattern SIToFP = Opcode 36

pattern FPTrunc :: Opcode
pattern FPTrunc = Opcode 37

pattern FPExt :: Opcode
pattern FPExt = Opcode 38

pattern PtrToInt :: Opcode
pattern PtrToInt = Opcode 39

pattern IntToPtr :: Opcode
pattern IntToPtr = Opcode 40

pattern BitCast :: Opcode
pattern BitCast = Opcode 41

pattern AddrSpaceCast :: Opcode
pattern AddrSpaceCast = Opcode 60

pattern ICmp :: Opcode
pattern ICmp = Opcode 42

pattern FCmp :: Opcode
pattern FCmp = Opcode 43

pattern PHI :: Opcode
pattern PHI = Opcode 44

pattern Call :: Opcode
pattern Call = Opcode 45

pattern Select :: Opcode
pattern Select = Opcode 46

pattern UserOp1 :: Opcode
pattern UserOp1 = Opcode 47

pattern UserOp2 :: Opcode
pattern UserOp2 = Opcode 48

pattern VAArg :: Opcode
pattern VAArg = Opcode 49

pattern ExtractElement :: Opcode
pattern ExtractElement = Opcode 50

pattern InsertElement :: Opcode
pattern InsertElement = Opcode 51

pattern ShuffleVector :: Opcode
pattern ShuffleVector = Opcode 52

pattern ExtractValue :: Opcode
pattern ExtractValue = Opcode 53

pattern InsertValue :: Opcode
pattern InsertValue = Opcode 54

pattern Freeze :: Opcode
pattern Freeze = Opcode 68

pattern Fence :: Opcode
pattern Fence = Opcode 55

pattern AtomicCmpXchg :: Opcode
pattern AtomicCmpXchg = Opcode 56

pattern AtomicRMW :: Opcode
pattern AtomicRMW = Opcode 57

pattern Resume :: Opcode
pattern Resume = Opcode 58

pattern LandingPad :: Opcode
pattern LandingPad = Opcode 59

pattern CleanupRet :: Opcode
pattern CleanupRet = Opcode 61

pattern CatchRet :: Opcode
pattern CatchRet = Opcode 62

pattern CatchPad :: Opcode
pattern CatchPad = Opcode 63

pattern CleanupPad :: Opcode
pattern CleanupPad = Opcode 64

pattern CatchSwitch :: Opcode
pattern CatchSwitch = Opcode 65

newtype TypeKind = TypeKind
  { un_TypeKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable TypeKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure TypeKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          TypeKind un_TypeKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_TypeKind2

instance HsBindgen.Runtime.CEnum.CEnum TypeKind where

  type CEnumZ TypeKind = FC.CUInt

  toCEnum = TypeKind

  fromCEnum = un_TypeKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "VoidTypeKind")
                                                     , (1, Data.List.NonEmpty.singleton "HalfTypeKind")
                                                     , (2, Data.List.NonEmpty.singleton "FloatTypeKind")
                                                     , (3, Data.List.NonEmpty.singleton "DoubleTypeKind")
                                                     , (4, Data.List.NonEmpty.singleton "X86_FP80TypeKind")
                                                     , (5, Data.List.NonEmpty.singleton "FP128TypeKind")
                                                     , (6, Data.List.NonEmpty.singleton "PPC_FP128TypeKind")
                                                     , (7, Data.List.NonEmpty.singleton "LabelTypeKind")
                                                     , (8, Data.List.NonEmpty.singleton "IntegerTypeKind")
                                                     , (9, Data.List.NonEmpty.singleton "FunctionTypeKind")
                                                     , (10, Data.List.NonEmpty.singleton "StructTypeKind")
                                                     , (11, Data.List.NonEmpty.singleton "ArrayTypeKind")
                                                     , (12, Data.List.NonEmpty.singleton "PointerTypeKind")
                                                     , (13, Data.List.NonEmpty.singleton "VectorTypeKind")
                                                     , (14, Data.List.NonEmpty.singleton "MetadataTypeKind")
                                                     , (15, Data.List.NonEmpty.singleton "X86_MMXTypeKind")
                                                     , (16, Data.List.NonEmpty.singleton "TokenTypeKind")
                                                     , (17, Data.List.NonEmpty.singleton "ScalableVectorTypeKind")
                                                     , (18, Data.List.NonEmpty.singleton "BFloatTypeKind")
                                                     , (19, Data.List.NonEmpty.singleton "X86_AMXTypeKind")
                                                     , (20, Data.List.NonEmpty.singleton "TargetExtTypeKind")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "TypeKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "TypeKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum TypeKind where

  minDeclaredValue = VoidTypeKind

  maxDeclaredValue = TargetExtTypeKind

instance Show TypeKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read TypeKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern VoidTypeKind :: TypeKind
pattern VoidTypeKind = TypeKind 0

pattern HalfTypeKind :: TypeKind
pattern HalfTypeKind = TypeKind 1

pattern FloatTypeKind :: TypeKind
pattern FloatTypeKind = TypeKind 2

pattern DoubleTypeKind :: TypeKind
pattern DoubleTypeKind = TypeKind 3

pattern X86_FP80TypeKind :: TypeKind
pattern X86_FP80TypeKind = TypeKind 4

pattern FP128TypeKind :: TypeKind
pattern FP128TypeKind = TypeKind 5

pattern PPC_FP128TypeKind :: TypeKind
pattern PPC_FP128TypeKind = TypeKind 6

pattern LabelTypeKind :: TypeKind
pattern LabelTypeKind = TypeKind 7

pattern IntegerTypeKind :: TypeKind
pattern IntegerTypeKind = TypeKind 8

pattern FunctionTypeKind :: TypeKind
pattern FunctionTypeKind = TypeKind 9

pattern StructTypeKind :: TypeKind
pattern StructTypeKind = TypeKind 10

pattern ArrayTypeKind :: TypeKind
pattern ArrayTypeKind = TypeKind 11

pattern PointerTypeKind :: TypeKind
pattern PointerTypeKind = TypeKind 12

pattern VectorTypeKind :: TypeKind
pattern VectorTypeKind = TypeKind 13

pattern MetadataTypeKind :: TypeKind
pattern MetadataTypeKind = TypeKind 14

pattern X86_MMXTypeKind :: TypeKind
pattern X86_MMXTypeKind = TypeKind 15

pattern TokenTypeKind :: TypeKind
pattern TokenTypeKind = TypeKind 16

pattern ScalableVectorTypeKind :: TypeKind
pattern ScalableVectorTypeKind = TypeKind 17

pattern BFloatTypeKind :: TypeKind
pattern BFloatTypeKind = TypeKind 18

pattern X86_AMXTypeKind :: TypeKind
pattern X86_AMXTypeKind = TypeKind 19

pattern TargetExtTypeKind :: TypeKind
pattern TargetExtTypeKind = TypeKind 20

newtype Linkage = Linkage
  { un_Linkage :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Linkage where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Linkage
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Linkage un_Linkage2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Linkage2

instance HsBindgen.Runtime.CEnum.CEnum Linkage where

  type CEnumZ Linkage = FC.CUInt

  toCEnum = Linkage

  fromCEnum = un_Linkage

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "ExternalLinkage")
                                                     , (1, Data.List.NonEmpty.singleton "AvailableExternallyLinkage")
                                                     , (2, Data.List.NonEmpty.singleton "LinkOnceAnyLinkage")
                                                     , (3, Data.List.NonEmpty.singleton "LinkOnceODRLinkage")
                                                     , (4, Data.List.NonEmpty.singleton "LinkOnceODRAutoHideLinkage")
                                                     , (5, Data.List.NonEmpty.singleton "WeakAnyLinkage")
                                                     , (6, Data.List.NonEmpty.singleton "WeakODRLinkage")
                                                     , (7, Data.List.NonEmpty.singleton "AppendingLinkage")
                                                     , (8, Data.List.NonEmpty.singleton "InternalLinkage")
                                                     , (9, Data.List.NonEmpty.singleton "PrivateLinkage")
                                                     , (10, Data.List.NonEmpty.singleton "DLLImportLinkage")
                                                     , (11, Data.List.NonEmpty.singleton "DLLExportLinkage")
                                                     , (12, Data.List.NonEmpty.singleton "ExternalWeakLinkage")
                                                     , (13, Data.List.NonEmpty.singleton "GhostLinkage")
                                                     , (14, Data.List.NonEmpty.singleton "CommonLinkage")
                                                     , (15, Data.List.NonEmpty.singleton "LinkerPrivateLinkage")
                                                     , (16, Data.List.NonEmpty.singleton "LinkerPrivateWeakLinkage")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Linkage"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Linkage"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum Linkage where

  minDeclaredValue = ExternalLinkage

  maxDeclaredValue = LinkerPrivateWeakLinkage

instance Show Linkage where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Linkage where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern ExternalLinkage :: Linkage
pattern ExternalLinkage = Linkage 0

pattern AvailableExternallyLinkage :: Linkage
pattern AvailableExternallyLinkage = Linkage 1

pattern LinkOnceAnyLinkage :: Linkage
pattern LinkOnceAnyLinkage = Linkage 2

pattern LinkOnceODRLinkage :: Linkage
pattern LinkOnceODRLinkage = Linkage 3

pattern LinkOnceODRAutoHideLinkage :: Linkage
pattern LinkOnceODRAutoHideLinkage = Linkage 4

pattern WeakAnyLinkage :: Linkage
pattern WeakAnyLinkage = Linkage 5

pattern WeakODRLinkage :: Linkage
pattern WeakODRLinkage = Linkage 6

pattern AppendingLinkage :: Linkage
pattern AppendingLinkage = Linkage 7

pattern InternalLinkage :: Linkage
pattern InternalLinkage = Linkage 8

pattern PrivateLinkage :: Linkage
pattern PrivateLinkage = Linkage 9

pattern DLLImportLinkage :: Linkage
pattern DLLImportLinkage = Linkage 10

pattern DLLExportLinkage :: Linkage
pattern DLLExportLinkage = Linkage 11

pattern ExternalWeakLinkage :: Linkage
pattern ExternalWeakLinkage = Linkage 12

pattern GhostLinkage :: Linkage
pattern GhostLinkage = Linkage 13

pattern CommonLinkage :: Linkage
pattern CommonLinkage = Linkage 14

pattern LinkerPrivateLinkage :: Linkage
pattern LinkerPrivateLinkage = Linkage 15

pattern LinkerPrivateWeakLinkage :: Linkage
pattern LinkerPrivateWeakLinkage = Linkage 16

newtype Visibility = Visibility
  { un_Visibility :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Visibility where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Visibility
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Visibility un_Visibility2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Visibility2

instance HsBindgen.Runtime.CEnum.CEnum Visibility where

  type CEnumZ Visibility = FC.CUInt

  toCEnum = Visibility

  fromCEnum = un_Visibility

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DefaultVisibility")
                                                     , (1, Data.List.NonEmpty.singleton "HiddenVisibility")
                                                     , (2, Data.List.NonEmpty.singleton "ProtectedVisibility")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Visibility"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Visibility"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum Visibility where

  minDeclaredValue = DefaultVisibility

  maxDeclaredValue = ProtectedVisibility

instance Show Visibility where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Visibility where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DefaultVisibility :: Visibility
pattern DefaultVisibility = Visibility 0

pattern HiddenVisibility :: Visibility
pattern HiddenVisibility = Visibility 1

pattern ProtectedVisibility :: Visibility
pattern ProtectedVisibility = Visibility 2

newtype UnnamedAddr = UnnamedAddr
  { un_UnnamedAddr :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable UnnamedAddr where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure UnnamedAddr
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          UnnamedAddr un_UnnamedAddr2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_UnnamedAddr2

instance HsBindgen.Runtime.CEnum.CEnum UnnamedAddr where

  type CEnumZ UnnamedAddr = FC.CUInt

  toCEnum = UnnamedAddr

  fromCEnum = un_UnnamedAddr

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "NoUnnamedAddr")
                                                     , (1, Data.List.NonEmpty.singleton "LocalUnnamedAddr")
                                                     , (2, Data.List.NonEmpty.singleton "GlobalUnnamedAddr")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "UnnamedAddr"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "UnnamedAddr"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum UnnamedAddr where

  minDeclaredValue = NoUnnamedAddr

  maxDeclaredValue = GlobalUnnamedAddr

instance Show UnnamedAddr where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read UnnamedAddr where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern NoUnnamedAddr :: UnnamedAddr
pattern NoUnnamedAddr = UnnamedAddr 0

pattern LocalUnnamedAddr :: UnnamedAddr
pattern LocalUnnamedAddr = UnnamedAddr 1

pattern GlobalUnnamedAddr :: UnnamedAddr
pattern GlobalUnnamedAddr = UnnamedAddr 2

newtype DLLStorageClass = DLLStorageClass
  { un_DLLStorageClass :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DLLStorageClass where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DLLStorageClass
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DLLStorageClass un_DLLStorageClass2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DLLStorageClass2

instance HsBindgen.Runtime.CEnum.CEnum DLLStorageClass where

  type CEnumZ DLLStorageClass = FC.CUInt

  toCEnum = DLLStorageClass

  fromCEnum = un_DLLStorageClass

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DefaultStorageClass")
                                                     , (1, Data.List.NonEmpty.singleton "DLLImportStorageClass")
                                                     , (2, Data.List.NonEmpty.singleton "DLLExportStorageClass")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DLLStorageClass"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DLLStorageClass"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum DLLStorageClass where

  minDeclaredValue = DefaultStorageClass

  maxDeclaredValue = DLLExportStorageClass

instance Show DLLStorageClass where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DLLStorageClass where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DefaultStorageClass :: DLLStorageClass
pattern DefaultStorageClass = DLLStorageClass 0

pattern DLLImportStorageClass :: DLLStorageClass
pattern DLLImportStorageClass = DLLStorageClass 1

pattern DLLExportStorageClass :: DLLStorageClass
pattern DLLExportStorageClass = DLLStorageClass 2

newtype CallConv = CallConv
  { un_CallConv :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable CallConv where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure CallConv
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          CallConv un_CallConv2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_CallConv2

instance HsBindgen.Runtime.CEnum.CEnum CallConv where

  type CEnumZ CallConv = FC.CUInt

  toCEnum = CallConv

  fromCEnum = un_CallConv

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "CCallConv")
                                                     , (8, Data.List.NonEmpty.singleton "FastCallConv")
                                                     , (9, Data.List.NonEmpty.singleton "ColdCallConv")
                                                     , (10, Data.List.NonEmpty.singleton "GHCCallConv")
                                                     , (11, Data.List.NonEmpty.singleton "HiPECallConv")
                                                     , (13, Data.List.NonEmpty.singleton "AnyRegCallConv")
                                                     , (14, Data.List.NonEmpty.singleton "PreserveMostCallConv")
                                                     , (15, Data.List.NonEmpty.singleton "PreserveAllCallConv")
                                                     , (16, Data.List.NonEmpty.singleton "SwiftCallConv")
                                                     , (17, Data.List.NonEmpty.singleton "CXXFASTTLSCallConv")
                                                     , (64, Data.List.NonEmpty.singleton "X86StdcallCallConv")
                                                     , (65, Data.List.NonEmpty.singleton "X86FastcallCallConv")
                                                     , (66, Data.List.NonEmpty.singleton "ARMAPCSCallConv")
                                                     , (67, Data.List.NonEmpty.singleton "ARMAAPCSCallConv")
                                                     , (68, Data.List.NonEmpty.singleton "ARMAAPCSVFPCallConv")
                                                     , (69, Data.List.NonEmpty.singleton "MSP430INTRCallConv")
                                                     , (70, Data.List.NonEmpty.singleton "X86ThisCallCallConv")
                                                     , (71, Data.List.NonEmpty.singleton "PTXKernelCallConv")
                                                     , (72, Data.List.NonEmpty.singleton "PTXDeviceCallConv")
                                                     , (75, Data.List.NonEmpty.singleton "SPIRFUNCCallConv")
                                                     , (76, Data.List.NonEmpty.singleton "SPIRKERNELCallConv")
                                                     , (77, Data.List.NonEmpty.singleton "IntelOCLBICallConv")
                                                     , (78, Data.List.NonEmpty.singleton "X8664SysVCallConv")
                                                     , (79, Data.List.NonEmpty.singleton "Win64CallConv")
                                                     , (80, Data.List.NonEmpty.singleton "X86VectorCallCallConv")
                                                     , (81, Data.List.NonEmpty.singleton "HHVMCallConv")
                                                     , (82, Data.List.NonEmpty.singleton "HHVMCCallConv")
                                                     , (83, Data.List.NonEmpty.singleton "X86INTRCallConv")
                                                     , (84, Data.List.NonEmpty.singleton "AVRINTRCallConv")
                                                     , (85, Data.List.NonEmpty.singleton "AVRSIGNALCallConv")
                                                     , (86, Data.List.NonEmpty.singleton "AVRBUILTINCallConv")
                                                     , (87, Data.List.NonEmpty.singleton "AMDGPUVSCallConv")
                                                     , (88, Data.List.NonEmpty.singleton "AMDGPUGSCallConv")
                                                     , (89, Data.List.NonEmpty.singleton "AMDGPUPSCallConv")
                                                     , (90, Data.List.NonEmpty.singleton "AMDGPUCSCallConv")
                                                     , (91, Data.List.NonEmpty.singleton "AMDGPUKERNELCallConv")
                                                     , (92, Data.List.NonEmpty.singleton "X86RegCallCallConv")
                                                     , (93, Data.List.NonEmpty.singleton "AMDGPUHSCallConv")
                                                     , (94, Data.List.NonEmpty.singleton "MSP430BUILTINCallConv")
                                                     , (95, Data.List.NonEmpty.singleton "AMDGPULSCallConv")
                                                     , (96, Data.List.NonEmpty.singleton "AMDGPUESCallConv")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "CallConv"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "CallConv"

instance Show CallConv where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read CallConv where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern CCallConv :: CallConv
pattern CCallConv = CallConv 0

pattern FastCallConv :: CallConv
pattern FastCallConv = CallConv 8

pattern ColdCallConv :: CallConv
pattern ColdCallConv = CallConv 9

pattern GHCCallConv :: CallConv
pattern GHCCallConv = CallConv 10

pattern HiPECallConv :: CallConv
pattern HiPECallConv = CallConv 11

pattern AnyRegCallConv :: CallConv
pattern AnyRegCallConv = CallConv 13

pattern PreserveMostCallConv :: CallConv
pattern PreserveMostCallConv = CallConv 14

pattern PreserveAllCallConv :: CallConv
pattern PreserveAllCallConv = CallConv 15

pattern SwiftCallConv :: CallConv
pattern SwiftCallConv = CallConv 16

pattern CXXFASTTLSCallConv :: CallConv
pattern CXXFASTTLSCallConv = CallConv 17

pattern X86StdcallCallConv :: CallConv
pattern X86StdcallCallConv = CallConv 64

pattern X86FastcallCallConv :: CallConv
pattern X86FastcallCallConv = CallConv 65

pattern ARMAPCSCallConv :: CallConv
pattern ARMAPCSCallConv = CallConv 66

pattern ARMAAPCSCallConv :: CallConv
pattern ARMAAPCSCallConv = CallConv 67

pattern ARMAAPCSVFPCallConv :: CallConv
pattern ARMAAPCSVFPCallConv = CallConv 68

pattern MSP430INTRCallConv :: CallConv
pattern MSP430INTRCallConv = CallConv 69

pattern X86ThisCallCallConv :: CallConv
pattern X86ThisCallCallConv = CallConv 70

pattern PTXKernelCallConv :: CallConv
pattern PTXKernelCallConv = CallConv 71

pattern PTXDeviceCallConv :: CallConv
pattern PTXDeviceCallConv = CallConv 72

pattern SPIRFUNCCallConv :: CallConv
pattern SPIRFUNCCallConv = CallConv 75

pattern SPIRKERNELCallConv :: CallConv
pattern SPIRKERNELCallConv = CallConv 76

pattern IntelOCLBICallConv :: CallConv
pattern IntelOCLBICallConv = CallConv 77

pattern X8664SysVCallConv :: CallConv
pattern X8664SysVCallConv = CallConv 78

pattern Win64CallConv :: CallConv
pattern Win64CallConv = CallConv 79

pattern X86VectorCallCallConv :: CallConv
pattern X86VectorCallCallConv = CallConv 80

pattern HHVMCallConv :: CallConv
pattern HHVMCallConv = CallConv 81

pattern HHVMCCallConv :: CallConv
pattern HHVMCCallConv = CallConv 82

pattern X86INTRCallConv :: CallConv
pattern X86INTRCallConv = CallConv 83

pattern AVRINTRCallConv :: CallConv
pattern AVRINTRCallConv = CallConv 84

pattern AVRSIGNALCallConv :: CallConv
pattern AVRSIGNALCallConv = CallConv 85

pattern AVRBUILTINCallConv :: CallConv
pattern AVRBUILTINCallConv = CallConv 86

pattern AMDGPUVSCallConv :: CallConv
pattern AMDGPUVSCallConv = CallConv 87

pattern AMDGPUGSCallConv :: CallConv
pattern AMDGPUGSCallConv = CallConv 88

pattern AMDGPUPSCallConv :: CallConv
pattern AMDGPUPSCallConv = CallConv 89

pattern AMDGPUCSCallConv :: CallConv
pattern AMDGPUCSCallConv = CallConv 90

pattern AMDGPUKERNELCallConv :: CallConv
pattern AMDGPUKERNELCallConv = CallConv 91

pattern X86RegCallCallConv :: CallConv
pattern X86RegCallCallConv = CallConv 92

pattern AMDGPUHSCallConv :: CallConv
pattern AMDGPUHSCallConv = CallConv 93

pattern MSP430BUILTINCallConv :: CallConv
pattern MSP430BUILTINCallConv = CallConv 94

pattern AMDGPULSCallConv :: CallConv
pattern AMDGPULSCallConv = CallConv 95

pattern AMDGPUESCallConv :: CallConv
pattern AMDGPUESCallConv = CallConv 96

newtype ValueKind = ValueKind
  { un_ValueKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable ValueKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure ValueKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          ValueKind un_ValueKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_ValueKind2

instance HsBindgen.Runtime.CEnum.CEnum ValueKind where

  type CEnumZ ValueKind = FC.CUInt

  toCEnum = ValueKind

  fromCEnum = un_ValueKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "ArgumentValueKind")
                                                     , (1, Data.List.NonEmpty.singleton "BasicBlockValueKind")
                                                     , (2, Data.List.NonEmpty.singleton "MemoryUseValueKind")
                                                     , (3, Data.List.NonEmpty.singleton "MemoryDefValueKind")
                                                     , (4, Data.List.NonEmpty.singleton "MemoryPhiValueKind")
                                                     , (5, Data.List.NonEmpty.singleton "FunctionValueKind")
                                                     , (6, Data.List.NonEmpty.singleton "GlobalAliasValueKind")
                                                     , (7, Data.List.NonEmpty.singleton "GlobalIFuncValueKind")
                                                     , (8, Data.List.NonEmpty.singleton "GlobalVariableValueKind")
                                                     , (9, Data.List.NonEmpty.singleton "BlockAddressValueKind")
                                                     , (10, Data.List.NonEmpty.singleton "ConstantExprValueKind")
                                                     , (11, Data.List.NonEmpty.singleton "ConstantArrayValueKind")
                                                     , (12, Data.List.NonEmpty.singleton "ConstantStructValueKind")
                                                     , (13, Data.List.NonEmpty.singleton "ConstantVectorValueKind")
                                                     , (14, Data.List.NonEmpty.singleton "UndefValueValueKind")
                                                     , (15, Data.List.NonEmpty.singleton "ConstantAggregateZeroValueKind")
                                                     , (16, Data.List.NonEmpty.singleton "ConstantDataArrayValueKind")
                                                     , (17, Data.List.NonEmpty.singleton "ConstantDataVectorValueKind")
                                                     , (18, Data.List.NonEmpty.singleton "ConstantIntValueKind")
                                                     , (19, Data.List.NonEmpty.singleton "ConstantFPValueKind")
                                                     , (20, Data.List.NonEmpty.singleton "ConstantPointerNullValueKind")
                                                     , (21, Data.List.NonEmpty.singleton "ConstantTokenNoneValueKind")
                                                     , (22, Data.List.NonEmpty.singleton "MetadataAsValueValueKind")
                                                     , (23, Data.List.NonEmpty.singleton "InlineAsmValueKind")
                                                     , (24, Data.List.NonEmpty.singleton "InstructionValueKind")
                                                     , (25, Data.List.NonEmpty.singleton "PoisonValueValueKind")
                                                     , (26, Data.List.NonEmpty.singleton "ConstantTargetNoneValueKind")
                                                     , (27, Data.List.NonEmpty.singleton "ConstantPtrAuthValueKind")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "ValueKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "ValueKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum ValueKind where

  minDeclaredValue = ArgumentValueKind

  maxDeclaredValue = ConstantPtrAuthValueKind

instance Show ValueKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read ValueKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern ArgumentValueKind :: ValueKind
pattern ArgumentValueKind = ValueKind 0

pattern BasicBlockValueKind :: ValueKind
pattern BasicBlockValueKind = ValueKind 1

pattern MemoryUseValueKind :: ValueKind
pattern MemoryUseValueKind = ValueKind 2

pattern MemoryDefValueKind :: ValueKind
pattern MemoryDefValueKind = ValueKind 3

pattern MemoryPhiValueKind :: ValueKind
pattern MemoryPhiValueKind = ValueKind 4

pattern FunctionValueKind :: ValueKind
pattern FunctionValueKind = ValueKind 5

pattern GlobalAliasValueKind :: ValueKind
pattern GlobalAliasValueKind = ValueKind 6

pattern GlobalIFuncValueKind :: ValueKind
pattern GlobalIFuncValueKind = ValueKind 7

pattern GlobalVariableValueKind :: ValueKind
pattern GlobalVariableValueKind = ValueKind 8

pattern BlockAddressValueKind :: ValueKind
pattern BlockAddressValueKind = ValueKind 9

pattern ConstantExprValueKind :: ValueKind
pattern ConstantExprValueKind = ValueKind 10

pattern ConstantArrayValueKind :: ValueKind
pattern ConstantArrayValueKind = ValueKind 11

pattern ConstantStructValueKind :: ValueKind
pattern ConstantStructValueKind = ValueKind 12

pattern ConstantVectorValueKind :: ValueKind
pattern ConstantVectorValueKind = ValueKind 13

pattern UndefValueValueKind :: ValueKind
pattern UndefValueValueKind = ValueKind 14

pattern ConstantAggregateZeroValueKind :: ValueKind
pattern ConstantAggregateZeroValueKind = ValueKind 15

pattern ConstantDataArrayValueKind :: ValueKind
pattern ConstantDataArrayValueKind = ValueKind 16

pattern ConstantDataVectorValueKind :: ValueKind
pattern ConstantDataVectorValueKind = ValueKind 17

pattern ConstantIntValueKind :: ValueKind
pattern ConstantIntValueKind = ValueKind 18

pattern ConstantFPValueKind :: ValueKind
pattern ConstantFPValueKind = ValueKind 19

pattern ConstantPointerNullValueKind :: ValueKind
pattern ConstantPointerNullValueKind = ValueKind 20

pattern ConstantTokenNoneValueKind :: ValueKind
pattern ConstantTokenNoneValueKind = ValueKind 21

pattern MetadataAsValueValueKind :: ValueKind
pattern MetadataAsValueValueKind = ValueKind 22

pattern InlineAsmValueKind :: ValueKind
pattern InlineAsmValueKind = ValueKind 23

pattern InstructionValueKind :: ValueKind
pattern InstructionValueKind = ValueKind 24

pattern PoisonValueValueKind :: ValueKind
pattern PoisonValueValueKind = ValueKind 25

pattern ConstantTargetNoneValueKind :: ValueKind
pattern ConstantTargetNoneValueKind = ValueKind 26

pattern ConstantPtrAuthValueKind :: ValueKind
pattern ConstantPtrAuthValueKind = ValueKind 27

newtype IntPredicate = IntPredicate
  { un_IntPredicate :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable IntPredicate where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure IntPredicate
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          IntPredicate un_IntPredicate2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_IntPredicate2

instance HsBindgen.Runtime.CEnum.CEnum IntPredicate where

  type CEnumZ IntPredicate = FC.CUInt

  toCEnum = IntPredicate

  fromCEnum = un_IntPredicate

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (32, Data.List.NonEmpty.singleton "IntEQ")
                                                     , (33, Data.List.NonEmpty.singleton "IntNE")
                                                     , (34, Data.List.NonEmpty.singleton "IntUGT")
                                                     , (35, Data.List.NonEmpty.singleton "IntUGE")
                                                     , (36, Data.List.NonEmpty.singleton "IntULT")
                                                     , (37, Data.List.NonEmpty.singleton "IntULE")
                                                     , (38, Data.List.NonEmpty.singleton "IntSGT")
                                                     , (39, Data.List.NonEmpty.singleton "IntSGE")
                                                     , (40, Data.List.NonEmpty.singleton "IntSLT")
                                                     , (41, Data.List.NonEmpty.singleton "IntSLE")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "IntPredicate"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "IntPredicate"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum IntPredicate where

  minDeclaredValue = IntEQ

  maxDeclaredValue = IntSLE

instance Show IntPredicate where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read IntPredicate where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern IntEQ :: IntPredicate
pattern IntEQ = IntPredicate 32

pattern IntNE :: IntPredicate
pattern IntNE = IntPredicate 33

pattern IntUGT :: IntPredicate
pattern IntUGT = IntPredicate 34

pattern IntUGE :: IntPredicate
pattern IntUGE = IntPredicate 35

pattern IntULT :: IntPredicate
pattern IntULT = IntPredicate 36

pattern IntULE :: IntPredicate
pattern IntULE = IntPredicate 37

pattern IntSGT :: IntPredicate
pattern IntSGT = IntPredicate 38

pattern IntSGE :: IntPredicate
pattern IntSGE = IntPredicate 39

pattern IntSLT :: IntPredicate
pattern IntSLT = IntPredicate 40

pattern IntSLE :: IntPredicate
pattern IntSLE = IntPredicate 41

newtype RealPredicate = RealPredicate
  { un_RealPredicate :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable RealPredicate where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure RealPredicate
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          RealPredicate un_RealPredicate2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_RealPredicate2

instance HsBindgen.Runtime.CEnum.CEnum RealPredicate where

  type CEnumZ RealPredicate = FC.CUInt

  toCEnum = RealPredicate

  fromCEnum = un_RealPredicate

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "RealPredicateFalse")
                                                     , (1, Data.List.NonEmpty.singleton "RealOEQ")
                                                     , (2, Data.List.NonEmpty.singleton "RealOGT")
                                                     , (3, Data.List.NonEmpty.singleton "RealOGE")
                                                     , (4, Data.List.NonEmpty.singleton "RealOLT")
                                                     , (5, Data.List.NonEmpty.singleton "RealOLE")
                                                     , (6, Data.List.NonEmpty.singleton "RealONE")
                                                     , (7, Data.List.NonEmpty.singleton "RealORD")
                                                     , (8, Data.List.NonEmpty.singleton "RealUNO")
                                                     , (9, Data.List.NonEmpty.singleton "RealUEQ")
                                                     , (10, Data.List.NonEmpty.singleton "RealUGT")
                                                     , (11, Data.List.NonEmpty.singleton "RealUGE")
                                                     , (12, Data.List.NonEmpty.singleton "RealULT")
                                                     , (13, Data.List.NonEmpty.singleton "RealULE")
                                                     , (14, Data.List.NonEmpty.singleton "RealUNE")
                                                     , (15, Data.List.NonEmpty.singleton "RealPredicateTrue")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "RealPredicate"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "RealPredicate"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum RealPredicate where

  minDeclaredValue = RealPredicateFalse

  maxDeclaredValue = RealPredicateTrue

instance Show RealPredicate where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read RealPredicate where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern RealPredicateFalse :: RealPredicate
pattern RealPredicateFalse = RealPredicate 0

pattern RealOEQ :: RealPredicate
pattern RealOEQ = RealPredicate 1

pattern RealOGT :: RealPredicate
pattern RealOGT = RealPredicate 2

pattern RealOGE :: RealPredicate
pattern RealOGE = RealPredicate 3

pattern RealOLT :: RealPredicate
pattern RealOLT = RealPredicate 4

pattern RealOLE :: RealPredicate
pattern RealOLE = RealPredicate 5

pattern RealONE :: RealPredicate
pattern RealONE = RealPredicate 6

pattern RealORD :: RealPredicate
pattern RealORD = RealPredicate 7

pattern RealUNO :: RealPredicate
pattern RealUNO = RealPredicate 8

pattern RealUEQ :: RealPredicate
pattern RealUEQ = RealPredicate 9

pattern RealUGT :: RealPredicate
pattern RealUGT = RealPredicate 10

pattern RealUGE :: RealPredicate
pattern RealUGE = RealPredicate 11

pattern RealULT :: RealPredicate
pattern RealULT = RealPredicate 12

pattern RealULE :: RealPredicate
pattern RealULE = RealPredicate 13

pattern RealUNE :: RealPredicate
pattern RealUNE = RealPredicate 14

pattern RealPredicateTrue :: RealPredicate
pattern RealPredicateTrue = RealPredicate 15

newtype LandingPadClauseTy = LandingPadClauseTy
  { un_LandingPadClauseTy :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable LandingPadClauseTy where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure LandingPadClauseTy
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          LandingPadClauseTy un_LandingPadClauseTy2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_LandingPadClauseTy2

instance HsBindgen.Runtime.CEnum.CEnum LandingPadClauseTy where

  type CEnumZ LandingPadClauseTy = FC.CUInt

  toCEnum = LandingPadClauseTy

  fromCEnum = un_LandingPadClauseTy

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "LandingPadCatch")
                                                     , (1, Data.List.NonEmpty.singleton "LandingPadFilter")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "LandingPadClauseTy"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "LandingPadClauseTy"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum LandingPadClauseTy where

  minDeclaredValue = LandingPadCatch

  maxDeclaredValue = LandingPadFilter

instance Show LandingPadClauseTy where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read LandingPadClauseTy where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LandingPadCatch :: LandingPadClauseTy
pattern LandingPadCatch = LandingPadClauseTy 0

pattern LandingPadFilter :: LandingPadClauseTy
pattern LandingPadFilter = LandingPadClauseTy 1

newtype ThreadLocalMode = ThreadLocalMode
  { un_ThreadLocalMode :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable ThreadLocalMode where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure ThreadLocalMode
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          ThreadLocalMode un_ThreadLocalMode2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_ThreadLocalMode2

instance HsBindgen.Runtime.CEnum.CEnum ThreadLocalMode where

  type CEnumZ ThreadLocalMode = FC.CUInt

  toCEnum = ThreadLocalMode

  fromCEnum = un_ThreadLocalMode

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "NotThreadLocal")
                                                     , (1, Data.List.NonEmpty.singleton "GeneralDynamicTLSModel")
                                                     , (2, Data.List.NonEmpty.singleton "LocalDynamicTLSModel")
                                                     , (3, Data.List.NonEmpty.singleton "InitialExecTLSModel")
                                                     , (4, Data.List.NonEmpty.singleton "LocalExecTLSModel")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "ThreadLocalMode"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "ThreadLocalMode"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum ThreadLocalMode where

  minDeclaredValue = NotThreadLocal

  maxDeclaredValue = LocalExecTLSModel

instance Show ThreadLocalMode where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read ThreadLocalMode where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern NotThreadLocal :: ThreadLocalMode
pattern NotThreadLocal = ThreadLocalMode 0

pattern GeneralDynamicTLSModel :: ThreadLocalMode
pattern GeneralDynamicTLSModel = ThreadLocalMode 1

pattern LocalDynamicTLSModel :: ThreadLocalMode
pattern LocalDynamicTLSModel = ThreadLocalMode 2

pattern InitialExecTLSModel :: ThreadLocalMode
pattern InitialExecTLSModel = ThreadLocalMode 3

pattern LocalExecTLSModel :: ThreadLocalMode
pattern LocalExecTLSModel = ThreadLocalMode 4

newtype AtomicOrdering = AtomicOrdering
  { un_AtomicOrdering :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable AtomicOrdering where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure AtomicOrdering
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          AtomicOrdering un_AtomicOrdering2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_AtomicOrdering2

instance HsBindgen.Runtime.CEnum.CEnum AtomicOrdering where

  type CEnumZ AtomicOrdering = FC.CUInt

  toCEnum = AtomicOrdering

  fromCEnum = un_AtomicOrdering

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "AtomicOrderingNotAtomic")
                                                     , (1, Data.List.NonEmpty.singleton "AtomicOrderingUnordered")
                                                     , (2, Data.List.NonEmpty.singleton "AtomicOrderingMonotonic")
                                                     , (4, Data.List.NonEmpty.singleton "AtomicOrderingAcquire")
                                                     , (5, Data.List.NonEmpty.singleton "AtomicOrderingRelease")
                                                     , (6, Data.List.NonEmpty.singleton "AtomicOrderingAcquireRelease")
                                                     , (7, Data.List.NonEmpty.singleton "AtomicOrderingSequentiallyConsistent")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "AtomicOrdering"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "AtomicOrdering"

instance Show AtomicOrdering where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read AtomicOrdering where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern AtomicOrderingNotAtomic :: AtomicOrdering
pattern AtomicOrderingNotAtomic = AtomicOrdering 0

pattern AtomicOrderingUnordered :: AtomicOrdering
pattern AtomicOrderingUnordered = AtomicOrdering 1

pattern AtomicOrderingMonotonic :: AtomicOrdering
pattern AtomicOrderingMonotonic = AtomicOrdering 2

pattern AtomicOrderingAcquire :: AtomicOrdering
pattern AtomicOrderingAcquire = AtomicOrdering 4

pattern AtomicOrderingRelease :: AtomicOrdering
pattern AtomicOrderingRelease = AtomicOrdering 5

pattern AtomicOrderingAcquireRelease :: AtomicOrdering
pattern AtomicOrderingAcquireRelease = AtomicOrdering 6

pattern AtomicOrderingSequentiallyConsistent :: AtomicOrdering
pattern AtomicOrderingSequentiallyConsistent = AtomicOrdering 7

newtype AtomicRMWBinOp = AtomicRMWBinOp
  { un_AtomicRMWBinOp :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable AtomicRMWBinOp where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure AtomicRMWBinOp
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          AtomicRMWBinOp un_AtomicRMWBinOp2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_AtomicRMWBinOp2

instance HsBindgen.Runtime.CEnum.CEnum AtomicRMWBinOp where

  type CEnumZ AtomicRMWBinOp = FC.CUInt

  toCEnum = AtomicRMWBinOp

  fromCEnum = un_AtomicRMWBinOp

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "AtomicRMWBinOpXchg")
                                                     , (1, Data.List.NonEmpty.singleton "AtomicRMWBinOpAdd")
                                                     , (2, Data.List.NonEmpty.singleton "AtomicRMWBinOpSub")
                                                     , (3, Data.List.NonEmpty.singleton "AtomicRMWBinOpAnd")
                                                     , (4, Data.List.NonEmpty.singleton "AtomicRMWBinOpNand")
                                                     , (5, Data.List.NonEmpty.singleton "AtomicRMWBinOpOr")
                                                     , (6, Data.List.NonEmpty.singleton "AtomicRMWBinOpXor")
                                                     , (7, Data.List.NonEmpty.singleton "AtomicRMWBinOpMax")
                                                     , (8, Data.List.NonEmpty.singleton "AtomicRMWBinOpMin")
                                                     , (9, Data.List.NonEmpty.singleton "AtomicRMWBinOpUMax")
                                                     , (10, Data.List.NonEmpty.singleton "AtomicRMWBinOpUMin")
                                                     , (11, Data.List.NonEmpty.singleton "AtomicRMWBinOpFAdd")
                                                     , (12, Data.List.NonEmpty.singleton "AtomicRMWBinOpFSub")
                                                     , (13, Data.List.NonEmpty.singleton "AtomicRMWBinOpFMax")
                                                     , (14, Data.List.NonEmpty.singleton "AtomicRMWBinOpFMin")
                                                     , (15, Data.List.NonEmpty.singleton "AtomicRMWBinOpUIncWrap")
                                                     , (16, Data.List.NonEmpty.singleton "AtomicRMWBinOpUDecWrap")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "AtomicRMWBinOp"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "AtomicRMWBinOp"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum AtomicRMWBinOp where

  minDeclaredValue = AtomicRMWBinOpXchg

  maxDeclaredValue = AtomicRMWBinOpUDecWrap

instance Show AtomicRMWBinOp where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read AtomicRMWBinOp where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern AtomicRMWBinOpXchg :: AtomicRMWBinOp
pattern AtomicRMWBinOpXchg = AtomicRMWBinOp 0

pattern AtomicRMWBinOpAdd :: AtomicRMWBinOp
pattern AtomicRMWBinOpAdd = AtomicRMWBinOp 1

pattern AtomicRMWBinOpSub :: AtomicRMWBinOp
pattern AtomicRMWBinOpSub = AtomicRMWBinOp 2

pattern AtomicRMWBinOpAnd :: AtomicRMWBinOp
pattern AtomicRMWBinOpAnd = AtomicRMWBinOp 3

pattern AtomicRMWBinOpNand :: AtomicRMWBinOp
pattern AtomicRMWBinOpNand = AtomicRMWBinOp 4

pattern AtomicRMWBinOpOr :: AtomicRMWBinOp
pattern AtomicRMWBinOpOr = AtomicRMWBinOp 5

pattern AtomicRMWBinOpXor :: AtomicRMWBinOp
pattern AtomicRMWBinOpXor = AtomicRMWBinOp 6

pattern AtomicRMWBinOpMax :: AtomicRMWBinOp
pattern AtomicRMWBinOpMax = AtomicRMWBinOp 7

pattern AtomicRMWBinOpMin :: AtomicRMWBinOp
pattern AtomicRMWBinOpMin = AtomicRMWBinOp 8

pattern AtomicRMWBinOpUMax :: AtomicRMWBinOp
pattern AtomicRMWBinOpUMax = AtomicRMWBinOp 9

pattern AtomicRMWBinOpUMin :: AtomicRMWBinOp
pattern AtomicRMWBinOpUMin = AtomicRMWBinOp 10

pattern AtomicRMWBinOpFAdd :: AtomicRMWBinOp
pattern AtomicRMWBinOpFAdd = AtomicRMWBinOp 11

pattern AtomicRMWBinOpFSub :: AtomicRMWBinOp
pattern AtomicRMWBinOpFSub = AtomicRMWBinOp 12

pattern AtomicRMWBinOpFMax :: AtomicRMWBinOp
pattern AtomicRMWBinOpFMax = AtomicRMWBinOp 13

pattern AtomicRMWBinOpFMin :: AtomicRMWBinOp
pattern AtomicRMWBinOpFMin = AtomicRMWBinOp 14

pattern AtomicRMWBinOpUIncWrap :: AtomicRMWBinOp
pattern AtomicRMWBinOpUIncWrap = AtomicRMWBinOp 15

pattern AtomicRMWBinOpUDecWrap :: AtomicRMWBinOp
pattern AtomicRMWBinOpUDecWrap = AtomicRMWBinOp 16

newtype DiagnosticSeverity = DiagnosticSeverity
  { un_DiagnosticSeverity :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable DiagnosticSeverity where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure DiagnosticSeverity
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          DiagnosticSeverity un_DiagnosticSeverity2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_DiagnosticSeverity2

instance HsBindgen.Runtime.CEnum.CEnum DiagnosticSeverity where

  type CEnumZ DiagnosticSeverity = FC.CUInt

  toCEnum = DiagnosticSeverity

  fromCEnum = un_DiagnosticSeverity

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "DSError")
                                                     , (1, Data.List.NonEmpty.singleton "DSWarning")
                                                     , (2, Data.List.NonEmpty.singleton "DSRemark")
                                                     , (3, Data.List.NonEmpty.singleton "DSNote")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "DiagnosticSeverity"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "DiagnosticSeverity"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum DiagnosticSeverity where

  minDeclaredValue = DSError

  maxDeclaredValue = DSNote

instance Show DiagnosticSeverity where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read DiagnosticSeverity where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern DSError :: DiagnosticSeverity
pattern DSError = DiagnosticSeverity 0

pattern DSWarning :: DiagnosticSeverity
pattern DSWarning = DiagnosticSeverity 1

pattern DSRemark :: DiagnosticSeverity
pattern DSRemark = DiagnosticSeverity 2

pattern DSNote :: DiagnosticSeverity
pattern DSNote = DiagnosticSeverity 3

newtype InlineAsmDialect = InlineAsmDialect
  { un_InlineAsmDialect :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable InlineAsmDialect where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure InlineAsmDialect
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          InlineAsmDialect un_InlineAsmDialect2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_InlineAsmDialect2

instance HsBindgen.Runtime.CEnum.CEnum InlineAsmDialect where

  type CEnumZ InlineAsmDialect = FC.CUInt

  toCEnum = InlineAsmDialect

  fromCEnum = un_InlineAsmDialect

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "InlineAsmDialectATT")
                                                     , (1, Data.List.NonEmpty.singleton "InlineAsmDialectIntel")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "InlineAsmDialect"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "InlineAsmDialect"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum InlineAsmDialect where

  minDeclaredValue = InlineAsmDialectATT

  maxDeclaredValue = InlineAsmDialectIntel

instance Show InlineAsmDialect where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read InlineAsmDialect where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern InlineAsmDialectATT :: InlineAsmDialect
pattern InlineAsmDialectATT = InlineAsmDialect 0

pattern InlineAsmDialectIntel :: InlineAsmDialect
pattern InlineAsmDialectIntel = InlineAsmDialect 1

newtype ModuleFlagBehavior = ModuleFlagBehavior
  { un_ModuleFlagBehavior :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable ModuleFlagBehavior where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure ModuleFlagBehavior
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          ModuleFlagBehavior un_ModuleFlagBehavior2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_ModuleFlagBehavior2

instance HsBindgen.Runtime.CEnum.CEnum ModuleFlagBehavior where

  type CEnumZ ModuleFlagBehavior = FC.CUInt

  toCEnum = ModuleFlagBehavior

  fromCEnum = un_ModuleFlagBehavior

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "ModuleFlagBehaviorError")
                                                     , (1, Data.List.NonEmpty.singleton "ModuleFlagBehaviorWarning")
                                                     , (2, Data.List.NonEmpty.singleton "ModuleFlagBehaviorRequire")
                                                     , (3, Data.List.NonEmpty.singleton "ModuleFlagBehaviorOverride")
                                                     , (4, Data.List.NonEmpty.singleton "ModuleFlagBehaviorAppend")
                                                     , (5, Data.List.NonEmpty.singleton "ModuleFlagBehaviorAppendUnique")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "ModuleFlagBehavior"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "ModuleFlagBehavior"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum ModuleFlagBehavior where

  minDeclaredValue = ModuleFlagBehaviorError

  maxDeclaredValue = ModuleFlagBehaviorAppendUnique

instance Show ModuleFlagBehavior where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read ModuleFlagBehavior where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern ModuleFlagBehaviorError :: ModuleFlagBehavior
pattern ModuleFlagBehaviorError = ModuleFlagBehavior 0

pattern ModuleFlagBehaviorWarning :: ModuleFlagBehavior
pattern ModuleFlagBehaviorWarning = ModuleFlagBehavior 1

pattern ModuleFlagBehaviorRequire :: ModuleFlagBehavior
pattern ModuleFlagBehaviorRequire = ModuleFlagBehavior 2

pattern ModuleFlagBehaviorOverride :: ModuleFlagBehavior
pattern ModuleFlagBehaviorOverride = ModuleFlagBehavior 3

pattern ModuleFlagBehaviorAppend :: ModuleFlagBehavior
pattern ModuleFlagBehaviorAppend = ModuleFlagBehavior 4

pattern ModuleFlagBehaviorAppendUnique :: ModuleFlagBehavior
pattern ModuleFlagBehaviorAppendUnique = ModuleFlagBehavior 5

newtype AttributeIndex = AttributeIndex
  { un_AttributeIndex :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype TailCallKind = TailCallKind
  { un_TailCallKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable TailCallKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure TailCallKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          TailCallKind un_TailCallKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_TailCallKind2

instance HsBindgen.Runtime.CEnum.CEnum TailCallKind where

  type CEnumZ TailCallKind = FC.CUInt

  toCEnum = TailCallKind

  fromCEnum = un_TailCallKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "TailCallKindNone")
                                                     , (1, Data.List.NonEmpty.singleton "TailCallKindTail")
                                                     , (2, Data.List.NonEmpty.singleton "TailCallKindMustTail")
                                                     , (3, Data.List.NonEmpty.singleton "TailCallKindNoTail")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "TailCallKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "TailCallKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum TailCallKind where

  minDeclaredValue = TailCallKindNone

  maxDeclaredValue = TailCallKindNoTail

instance Show TailCallKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read TailCallKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern TailCallKindNone :: TailCallKind
pattern TailCallKindNone = TailCallKind 0

pattern TailCallKindTail :: TailCallKind
pattern TailCallKindTail = TailCallKind 1

pattern TailCallKindMustTail :: TailCallKind
pattern TailCallKindMustTail = TailCallKind 2

pattern TailCallKindNoTail :: TailCallKind
pattern TailCallKindNoTail = TailCallKind 3

newtype FastMathFlags = FastMathFlags
  { un_FastMathFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype GEPNoWrapFlags = GEPNoWrapFlags
  { un_GEPNoWrapFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c660ef7eea24d4ba" shutdown
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_65bd57ec4fa83523" getVersion
  :: F.Ptr FC.CUInt
     {- ^ __from C:__ @major@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @minor@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @patch@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0c750bb2f74dfbe2" createMessage
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @message@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e858bd253ce566b7" disposeMessage
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @message@ -}
  -> IO ()

newtype DiagnosticHandler = DiagnosticHandler
  { un_DiagnosticHandler :: F.FunPtr (LlvmC.Raw.Types.DiagnosticInfoRef -> (F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype YieldCallback = YieldCallback
  { un_YieldCallback :: F.FunPtr (LlvmC.Raw.Types.ContextRef -> (F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0c9df8eae2f4ed4b" contextCreate
  :: IO LlvmC.Raw.Types.ContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_18ae1ccbad5f2575" getGlobalContext
  :: IO LlvmC.Raw.Types.ContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_76e8b923e53eacae" contextSetDiagnosticHandler
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> DiagnosticHandler
     {- ^ __from C:__ @handler@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @diagnosticContext@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d6356c1c87d9824f" contextGetDiagnosticHandler
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO DiagnosticHandler

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fcdf8cdafe22920a" contextGetDiagnosticContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_44a29e30928bfb1c" contextSetYieldCallback
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> YieldCallback
     {- ^ __from C:__ @callback@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @opaqueHandle@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_adb890434595dc0c" contextShouldDiscardValueNames
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f62afd7a02a5db37" contextSetDiscardValueNames
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @discard@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8349f73c4278d19a" contextDispose
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fe151e2c3e2269dc" getDiagInfoDescription
  :: LlvmC.Raw.Types.DiagnosticInfoRef
     {- ^ __from C:__ @dI@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c97f46e70b7073f1" getDiagInfoSeverity
  :: LlvmC.Raw.Types.DiagnosticInfoRef
     {- ^ __from C:__ @dI@ -}
  -> IO DiagnosticSeverity

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8157ad9d51a3f412" getMDKindIDInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_750e3a5fae5b81b7" getMDKindID
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c05f8c2fa2dd3e12" getEnumAttributeKindForName
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sLen@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b5ba7a777d43f573" getLastEnumAttributeKind
  :: IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9654080d23156fa8" createEnumAttribute
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d1989db82f2761b3" getEnumAttributeKind
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5035083b24abe2ab" getEnumAttributeValue
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_44e1a613a5383292" createTypeAttribute
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @type_ref@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0b40aa19331ffa62" getTypeAttributeValue
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ff1208296dede47c" createConstantRangeAttribute_wrapper
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numBits@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @lowerWords@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @upperWords@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

createConstantRangeAttribute :: LlvmC.Raw.Types.ContextRef -> FC.CUInt -> FC.CUInt -> (HsBindgen.Runtime.IncompleteArray.IncompleteArray HsBindgen.Runtime.Prelude.Word64) -> (HsBindgen.Runtime.IncompleteArray.IncompleteArray HsBindgen.Runtime.Prelude.Word64) -> IO LlvmC.Raw.Types.AttributeRef
createConstantRangeAttribute =
  \x0 ->
    \x1 ->
      \x2 ->
        \x3 ->
          \x4 ->
            HsBindgen.Runtime.IncompleteArray.withPtr x4 (\ptr5 ->
                                                            HsBindgen.Runtime.IncompleteArray.withPtr x3 (\ptr6 ->
                                                                                                            createConstantRangeAttribute_wrapper x0 x1 x2 ptr6 ptr5))

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f8e9c8ffcc09cf00" createStringAttribute
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @k@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kLength@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @v@ -}
  -> FC.CUInt
     {- ^ __from C:__ @vLength@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dd5c313e42c91f52" getStringAttributeKind
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_51644d0e228d0322" getStringAttributeValue
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_143f4c5d7f274333" isEnumAttribute
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2b4daeffe9f11e06" isStringAttribute
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_848e08677fe0d625" isTypeAttribute
  :: LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dfc4c1791a068431" getTypeByName2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f40ed84793bcdd42" moduleCreateWithName
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @moduleID@ -}
  -> IO LlvmC.Raw.Types.ModuleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_acfea95b7084d9b6" moduleCreateWithNameInContext
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @moduleID@ -}
  -> LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.ModuleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_22fbe3b7a5adf598" cloneModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ModuleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c5aeb649e812136f" disposeModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1e34c5eb772741c3" isNewDbgInfoFormat
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0a084eab7853647b" setIsNewDbgInfoFormat
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @useNewFormat@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_62a1a7a021bed926" getModuleIdentifier
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0a044135c3a6f6ff" setModuleIdentifier
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @ident@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6fe89a53d6e25a99" getSourceFileName
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6e8359baecfc2cc3" setSourceFileName
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_00e761614662d2d5" getDataLayoutStr
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2166c0a9376344b2" getDataLayout
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_02ae7ee7042e39c1" setDataLayout
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @dataLayoutStr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2b9ed971c1e70b57" getTarget
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_91740f25aa89d887" setTarget
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2231710eba76cc3b" copyModuleFlagsMetadata
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr ModuleFlagEntry)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fbcad408e7306486" disposeModuleFlagsMetadata
  :: F.Ptr ModuleFlagEntry
     {- ^ __from C:__ @entries@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_16044f3a918f7707" moduleFlagEntriesGetFlagBehavior
  :: F.Ptr ModuleFlagEntry
     {- ^ __from C:__ @entries@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO ModuleFlagBehavior

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_14643efd62786c2d" moduleFlagEntriesGetKey
  :: F.Ptr ModuleFlagEntry
     {- ^ __from C:__ @entries@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4a2c85205a7ca551" moduleFlagEntriesGetMetadata
  :: F.Ptr ModuleFlagEntry
     {- ^ __from C:__ @entries@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_da17c373b29963af" getModuleFlag
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @key@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @keyLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_17088b876c779629" addModuleFlag
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> ModuleFlagBehavior
     {- ^ __from C:__ @behavior@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @key@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @keyLen@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9b46a35a39b6ca28" dumpModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_94be70b47353d6e1" printModuleToFile
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @filename@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_12e37236b5591bc6" printModuleToString
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6a4fc8f47316e2ab" getModuleInlineAsm
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_34ce0af1a30dbce8" setModuleInlineAsm2
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @asm@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_db696627d92aa83c" appendModuleInlineAsm
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @asm@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_34cce480519419db" getInlineAsm
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @asmString@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @asmStringSize@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @constraints@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @constraintsSize@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @hasSideEffects@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isAlignStack@ -}
  -> InlineAsmDialect
     {- ^ __from C:__ @dialect@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @canThrow@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_763cb22942ec872e" getInlineAsmAsmString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8f78269a6c4c7984" getInlineAsmConstraintString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3ddb5c48e6f23785" getInlineAsmDialect
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> IO InlineAsmDialect

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0cbe6c1452db36fd" getInlineAsmFunctionType
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2bce8800f6386f8b" getInlineAsmHasSideEffects
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a788ada940375dde" getInlineAsmNeedsAlignedStack
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7e7178d53c22ea9d" getInlineAsmCanUnwind
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inlineAsmVal@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3fa834032b26ea51" getModuleContext
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8a4a2487dcaa15f4" getTypeByName
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cf761402d484ee76" getFirstNamedMetadata
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3ba47055a92c2e12" getLastNamedMetadata
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f80acaf202bed5ae" getNextNamedMetadata
  :: LlvmC.Raw.Types.NamedMDNodeRef
     {- ^ __from C:__ @namedMDNode@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_811ace267229591c" getPreviousNamedMetadata
  :: LlvmC.Raw.Types.NamedMDNodeRef
     {- ^ __from C:__ @namedMDNode@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8cf1573206a8038a" getNamedMetadata
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_233ee9fea637a3ea" getOrInsertNamedMetadata
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.NamedMDNodeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e7b3858bac64c88c" getNamedMetadataName
  :: LlvmC.Raw.Types.NamedMDNodeRef
     {- ^ __from C:__ @namedMD@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_110d8a5ec22c60c6" getNamedMetadataNumOperands
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ad1d6c09f035029c" getNamedMetadataOperands
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_557ae7ece7419218" addNamedMetadataOperand
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_decdded8ea4e10e0" getDebugLocDirectory
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5b30737776c61e94" getDebugLocFilename
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e8a705caecb7613e" getDebugLocLine
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2459f0b6e7f6b30a" getDebugLocColumn
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_34adef42c3b9bc83" addFunction
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @functionTy@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_36a0fc333f895125" getNamedFunction
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_aa2fd2d9f9b6f45a" getFirstFunction
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f187758219370b71" getLastFunction
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_763ca186883b97b7" getNextFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_72e81560dbd8f811" getPreviousFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bed40cbecdad0a4a" setModuleInlineAsm
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @asm@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6efc04a8142542f5" getTypeKind
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO TypeKind

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_596f3252c558b37b" typeIsSized
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_66baf11867a251e6" getTypeContext
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fdf7ed1a5dbea855" dumpType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_21c3b6c66a3125d1" printTypeToString
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @val@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5b47a43c46c71996" int1TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_81b45eba83cb4686" int8TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2b80ffe01d952a00" int16TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5554c58cfccc7842" int32TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1645be95b2999a27" int64TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9d37dd31fe9ed00f" int128TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8662c58e34e524a2" intTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numBits@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3048d3db949b8d90" int1Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9401a3794e6e0fbe" int8Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a6b48d0af55a2a6f" int16Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7b99fb943d4feb98" int32Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b6b714cbacaff1b1" int64Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ea7a26825a49b747" int128Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a50353e0b58836a9" intType
  :: FC.CUInt
     {- ^ __from C:__ @numBits@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4b74a3228f8825b7" getIntTypeWidth
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @integerTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7249cd3ef56add0f" halfTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8c7f43aa8bcf0af8" bFloatTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_af6f4a1cbbf4f1c5" floatTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3372128e23b9358b" doubleTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b2030c19a72cb5f1" x86FP80TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_72bbef3fb8a90bed" fP128TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c0593b6725b4442e" pPCFP128TypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dbe2f77aca7bd008" halfType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e8ae3dc235e4ccaa" bFloatType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_41d1a296ff6808c4" floatType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_116ab54ba727009b" doubleType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_df014ebd7ce2b0bd" x86FP80Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_049b89b8b6d0331b" fP128Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9abf5b0574fef014" pPCFP128Type
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6d91c0302192801c" functionType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @returnType@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @paramTypes@ -}
  -> FC.CUInt
     {- ^ __from C:__ @paramCount@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isVarArg@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4d9be33b4643917e" isFunctionVarArg
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @functionTy@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_810909d4cfc04ffb" getReturnType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @functionTy@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2b5c4a5166648b87" countParamTypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @functionTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2fa6b88fb873d810" getParamTypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @functionTy@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7d5670a5232a409d" structTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementTypes@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @packed@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7ed42f9c9689f856" structType
  :: F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementTypes@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @packed@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb9ae856f933ce3c" structCreateNamed
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ad97c14b347fa0f2" getStructName
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_59ad629727e32cae" structSetBody
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementTypes@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @packed@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bf3b3bfacf5c212d" countStructElementTypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4becc113fd41d964" getStructElementTypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_280946a8aadd95b8" structGetTypeAtIndex
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @i@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9a67cf6d2d16526e" isPackedStruct
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d05cf09de3330c37" isOpaqueStruct
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b45fc300305f28d7" isLiteralStruct
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_71d7175693fe8526" getElementType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3adbd41c35bcf167" getSubtypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @tp@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @arr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a470af21593a3265" getNumContainedTypes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @tp@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_26029a112be6d9c6" arrayType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementType@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c36f5c47a241db50" arrayType2
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementType@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @elementCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_694d35caa5e31295" getArrayLength
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @arrayTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_75f5f14e1aff88d9" getArrayLength2
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @arrayTy@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5c752a4ad5987419" pointerType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementType@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addressSpace@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_46edaefee3535cc7" pointerTypeIsOpaque
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b88846597f730531" pointerTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addressSpace@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_027b06ec7f026acb" getPointerAddressSpace
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @pointerTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2ff503d6ebb9d8dc" vectorType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementType@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fd2438f820e045f5" scalableVectorType
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementType@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elementCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4a835958c61c9318" getVectorSize
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @vectorTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cb6cca4b7cda1dba" getConstantPtrAuthPointer
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptrAuth@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cd5236f22ff5006c" getConstantPtrAuthKey
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptrAuth@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6f2a22af1e59dd01" getConstantPtrAuthDiscriminator
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptrAuth@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3045aec7fe57a584" getConstantPtrAuthAddrDiscriminator
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptrAuth@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_83f7c7e2402321bf" voidTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2946d9fe32f41791" labelTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dafc8fda8254262d" x86MMXTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9d548e8842b9b518" x86AMXTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b16feff443526a6e" tokenTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb1c9d12de1e9e1a" metadataTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b0df5ee069fe99e5" voidType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a75cdea0f88aca88" labelType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8287bfbdcfcc51b6" x86MMXType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_31ec7704f9ae0db5" x86AMXType
  :: IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b74edcd44f2ab284" targetExtTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @typeParams@ -}
  -> FC.CUInt
     {- ^ __from C:__ @typeParamCount@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @intParams@ -}
  -> FC.CUInt
     {- ^ __from C:__ @intParamCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c4213d772e69970e" getTargetExtTypeName
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @targetExtTy@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d0a4f76b249cf2e9" getTargetExtTypeNumTypeParams
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @targetExtTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e5ddd30fd79df35c" getTargetExtTypeTypeParam
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @targetExtTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7a362586c264faf4" getTargetExtTypeNumIntParams
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @targetExtTy@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2156e1007893eb35" getTargetExtTypeIntParam
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @targetExtTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6949e588426b685b" typeOf
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_160161bb05117d76" getValueKind
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO ValueKind

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_40b32422b547ee1a" getValueName2
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9ad4f0f4db7e00ba" setValueName2
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0660aefb99e00360" dumpValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8187c8cbc9c35391" printValueToString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_360a6008feee9751" printDbgRecordToString
  :: LlvmC.Raw.Types.DbgRecordRef
     {- ^ __from C:__ @record@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_910f87142dfe4d3a" replaceAllUsesWith
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @oldVal@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @newVal@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2feb13a1d9ec7785" isConstant
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ba47f497cb3553cc" isUndef
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_24230734e77ee572" isPoison
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_81d80c8190a951b2" isAArgument
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bff99ee872b624d9" isABasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_426e30e449bae6c2" isAInlineAsm
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cc13a7160000b971" isAUser
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bf6964d78b71d113" isAConstant
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_df9c6089b5db2a0b" isABlockAddress
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e83826a32a4ca01a" isAConstantAggregateZero
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_51da9e38cd7beb6f" isAConstantArray
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_776cb3244575331b" isAConstantDataSequential
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f4e59c470e7910f8" isAConstantDataArray
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_01ddfe2d1619a80d" isAConstantDataVector
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f09da101ad4d0918" isAConstantExpr
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bcebac0703c9339c" isAConstantFP
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cc2a3902c68cff38" isAConstantInt
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2bf21db1ceb950f9" isAConstantPointerNull
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9b968107e9b368e0" isAConstantStruct
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b775af0cfe332ead" isAConstantTokenNone
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_43031181e7214dc8" isAConstantVector
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c569999e022bc42d" isAConstantPtrAuth
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bf5d44837f2084f1" isAGlobalValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a418b870d0c1cdb9" isAGlobalAlias
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1f5fe63908fe62f2" isAGlobalObject
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_eab190632c144f3a" isAFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f39a91f5c8a8240c" isAGlobalVariable
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_97bbb74ade678b02" isAGlobalIFunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d253e396588805d4" isAUndefValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a9462edb64581228" isAPoisonValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f5af237c77ded862" isAInstruction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e4332882abe13019" isAUnaryOperator
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_547529aa128078cb" isABinaryOperator
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_48bc770fadb28368" isACallInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb93c13779ab2f60" isAIntrinsicInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1d183980f090a895" isADbgInfoIntrinsic
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ff9def3b64ae241a" isADbgVariableIntrinsic
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3b081c6472306889" isADbgDeclareInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9300ff7ed1555055" isADbgLabelInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dd0b6ecd48835efb" isAMemIntrinsic
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e3b157303c86c7d9" isAMemCpyInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c185a7fadb16e29d" isAMemMoveInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_59360f8d765051d3" isAMemSetInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1d9411a28c5551ab" isACmpInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3a2d046f07d9b1d9" isAFCmpInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f56642cd72af69e3" isAICmpInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_180d6dabe728f4c5" isAExtractElementInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d818ae7ee1f12b51" isAGetElementPtrInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_59afafe0f8d34336" isAInsertElementInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4ae690f2eac242b1" isAInsertValueInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2e088ac81cefb800" isALandingPadInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_968f66b82f09e9d8" isAPHINode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2152d07fc4205deb" isASelectInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_abeaac9c3af81c1f" isAShuffleVectorInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7d1a32a38ac221cd" isAStoreInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_030ed5cb98ff35bd" isABranchInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_698fc003189adb06" isAIndirectBrInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4998d932d15205a8" isAInvokeInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_62d5637f5b31c758" isAReturnInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f13ce1e12fc81a20" isASwitchInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6e219b36ae63aded" isAUnreachableInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7acffaa87a148429" isAResumeInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f58ae8ee91f9f19b" isACleanupReturnInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cb7093faa6206529" isACatchReturnInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b13c14403b761165" isACatchSwitchInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5f5c0286f27c3221" isACallBrInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_18544ec766f3542a" isAFuncletPadInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_27eb2287a832704b" isACatchPadInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d2e9824c14ccc592" isACleanupPadInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9a1ff3d576a39730" isAUnaryInstruction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2d14eb4bf8dc8964" isAAllocaInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0d0d66083f456bf3" isACastInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0573663220b74681" isAAddrSpaceCastInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_338014e0dd67d012" isABitCastInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_548b8735a3719185" isAFPExtInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9c45b2328a838d85" isAFPToSIInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6a8b23a80dce2723" isAFPToUIInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_99f2df36b122b08d" isAFPTruncInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b2468dd1a762babf" isAIntToPtrInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4691475c0e23723e" isAPtrToIntInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9e67234be595e3b8" isASExtInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_abae807e489af4c3" isASIToFPInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_93862148876fa07c" isATruncInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ff55f5c06d759c77" isAUIToFPInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f6d988e404470765" isAZExtInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e8d77b1c4c3cf727" isAExtractValueInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_44116c5f4cccc1c5" isALoadInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_598b4596261af7ec" isAVAArgInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f5f19bf7c13847df" isAFreezeInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ea5f13aa3a074a5b" isAAtomicCmpXchgInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_51a5ed4ed5a0fa57" isAAtomicRMWInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a57263187d69c785" isAFenceInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_baa46b4187501c24" isAMDNode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_29b9107dfa2b037f" isAValueAsMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_195d52cd38746e76" isAMDString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a0abc80364768961" getValueName
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d2d842cd38927ad6" setValueName
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bb63a93399ba0c08" getFirstUse
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.UseRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_19f4a6f8b56e4fb1" getNextUse
  :: LlvmC.Raw.Types.UseRef
     {- ^ __from C:__ @u@ -}
  -> IO LlvmC.Raw.Types.UseRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b530f5a40491854d" getUser
  :: LlvmC.Raw.Types.UseRef
     {- ^ __from C:__ @u@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_87e7d32c7298155f" getUsedValue
  :: LlvmC.Raw.Types.UseRef
     {- ^ __from C:__ @u@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_38241c8f083615c9" getOperand
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_db48b7b15953e4d5" getOperandUse
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.UseRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_00472a7129e576f1" setOperand
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @user@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d8939614db5be876" getNumOperands
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a7a825b7e07c6920" constNull
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_06b7bd1735a84cbf" constAllOnes
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0a6f1cab329086e6" getUndef
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1e28be075fdcbadb" getPoison
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_91e5cfdbce21298a" isNull
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9f5bc935f3c9ccef" constPointerNull
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cd69f898b240a3b6" constInt
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @intTy@ -}
  -> FC.CULLong
     {- ^ __from C:__ @n@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @signExtend@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a08dfdee4e5fb51d" constIntOfArbitraryPrecision_wrapper
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @intTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numWords@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @words@ -}
  -> IO LlvmC.Raw.Types.ValueRef

constIntOfArbitraryPrecision :: LlvmC.Raw.Types.TypeRef -> FC.CUInt -> (HsBindgen.Runtime.IncompleteArray.IncompleteArray HsBindgen.Runtime.Prelude.Word64) -> IO LlvmC.Raw.Types.ValueRef
constIntOfArbitraryPrecision =
  \x0 ->
    \x1 ->
      \x2 ->
        HsBindgen.Runtime.IncompleteArray.withPtr x2 (\ptr3 ->
                                                        constIntOfArbitraryPrecision_wrapper x0 x1 ptr3)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_49dffd7555089af6" constIntOfString
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @intTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @text@ -}
  -> HsBindgen.Runtime.Prelude.Word8
     {- ^ __from C:__ @radix@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dbbae2f2ed044a31" constIntOfStringAndSize
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @intTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @text@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> HsBindgen.Runtime.Prelude.Word8
     {- ^ __from C:__ @radix@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4d76dac773ebf346" constReal
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @realTy@ -}
  -> FC.CDouble
     {- ^ __from C:__ @n@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5ed898540a4e301b" constRealOfString
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @realTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @text@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4103f46d3643be5c" constRealOfStringAndSize
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @realTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @text@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_065b72f9693e046e" constIntGetZExtValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO FC.CULLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_84ae878f19b72216" constIntGetSExtValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO FC.CLLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0028efcaf9839842" constRealGetDouble
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> F.Ptr LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @losesInfo@ -}
  -> IO FC.CDouble

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f80c98e38481d491" constStringInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @dontNullTerminate@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ceb68e644873e95d" constStringInContext2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @dontNullTerminate@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e706f63a354d0ee2" constString
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @dontNullTerminate@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e24d465b8b605b0b" isConstantString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_05cdfb60c8bd7d10" getAsString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6b56ecc70339b8a1" constStructInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @packed@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_205434094c784e16" constStruct
  :: F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @packed@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bbae4588d3e9c66c" constArray
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementTy@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4ab1a1e23a0153ac" constArray2
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elementTy@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVals@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @length@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4220ba983a31afe3" constNamedStruct
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f119a1a823a93231" getAggregateElement
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_14b8e3c154371f0e" getElementAsConstant
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b41294b940318c9e" constVector
  :: F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @scalarConstantVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @size@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_08c4590699ccccbd" constantPtrAuth
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptr@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @key@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @disc@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @addrDisc@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_11d087b19b9c25c4" getConstOpcode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO Opcode

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f8076cd114ecc0a0" alignOf
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cac24ad7369fa2a1" sizeOf
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c929918d5ed7b095" constNeg
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0f699a53f4aa6920" constNSWNeg
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9736a246c4d45b93" constNUWNeg
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_080378937434c0eb" constNot
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0e57ac84c08f78e1" constAdd
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_17836442429b1048" constNSWAdd
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2ff9241e8a83bcc1" constNUWAdd
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e6a70386a6dcc12b" constSub
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_860b940b6308467d" constNSWSub
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d2b9f64985736168" constNUWSub
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_860457d769e5b66f" constMul
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6dda81d468ab1591" constNSWMul
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0f194320874dfc20" constNUWMul
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8eda015c9f50ca3e" constXor
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHSConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHSConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1c06b5d226579727" constGEP2
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantIndices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_57000d6968127c8c" constInBoundsGEP2
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantIndices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_499c7b0e9f8fb7d7" constGEPWithNoWrapFlags
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantIndices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> GEPNoWrapFlags
     {- ^ __from C:__ @noWrapFlags@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e671d06eb9b7c5fb" constTrunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c80f24f304384bc3" constPtrToInt
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a7a22e22ffacc167" constIntToPtr
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_310b773e7fd171d9" constBitCast
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c47980cbf77a9258" constAddrSpaceCast
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5bb63a9e00b51011" constTruncOrBitCast
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5c5de024f900e6e9" constPointerCast
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @toType@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d18df2ea0e5cefbc" constExtractElement
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vectorConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indexConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a1de64dc381aae3d" constInsertElement
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vectorConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @elementValueConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indexConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c1127a57f6d8b9d3" constShuffleVector
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vectorAConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vectorBConstant@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @maskConstant@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_05d360b6e838ece0" blockAddress
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_42ac282cfaa9fc50" getBlockAddressFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @blockAddr@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c311e8a0d4d99b21" getBlockAddressBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @blockAddr@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b82f9f7e6c457467" constInlineAsm
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @asmString@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @constraints@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @hasSideEffects@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isAlignStack@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5d84d67916fe2414" getGlobalParent
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO LlvmC.Raw.Types.ModuleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_47ee9d3a8491fa0e" isDeclaration
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e369134559ea51a8" getLinkage
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO Linkage

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a8a118e6012cec39" setLinkage
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> Linkage
     {- ^ __from C:__ @linkage@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_669ecc0330111487" getSection
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_97b8f577f1f1f818" setSection
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @section@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f352ccc3f318c498" getVisibility
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO Visibility

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_109faa626f3ec0a5" setVisibility
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> Visibility
     {- ^ __from C:__ @viz@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_01acbf4fbd01d46c" getDLLStorageClass
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO DLLStorageClass

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9e04be30a35070bb" setDLLStorageClass
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> DLLStorageClass
     {- ^ __from C:__ @class'@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_db72f3f32f26d8e7" getUnnamedAddress
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO UnnamedAddr

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_47207d0d84119b7d" setUnnamedAddress
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> UnnamedAddr
     {- ^ __from C:__ @unnamedAddr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c7fae327629d97af" globalGetValueType
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_526253c0d6b6616f" hasUnnamedAddr
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9f3e9b49184541fd" setUnnamedAddr
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @hasUnnamedAddr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c3d8b3831f434d29" getAlignment
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6e708f0a1d621cec" setAlignment
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> FC.CUInt
     {- ^ __from C:__ @bytes@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b132e3e4383021e8" globalSetMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kind@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @mD@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3f8755e6c2dfb6c9" globalEraseMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kind@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_df1e2afebb8b80ed" globalClearMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a71b22cbdfaea9c0" globalCopyAllMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @value@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numEntries@ -}
  -> IO (F.Ptr ValueMetadataEntry)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_032b7cfdc192e6f0" disposeValueMetadataEntries
  :: F.Ptr ValueMetadataEntry
     {- ^ __from C:__ @entries@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e38dacc26b323c7a" valueMetadataEntriesGetKind
  :: F.Ptr ValueMetadataEntry
     {- ^ __from C:__ @entries@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6a5062c98e9bd70f" valueMetadataEntriesGetMetadata
  :: F.Ptr ValueMetadataEntry
     {- ^ __from C:__ @entries@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_288620c4c2ece5f9" addGlobal
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9fb91e46ed811984" addGlobalInAddressSpace
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addressSpace@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_397cec9bbdfc0385" getNamedGlobal
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c8ba526992b93237" getFirstGlobal
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0393b8bd3f3d76b1" getLastGlobal
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d7f26074e434d94c" getNextGlobal
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c82bd6d905d15dac" getPreviousGlobal
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ab3ba6aef4a985e4" deleteGlobal
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_714d3cf3611a5fd2" getInitializer
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_518bf57d32a5c832" setInitializer
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @constantVal@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e448e5a56db28b3a" isThreadLocal
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_627b7b102b31de05" setThreadLocal
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isThreadLocal@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1ce19ea9f3f1993d" isGlobalConstant
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_356b78b4aef978aa" setGlobalConstant
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isConstant@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1af3e12cceffceea" getThreadLocalMode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO ThreadLocalMode

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6ab1129a4cebba99" setThreadLocalMode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> ThreadLocalMode
     {- ^ __from C:__ @mode@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_51d4acf224bc8dfa" isExternallyInitialized
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8cd153cbbdf610db" setExternallyInitialized
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isExtInit@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f731078614a84dea" addAlias2
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @valueTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addrSpace@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @aliasee@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0759173336db5c1d" getNamedGlobalAlias
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4e1e21751f05bc08" getFirstGlobalAlias
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9b24814c501221e9" getLastGlobalAlias
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_23adaa4b7d55ec18" getNextGlobalAlias
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gA@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2189c193f4734dde" getPreviousGlobalAlias
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gA@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_da07743384b52343" aliasGetAliasee
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @alias@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1f1285d7eb86ad88" aliasSetAliasee
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @alias@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @aliasee@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ca075570966d4a71" deleteFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3db773fac6d1e0be" hasPersonalityFn
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_93e45136f168b8f7" getPersonalityFn
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d706ed1eb309d23f" setPersonalityFn
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @personalityFn@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_95a458fe969f89b5" lookupIntrinsicID
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c3f90de1017ffb50" getIntrinsicID
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b933b652895f0f08" getIntrinsicDeclaration
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @mod@ -}
  -> FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @paramTypes@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @paramCount@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_af4ff83f902f0c03" intrinsicGetType
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @ctx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @paramTypes@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @paramCount@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9d9d1344497770bf" intrinsicGetName
  :: FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLength@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_eec3ab68a8419ba3" intrinsicCopyOverloadedName
  :: FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @paramTypes@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @paramCount@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLength@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_92e697c6cbbb6b91" intrinsicCopyOverloadedName2
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @mod@ -}
  -> FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> F.Ptr LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @paramTypes@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @paramCount@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLength@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_64a2b93f760180e5" intrinsicIsOverloaded
  :: FC.CUInt
     {- ^ __from C:__ @iD@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d9759510b28a2957" getFunctionCallConv
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4ad0b2920a8d06c6" setFunctionCallConv
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> FC.CUInt
     {- ^ __from C:__ @cC@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_586c6781c74db06c" getGC
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a793c3f8a8a70189" setGC
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6af5b4865bc4e408" getPrefixData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2d316301bf8e2be3" hasPrefixData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9941cc08beb73ad9" setPrefixData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @prefixData@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b0fa3210bf612b72" getPrologueData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5785b8178e777b69" hasPrologueData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9818d3592abf56ba" setPrologueData
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @prologueData@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5d0a271fd82aa638" addAttributeAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e59b3ce7a1452c58" getAttributeCountAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_50b2297d0f89a550" getAttributesAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @attrs@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5cde0d1ca4d4ce73" getEnumAttributeAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_39b770b39e58c4ad" getStringAttributeAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @k@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kLen@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b66c7cbce40cf56c" removeEnumAttributeAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7e42e94d44a29e28" removeStringAttributeAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @k@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kLen@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0dd5e2d357517413" addTargetDependentFunctionAttr
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @a@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @v@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_28501baf0bdc3b47" countParams
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9faf1968f9cf86db" getParams
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @params@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6628bbab070a58a8" getParam
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4ceb1ff5b83b74f3" getParamParent
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a0169a1aa0eb57ce" getFirstParam
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_86757ba56825e78c" getLastParam
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e3202f6cad386149" getNextParam
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arg@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6435b441c8bc26a5" getPreviousParam
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arg@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c7876cf8e3d28ee7" setParamAlignment
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @align@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_42594e0c518fc409" addGlobalIFunc
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> FC.CUInt
     {- ^ __from C:__ @addrSpace@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @resolver@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7cb876fe578b6720" getNamedGlobalIFunc
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @nameLen@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cf1e1d180ae62318" getFirstGlobalIFunc
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3b3e9f5e7ef47667" getLastGlobalIFunc
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_df26490d2fc2e1a4" getNextGlobalIFunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9a4193523a20973d" getPreviousGlobalIFunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f8bccc0a9f9d5939" getGlobalIFuncResolver
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_55b07f7853fbb81f" setGlobalIFuncResolver
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @resolver@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dd0f5d9d3789098e" eraseGlobalIFunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_74528152d3585c97" removeGlobalIFunc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @iFunc@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_065ea37750a748fa" mDStringInContext2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sLen@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cdaa8984f26ab3bc" mDNodeInContext2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @mDs@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @count@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9cef587073f6eae1" metadataAsValue
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @mD@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c234653b5244073a" valueAsMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d36718d80de80d14" getMDString
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0e79e43f7411053d" getMDNodeNumOperands
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_76d203b6b254448e" getMDNodeOperands
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_53a56672f1144046" replaceMDNodeOperandWith
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @replacement@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_65ba968aca6561c9" mDStringInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_31b7e57012d86650" mDString
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> FC.CUInt
     {- ^ __from C:__ @sLen@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6e0aaa7377dfee90" mDNodeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ac9689b684cc9ab6" mDNode
  :: F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3a357528457413b9" createOperandBundle
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @tag@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @tagLen@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> IO LlvmC.Raw.Types.OperandBundleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_800e61b0d63495bc" disposeOperandBundle
  :: LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundle@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3f5dc1971561f683" getOperandBundleTag
  :: LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundle@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @len@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7d471aa962c59f66" getNumOperandBundleArgs
  :: LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundle@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0c3018e06392f68b" getOperandBundleArgAtIndex
  :: LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundle@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f744a9d55578fdbd" basicBlockAsValue
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_00ab3ff6293a05d0" valueIsBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f4af41e81fce4de9" valueAsBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_53576b191565cfad" getBasicBlockName
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3d4bfd21345463a5" getBasicBlockParent
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b2b95e4509d8c019" getBasicBlockTerminator
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d868c01183de77cc" countBasicBlocks
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4877809763f3196e" getBasicBlocks
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @basicBlocks@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dcb6bf6ac5a05b10" getFirstBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_95b6b22fbec1acd6" getLastBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_42f6a4edc6cecd7b" getNextBasicBlock
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_693b4a012e63f54b" getPreviousBasicBlock
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c8b71174fd6c3451" getEntryBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ae6ea771f3d60964" insertExistingBasicBlockAfterInsertBlock
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_de78078738ae0787" appendExistingBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0ee960f878a4e207" createBasicBlockInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_03f817b3a6ca9324" appendBasicBlockInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9676c4627f4d4ab7" appendBasicBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d8d9338148f77185" insertBasicBlockInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f5742313815c2402" insertBasicBlock
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @insertBeforeBB@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7425c5388647ae2e" deleteBasicBlock
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ad87a06d0e0e5535" removeBasicBlockFromParent
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e896df6a6808549a" moveBasicBlockBefore
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @movePos@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0854c728c6320b6a" moveBasicBlockAfter
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @movePos@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_558fee18c06332e0" getFirstInstruction
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_06ab487fae1cb9f8" getLastInstruction
  :: LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_41dce98bd6aca2af" hasMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ef82aa0a71f9b75e" getMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_179b7e139066f223" setMetadata
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @node@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0808868eca5c7a3a" instructionGetAllMetadataOtherThanDebugLoc
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numEntries@ -}
  -> IO (F.Ptr ValueMetadataEntry)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_849a63d461b40fd3" getInstructionParent
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_043ce7ac1bbb24bd" getNextInstruction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2129d9c7f6461dd2" getPreviousInstruction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a25bfe5504a269d2" instructionRemoveFromParent
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1e521b9d49b6fef4" instructionEraseFromParent
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4cec2095dc4318db" deleteInstruction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_53561d8e9a27ff4a" getInstructionOpcode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO Opcode

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ddc537c097c921c1" getICmpPredicate
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO IntPredicate

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b9c63ef6620e9f03" getFCmpPredicate
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO RealPredicate

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_74d56cbf53b9c711" instructionClone
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d7985fb75a1bc6ac" isATerminatorInst
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_109f3ed805cc4a2c" getNumArgOperands
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_03f6e383fc89adbe" setInstructionCallConv
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> FC.CUInt
     {- ^ __from C:__ @cC@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_026534c3e046d6d0" getInstructionCallConv
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dbf522754a8480be" setInstrParamAlignment
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @align@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_91a288dd88cf9609" addCallSiteAttribute
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @a@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6fc08a9feec65346" getCallSiteAttributeCount
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_90ea0e9cb7630aad" getCallSiteAttributes
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr LlvmC.Raw.Types.AttributeRef
     {- ^ __from C:__ @attrs@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_00161941bc7334ed" getCallSiteEnumAttribute
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_64eaa8c3dd2f887c" getCallSiteStringAttribute
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @k@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kLen@ -}
  -> IO LlvmC.Raw.Types.AttributeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9efa3a24e0e365e8" removeCallSiteEnumAttribute
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kindID@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6e586b7b9711840a" removeCallSiteStringAttribute
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> AttributeIndex
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @k@ -}
  -> FC.CUInt
     {- ^ __from C:__ @kLen@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_42a37773d3e2187c" getCalledFunctionType
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2ab0172af8808ebd" getCalledValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e4c9ccb2ee9e076c" getNumOperandBundles
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b83194ae3b84465d" getOperandBundleAtIndex
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @c@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.OperandBundleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4f0a291f7a41c9be" isTailCall
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ece03577efebab76" setTailCall
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isTailCall@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb031a68e54ddc8e" getTailCallKind
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callInst@ -}
  -> IO TailCallKind

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cfb5c9a12860cd93" setTailCallKind
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callInst@ -}
  -> TailCallKind
     {- ^ __from C:__ @kind@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dcf566ecaff920f5" getNormalDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @invokeInst@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f0398d6b213479ed" getUnwindDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @invokeInst@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8a432b71271d6dd9" setNormalDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @invokeInst@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @b@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_aaffc61b434e10e5" setUnwindDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @invokeInst@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @b@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_52a6f15727ccd2b0" getCallBrDefaultDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callBr@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_393abadc7633580c" getCallBrNumIndirectDests
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callBr@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_48947787134ea08b" getCallBrIndirectDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @callBr@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_294495d191927c85" getNumSuccessors
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @term@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f5b65efe65518929" getSuccessor
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @term@ -}
  -> FC.CUInt
     {- ^ __from C:__ @i@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3352be654c5d9c8e" setSuccessor
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @term@ -}
  -> FC.CUInt
     {- ^ __from C:__ @i@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_927c538bca435149" isConditional
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @branch@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb3ffdc7783cb43c" getCondition
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @branch@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5ac68299ab3f205d" setCondition
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @branch@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cond@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_485e79c39015ed8b" getSwitchDefaultDest
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @switchInstr@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_08e8e6e7269e46fa" getAllocatedType
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @alloca@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ea195328ce0f69f5" isInBounds
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gEP@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0248a0d510aa6631" setIsInBounds
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gEP@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @inBounds@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fb05c6bf9535fd94" getGEPSourceElementType
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gEP@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d2c4dc26b152c64a" gEPGetNoWrapFlags
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gEP@ -}
  -> IO GEPNoWrapFlags

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a1aebcf4671a8868" gEPSetNoWrapFlags
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @gEP@ -}
  -> GEPNoWrapFlags
     {- ^ __from C:__ @noWrapFlags@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d49e3423586d215a" addIncoming
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @phiNode@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @incomingValues@ -}
  -> F.Ptr LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @incomingBlocks@ -}
  -> FC.CUInt
     {- ^ __from C:__ @count@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d766a5b11252f220" countIncoming
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @phiNode@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_abac6210e7528a1d" getIncomingValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @phiNode@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6ab3a8c16be589ad" getIncomingBlock
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @phiNode@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dbf17899e24af082" getNumIndices
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b8b0223806e50a09" getIndices
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO (F.Ptr FC.CUInt)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c569c2c67a56a1fd" createBuilderInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> IO LlvmC.Raw.Types.BuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_843f37f9d6106bb8" createBuilder
  :: IO LlvmC.Raw.Types.BuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_244b46ac8e56b7b9" positionBuilder
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ed151682b3996383" positionBuilderBeforeDbgRecords
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1a76e85cc468ab0a" positionBuilderBefore
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f04218b15eb51b0b" positionBuilderBeforeInstrAndDbgRecords
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8f92d748f0b73f5a" positionBuilderAtEnd
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @block@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9b3d8831f416dc6c" getInsertBlock
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Types.BasicBlockRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fc3a137466fd5e4f" clearInsertionPosition
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c0122eee6510c727" insertIntoBuilder
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ec62e7a065aaebf6" insertIntoBuilderWithName
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @instr@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ff90b921dc8486c8" disposeBuilder
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_eeb4fb6e93262d96" getCurrentDebugLocation2
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4a4e25b6db15c8b2" setCurrentDebugLocation2
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @loc@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_567da7b4bc1ed0cb" setInstDebugLocation
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_28351862e74a5113" addMetadataToInst
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_597699c997b3c9df" builderGetDefaultFPMathTag
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Types.MetadataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3b768efb0750bb29" builderSetDefaultFPMathTag
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.MetadataRef
     {- ^ __from C:__ @fPMathTag@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5f1d18caa017e0d5" setCurrentDebugLocation
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @l@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8ff54557f0e5a944" getCurrentDebugLocation
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_325efb3a07aeb128" buildRetVoid
  :: LlvmC.Raw.Types.BuilderRef
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d08a10eca7bb99fb" buildRet
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_6eb9d0d8ba63ef90" buildAggregateRet
  :: LlvmC.Raw.Types.BuilderRef
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @retVals@ -}
  -> FC.CUInt
     {- ^ __from C:__ @n@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3cc88f79d6240bfe" buildBr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @dest@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cb143e559105c68b" buildCondBr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @if'@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @then'@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @else'@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_88cf88935f2556a8" buildSwitch
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @else'@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numCases@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2af79ecdbafaa96e" buildIndirectBr
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @addr@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numDests@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_201662f4b9cd0537" buildCallBr
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @defaultDest@ -}
  -> F.Ptr LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @indirectDests@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndirectDests@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundles@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numBundles@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_842346fb62c01943" buildInvoke2
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @then'@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @catch@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_729af12eeef24f18" buildInvokeWithOperandBundles
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @then'@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @catch@ -}
  -> F.Ptr LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundles@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numBundles@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_333988f2e3450c43" buildUnreachable
  :: LlvmC.Raw.Types.BuilderRef
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_04e448541569ef7f" buildResume
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @exn@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cdfd371a8a1a6587" buildLandingPad
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @persFn@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numClauses@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e26de1581b7214c1" buildCleanupRet
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchPad@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8751efb9234f5c5e" buildCatchRet
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchPad@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @bB@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0051c09e15fa56cb" buildCatchPad
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @parentPad@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0b596d553b7ff700" buildCleanupPad
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @parentPad@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2c8772cc71dbc292" buildCatchSwitch
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @parentPad@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @unwindBB@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numHandlers@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_624111495f97a907" addCase
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @switch@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @onVal@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1865906a479681f3" addDestination
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indirectBr@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e822e3b9475aebe2" getNumClauses
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @landingPad@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_25cb5d9e236228b7" getClause
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @landingPad@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1eff582d7a9f0ac4" addClause
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @landingPad@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @clauseVal@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7eeec7ddfad59b1f" isCleanup
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @landingPad@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_600e8f135db0044b" setCleanup
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @landingPad@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @val@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f58f63393c923653" addHandler
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchSwitch@ -}
  -> LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @dest@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_82f547d4ee424e8f" getNumHandlers
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchSwitch@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f1c6c682e68be3f1" getHandlers
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchSwitch@ -}
  -> F.Ptr LlvmC.Raw.Types.BasicBlockRef
     {- ^ __from C:__ @handlers@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ee6878a7bfcfbeb1" getArgOperand
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @funclet@ -}
  -> FC.CUInt
     {- ^ __from C:__ @i@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_26f1bf6b6d074d3c" setArgOperand
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @funclet@ -}
  -> FC.CUInt
     {- ^ __from C:__ @i@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @value@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_40b8b751ac5ec18d" getParentCatchSwitch
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchPad@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0037aa1dbb43f2d1" setParentCatchSwitch
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchPad@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @catchSwitch@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0dcc6b09937cb05e" buildAdd
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ccb289d54de75229" buildNSWAdd
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e049bd7d6d8b73b5" buildNUWAdd
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b8cfe58f7937b990" buildFAdd
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e289e75b0e2aa58a" buildSub
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_21cf8bf5da366b70" buildNSWSub
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a6995596c6a76185" buildNUWSub
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dddbfbb144a76c78" buildFSub
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_8e963dd25412fe6d" buildMul
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1757eed728974cab" buildNSWMul
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_43ac4dc258dfb231" buildNUWMul
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fa8297838021149f" buildFMul
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_cc21b2c74a1b88a0" buildUDiv
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ef7f2523fb06c256" buildExactUDiv
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3e407169ab75322f" buildSDiv
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c822c620ce2061ea" buildExactSDiv
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_360127de42034b14" buildFDiv
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_aac3d2ca75de39f1" buildURem
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_763372ef455d4e7a" buildSRem
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d67c529000984ff4" buildFRem
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_96934186c80667cc" buildShl
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4cbe1ade8e0324f3" buildLShr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ab9212590b99447c" buildAShr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dc6761ce5285c498" buildAnd
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ac18de78f76e53ca" buildOr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9201833edc8056f3" buildXor
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2169c42d262a8f46" buildBinOp
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> Opcode
     {- ^ __from C:__ @op@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_14330cfec8bee4e8" buildNeg
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_08359b3f8159eb39" buildNSWNeg
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d812b26a7f1476f2" buildNUWNeg
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ee636ef711b1ea35" buildFNeg
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b433897a818efdca" buildNot
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a82611cc68e67094" getNUW
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arithInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0cbc06a85c4253fe" setNUW
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arithInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @hasNUW@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a43c6653450c2fb8" getNSW
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arithInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b28e767daa13a883" setNSW
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @arithInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @hasNSW@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_531818db083da26d" getExact
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @divOrShrInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_369750e3b54cd5a0" setExact
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @divOrShrInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isExact@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ac32991ae4505b76" getNNeg
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @nonNegInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dd9782c6008fadfd" setNNeg
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @nonNegInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isNonNeg@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c3b8e1e358b402a5" getFastMathFlags
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fPMathInst@ -}
  -> IO FastMathFlags

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d196b883f2240889" setFastMathFlags
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fPMathInst@ -}
  -> FastMathFlags
     {- ^ __from C:__ @fMF@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f51ddb0a0bcc013b" canValueUseFastMathFlags
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_92881b4629119435" getIsDisjoint
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_884ff60905732e85" setIsDisjoint
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @inst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isDisjoint@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_52792f6fc7f3f48c" buildMalloc
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4c17f03cd6470ae5" buildArrayMalloc
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a5bd0922c385ae1f" buildMemSet
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptr@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @len@ -}
  -> FC.CUInt
     {- ^ __from C:__ @align@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a23f8bdac4c2052e" buildMemCpy
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @dst@ -}
  -> FC.CUInt
     {- ^ __from C:__ @dstAlign@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @src@ -}
  -> FC.CUInt
     {- ^ __from C:__ @srcAlign@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @size@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7fe4adf90f6e4211" buildMemMove
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @dst@ -}
  -> FC.CUInt
     {- ^ __from C:__ @dstAlign@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @src@ -}
  -> FC.CUInt
     {- ^ __from C:__ @srcAlign@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @size@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_31fcc31371fa1948" buildAlloca
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_666a355e2dfb0ff0" buildArrayAlloca
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3ec2c9d38799806d" buildFree
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointerVal@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7e864a9307b5d4df" buildLoad2
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointerVal@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7b110c2acb2747d3" buildStore
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptr@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_192779ee468424a7" buildGEP2
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointer@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e55144b722df4050" buildInBoundsGEP2
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointer@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0e87c4058347c660" buildGEPWithNoWrapFlags
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointer@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @indices@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numIndices@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> GEPNoWrapFlags
     {- ^ __from C:__ @noWrapFlags@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_5f43c372159f995f" buildStructGEP2
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pointer@ -}
  -> FC.CUInt
     {- ^ __from C:__ @idx@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fa667a4fd7ab2967" buildGlobalString
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e6a98b746e50f0ef" buildGlobalStringPtr
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @str@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a315d01d7f4fe85b" getVolatile
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @memoryAccessInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4daf5a46d6de4bca" setVolatile
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @memoryAccessInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isVolatile@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_725b05468ae49a6c" getWeak
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4a4bb4123e920536" setWeak
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isWeak@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ffb37cb280a33267" getOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @memoryAccessInst@ -}
  -> IO AtomicOrdering

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1182d20b1e52177a" setOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @memoryAccessInst@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @ordering@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7e7c3c9705076f73" getAtomicRMWBinOp
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @atomicRMWInst@ -}
  -> IO AtomicRMWBinOp

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c9e00df3eb6267ce" setAtomicRMWBinOp
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @atomicRMWInst@ -}
  -> AtomicRMWBinOp
     {- ^ __from C:__ @binOp@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3cf467f0742a264d" buildTrunc
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c53cd680954d894e" buildZExt
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ae0d3d6c31dbd2aa" buildSExt
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3949fca4697a4ffa" buildFPToUI
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2b8de607781909b3" buildFPToSI
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_80c46b09f2a6a0e8" buildUIToFP
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_536c0cae55b8f17c" buildSIToFP
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ab034615839bbddf" buildFPTrunc
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b833e0f6759f2800" buildFPExt
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ef0c5d14ff34e7c0" buildPtrToInt
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_0ddd25b3a188c6a2" buildIntToPtr
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_94d27ff47e4d29a1" buildBitCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fbe1f98301b4865a" buildAddrSpaceCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ad645a13da2cfc34" buildZExtOrBitCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_9a2757f21ca1ec24" buildSExtOrBitCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_819041ac26b2a6b5" buildTruncOrBitCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_95d96719fd55dcc9" buildCast
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> Opcode
     {- ^ __from C:__ @op@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_7acfdaf04d72c2c0" buildPointerCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f16281631d992ae6" buildIntCast2
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isSigned@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_67e348107824f7d1" buildFPCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_066ac1af426404db" buildIntCast
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_abadb523dd883c16" getCastOpcode
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @src@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @srcIsSigned@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @destTy@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @destIsSigned@ -}
  -> IO Opcode

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3857d5fc396ca8a1" buildICmp
  :: LlvmC.Raw.Types.BuilderRef
  -> IntPredicate
     {- ^ __from C:__ @op@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d305171a5b5a3e32" buildFCmp
  :: LlvmC.Raw.Types.BuilderRef
  -> RealPredicate
     {- ^ __from C:__ @op@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3e46f4863c463cba" buildPhi
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_50bda63288a943b4" buildCall2
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_19118da636f83b60" buildCallWithOperandBundles
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @args@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr LlvmC.Raw.Types.OperandBundleRef
     {- ^ __from C:__ @bundles@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numBundles@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_845f3692c6d70f16" buildSelect
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @if'@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @then'@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @else'@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1b6ed73dda5328d8" buildVAArg
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @list@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f61fa0514b09b62f" buildExtractElement
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vecVal@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @index@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d0c583c6061c4c89" buildInsertElement
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @vecVal@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @eltVal@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @index@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_54e31949b22804fe" buildShuffleVector
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v1@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v2@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @mask@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d1d145fddf42a438" buildExtractValue
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @aggVal@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_504d1bc4a6217d27" buildInsertValue
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @aggVal@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @eltVal@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ff1013ecd1a71d74" buildFreeze
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_007b5ac9933336fb" buildIsNull
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_669e66ba3bc8e642" buildIsNotNull
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_ce73263b8e75bb58" buildPtrDiff2
  :: LlvmC.Raw.Types.BuilderRef
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @elemTy@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @lHS@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @rHS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fc1a2c4084f519d2" buildFence
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @ordering@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @singleThread@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_e941ffadc15c355e" buildAtomicRMW
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> AtomicRMWBinOp
     {- ^ __from C:__ @op@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @pTR@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @val@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @ordering@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @singleThread@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_558848291a2679aa" buildAtomicCmpXchg
  :: LlvmC.Raw.Types.BuilderRef
     {- ^ __from C:__ @b@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @ptr@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmp@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @new@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @successOrdering@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @failureOrdering@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @singleThread@ -}
  -> IO LlvmC.Raw.Types.ValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d450ebe4bef70d15" getNumMaskElements
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @shuffleVectorInst@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f721215878af6a85" getUndefMaskElem
  :: IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_15329a12a80b7929" getMaskValue
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @shuffleVectorInst@ -}
  -> FC.CUInt
     {- ^ __from C:__ @elt@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_1a39dc74a1a0be3d" isAtomicSingleThread
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @atomicInst@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_69065eb8cd0e7b53" setAtomicSingleThread
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @atomicInst@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @singleThread@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_98bb9e133646a940" getCmpXchgSuccessOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> IO AtomicOrdering

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_fa98f838fdf3c762" setCmpXchgSuccessOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @ordering@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_710308e58a8ab176" getCmpXchgFailureOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> IO AtomicOrdering

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_945a173ce985b76d" setCmpXchgFailureOrdering
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @cmpXchgInst@ -}
  -> AtomicOrdering
     {- ^ __from C:__ @ordering@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_f8d9a0f182e5c7d6" createModuleProviderForExistingModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.ModuleProviderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_15cade3b085564ea" disposeModuleProvider
  :: LlvmC.Raw.Types.ModuleProviderRef
     {- ^ __from C:__ @m@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_bb6d2ae6549eb8c0" createMemoryBufferWithContentsOfFile
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> F.Ptr LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @outMemBuf@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_26e2ed0f271c2e02" createMemoryBufferWithSTDIN
  :: F.Ptr LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @outMemBuf@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a7231fd877d6bb43" createMemoryBufferWithMemoryRange
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @inputData@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @inputDataLength@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @bufferName@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @requiresNullTerminator@ -}
  -> IO LlvmC.Raw.Types.MemoryBufferRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_dbd4c8d10bd921b6" createMemoryBufferWithMemoryRangeCopy
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @inputData@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @inputDataLength@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @bufferName@ -}
  -> IO LlvmC.Raw.Types.MemoryBufferRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d75a6950e604e0e8" getBufferStart
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_3ccf1d8ad2bac6aa" getBufferSize
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> IO HsBindgen.Runtime.Prelude.CSize

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_563c1b8da589dd00" disposeMemoryBuffer
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_885ed76658a29788" createPassManager
  :: IO LlvmC.Raw.Types.PassManagerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_2e384bff9f05324c" createFunctionPassManagerForModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.PassManagerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_64c672d789861eed" createFunctionPassManager
  :: LlvmC.Raw.Types.ModuleProviderRef
     {- ^ __from C:__ @mP@ -}
  -> IO LlvmC.Raw.Types.PassManagerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_b3b247c48d0fd4fc" runPassManager
  :: LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @pM@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_a3d26c7cd111f1b7" initializeFunctionPassManager
  :: LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @fPM@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d5cfd1926a6d2fa9" runFunctionPassManager
  :: LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @fPM@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_4eeeb2cbd8257d9d" finalizeFunctionPassManager
  :: LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @fPM@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_c427c93c1f7ed6c8" disposePassManager
  :: LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @pM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_d2c64545ef0a5d40" startMultithreaded
  :: IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_09aa9c20ab5ebe85" stopMultithreaded
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Core_34a9924e757d71c6" isMultithreaded
  :: IO LlvmC.Raw.Types.Bool
