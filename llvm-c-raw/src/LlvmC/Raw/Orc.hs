{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Orc where

import Data.Bits (FiniteBits)
import qualified Data.Bits as Bits
import qualified Data.Ix as Ix
import qualified Data.List.NonEmpty
import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Error
import qualified LlvmC.Raw.TargetMachine
import qualified LlvmC.Raw.Types
import Prelude ((<*>), (>>), Bounded, Enum, Eq, IO, Int, Integral, Num, Ord, Read, Real, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Orc.h>\nvoid hs_bindgen_LlvmC_Raw_Orc_80cac539f65c98e3 (LLVMOrcExecutionSessionRef arg1, LLVMOrcErrorReporterFunction arg2, void *arg3) { LLVMOrcExecutionSessionSetErrorReporter(arg1, arg2, arg3); }\nLLVMOrcSymbolStringPoolRef hs_bindgen_LlvmC_Raw_Orc_3fe7853bc1c892b3 (LLVMOrcExecutionSessionRef arg1) { return LLVMOrcExecutionSessionGetSymbolStringPool(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_8653565e907ad0c4 (LLVMOrcSymbolStringPoolRef arg1) { LLVMOrcSymbolStringPoolClearDeadEntries(arg1); }\nLLVMOrcSymbolStringPoolEntryRef hs_bindgen_LlvmC_Raw_Orc_c45654f85472c38b (LLVMOrcExecutionSessionRef arg1, char *arg2) { return LLVMOrcExecutionSessionIntern(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Orc_af6e3c583251abc0 (LLVMOrcExecutionSessionRef arg1, LLVMOrcLookupKind arg2, LLVMOrcCJITDylibSearchOrder arg3, size_t arg4, LLVMOrcCLookupSet arg5, size_t arg6, LLVMOrcExecutionSessionLookupHandleResultFunction arg7, void *arg8) { LLVMOrcExecutionSessionLookup(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nvoid hs_bindgen_LlvmC_Raw_Orc_ae85ff71eb635922 (LLVMOrcSymbolStringPoolEntryRef arg1) { LLVMOrcRetainSymbolStringPoolEntry(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_83e497e3b769bbbf (LLVMOrcSymbolStringPoolEntryRef arg1) { LLVMOrcReleaseSymbolStringPoolEntry(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Orc_5f15676ce9260838 (LLVMOrcSymbolStringPoolEntryRef arg1) { return LLVMOrcSymbolStringPoolEntryStr(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_e3180549942dad3d (LLVMOrcResourceTrackerRef arg1) { LLVMOrcReleaseResourceTracker(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_76a919d380367281 (LLVMOrcResourceTrackerRef arg1, LLVMOrcResourceTrackerRef arg2) { LLVMOrcResourceTrackerTransferTo(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_fb9c5df70deca22a (LLVMOrcResourceTrackerRef arg1) { return LLVMOrcResourceTrackerRemove(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_3ee44d84db9b0096 (LLVMOrcDefinitionGeneratorRef arg1) { LLVMOrcDisposeDefinitionGenerator(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_e4190d4f68475f08 (LLVMOrcMaterializationUnitRef arg1) { LLVMOrcDisposeMaterializationUnit(arg1); }\nLLVMOrcMaterializationUnitRef hs_bindgen_LlvmC_Raw_Orc_5e3fcd5dfec681d5 (char *arg1, void *arg2, LLVMOrcCSymbolFlagsMapPairs arg3, size_t arg4, LLVMOrcSymbolStringPoolEntryRef arg5, LLVMOrcMaterializationUnitMaterializeFunction arg6, LLVMOrcMaterializationUnitDiscardFunction arg7, LLVMOrcMaterializationUnitDestroyFunction arg8) { return LLVMOrcCreateCustomMaterializationUnit(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nLLVMOrcMaterializationUnitRef hs_bindgen_LlvmC_Raw_Orc_5e3ca1bf3162960a (LLVMOrcCSymbolMapPairs arg1, size_t arg2) { return LLVMOrcAbsoluteSymbols(arg1, arg2); }\nLLVMOrcMaterializationUnitRef hs_bindgen_LlvmC_Raw_Orc_235a19d63d848c73 (LLVMOrcLazyCallThroughManagerRef arg1, LLVMOrcIndirectStubsManagerRef arg2, LLVMOrcJITDylibRef arg3, LLVMOrcCSymbolAliasMapPairs arg4, size_t arg5) { return LLVMOrcLazyReexports(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_Orc_af8dda30a5dc259d (LLVMOrcMaterializationResponsibilityRef arg1) { LLVMOrcDisposeMaterializationResponsibility(arg1); }\nLLVMOrcJITDylibRef hs_bindgen_LlvmC_Raw_Orc_fd4c60cb48a411bd (LLVMOrcMaterializationResponsibilityRef arg1) { return LLVMOrcMaterializationResponsibilityGetTargetDylib(arg1); }\nLLVMOrcExecutionSessionRef hs_bindgen_LlvmC_Raw_Orc_20ba4f5565315eee (LLVMOrcMaterializationResponsibilityRef arg1) { return LLVMOrcMaterializationResponsibilityGetExecutionSession(arg1); }\nLLVMOrcCSymbolFlagsMapPairs hs_bindgen_LlvmC_Raw_Orc_7c9c665c342ad7ed (LLVMOrcMaterializationResponsibilityRef arg1, size_t *arg2) { return LLVMOrcMaterializationResponsibilityGetSymbols(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Orc_a06c88ef8a37e2da (LLVMOrcCSymbolFlagsMapPairs arg1) { LLVMOrcDisposeCSymbolFlagsMap(arg1); }\nLLVMOrcSymbolStringPoolEntryRef hs_bindgen_LlvmC_Raw_Orc_645f2d7335f80a0b (LLVMOrcMaterializationResponsibilityRef arg1) { return LLVMOrcMaterializationResponsibilityGetInitializerSymbol(arg1); }\nLLVMOrcSymbolStringPoolEntryRef *hs_bindgen_LlvmC_Raw_Orc_97cafeb7da90f71e (LLVMOrcMaterializationResponsibilityRef arg1, size_t *arg2) { return LLVMOrcMaterializationResponsibilityGetRequestedSymbols(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Orc_25a12914ad25f53c (LLVMOrcSymbolStringPoolEntryRef *arg1) { LLVMOrcDisposeSymbols(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_e2f67e0a09be17f4 (LLVMOrcMaterializationResponsibilityRef arg1, LLVMOrcCSymbolMapPairs arg2, size_t arg3) { return LLVMOrcMaterializationResponsibilityNotifyResolved(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_7d0916eb0c14f194 (LLVMOrcMaterializationResponsibilityRef arg1, LLVMOrcCSymbolDependenceGroup *arg2, size_t arg3) { return LLVMOrcMaterializationResponsibilityNotifyEmitted(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_cbf5d04f11b1a808 (LLVMOrcMaterializationResponsibilityRef arg1, LLVMOrcCSymbolFlagsMapPairs arg2, size_t arg3) { return LLVMOrcMaterializationResponsibilityDefineMaterializing(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_444f59b8560fffde (LLVMOrcMaterializationResponsibilityRef arg1) { LLVMOrcMaterializationResponsibilityFailMaterialization(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_0e96a580c4a36ca3 (LLVMOrcMaterializationResponsibilityRef arg1, LLVMOrcMaterializationUnitRef arg2) { return LLVMOrcMaterializationResponsibilityReplace(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_4d46ec996727d1ec (LLVMOrcMaterializationResponsibilityRef arg1, LLVMOrcSymbolStringPoolEntryRef *arg2, size_t arg3, LLVMOrcMaterializationResponsibilityRef *arg4) { return LLVMOrcMaterializationResponsibilityDelegate(arg1, arg2, arg3, arg4); }\nLLVMOrcJITDylibRef hs_bindgen_LlvmC_Raw_Orc_22da2c0012306c7c (LLVMOrcExecutionSessionRef arg1, char *arg2) { return LLVMOrcExecutionSessionCreateBareJITDylib(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_d02c3dc7774da5a7 (LLVMOrcExecutionSessionRef arg1, LLVMOrcJITDylibRef *arg2, char *arg3) { return LLVMOrcExecutionSessionCreateJITDylib(arg1, arg2, arg3); }\nLLVMOrcJITDylibRef hs_bindgen_LlvmC_Raw_Orc_0e71b205a2540305 (LLVMOrcExecutionSessionRef arg1, char *arg2) { return LLVMOrcExecutionSessionGetJITDylibByName(arg1, arg2); }\nLLVMOrcResourceTrackerRef hs_bindgen_LlvmC_Raw_Orc_d9d42b76a83e37d8 (LLVMOrcJITDylibRef arg1) { return LLVMOrcJITDylibCreateResourceTracker(arg1); }\nLLVMOrcResourceTrackerRef hs_bindgen_LlvmC_Raw_Orc_5a9ae9924b9bf92d (LLVMOrcJITDylibRef arg1) { return LLVMOrcJITDylibGetDefaultResourceTracker(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_2e97a49ad0a41a94 (LLVMOrcJITDylibRef arg1, LLVMOrcMaterializationUnitRef arg2) { return LLVMOrcJITDylibDefine(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_cd318a7d484413bf (LLVMOrcJITDylibRef arg1) { return LLVMOrcJITDylibClear(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_d55f342eb5e3bcf3 (LLVMOrcJITDylibRef arg1, LLVMOrcDefinitionGeneratorRef arg2) { LLVMOrcJITDylibAddGenerator(arg1, arg2); }\nLLVMOrcDefinitionGeneratorRef hs_bindgen_LlvmC_Raw_Orc_3c7d40d88e9f9b0c (LLVMOrcCAPIDefinitionGeneratorTryToGenerateFunction arg1, void *arg2, LLVMOrcDisposeCAPIDefinitionGeneratorFunction arg3) { return LLVMOrcCreateCustomCAPIDefinitionGenerator(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_81356ea06afd4d01 (LLVMOrcLookupStateRef arg1, LLVMErrorRef arg2) { LLVMOrcLookupStateContinueLookup(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_6299438581db04b1 (LLVMOrcDefinitionGeneratorRef *arg1, char arg2, LLVMOrcSymbolPredicate arg3, void *arg4) { return LLVMOrcCreateDynamicLibrarySearchGeneratorForProcess(arg1, arg2, arg3, arg4); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_f1cbf077b7feea7e (LLVMOrcDefinitionGeneratorRef *arg1, char *arg2, char arg3, LLVMOrcSymbolPredicate arg4, void *arg5) { return LLVMOrcCreateDynamicLibrarySearchGeneratorForPath(arg1, arg2, arg3, arg4, arg5); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_1790b24c5dbafdd7 (LLVMOrcDefinitionGeneratorRef *arg1, LLVMOrcObjectLayerRef arg2, char *arg3, char *arg4) { return LLVMOrcCreateStaticLibrarySearchGeneratorForPath(arg1, arg2, arg3, arg4); }\nLLVMOrcThreadSafeContextRef hs_bindgen_LlvmC_Raw_Orc_848b8091895d8f9d (void) { return LLVMOrcCreateNewThreadSafeContext(); }\nLLVMContextRef hs_bindgen_LlvmC_Raw_Orc_b9bb1dbda13d3161 (LLVMOrcThreadSafeContextRef arg1) { return LLVMOrcThreadSafeContextGetContext(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_7fee397c0ecb33dd (LLVMOrcThreadSafeContextRef arg1) { LLVMOrcDisposeThreadSafeContext(arg1); }\nLLVMOrcThreadSafeModuleRef hs_bindgen_LlvmC_Raw_Orc_dfc9438c9e8bb47d (LLVMModuleRef arg1, LLVMOrcThreadSafeContextRef arg2) { return LLVMOrcCreateNewThreadSafeModule(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Orc_641f0e28b2e0c847 (LLVMOrcThreadSafeModuleRef arg1) { LLVMOrcDisposeThreadSafeModule(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_26eb77c11b031f34 (LLVMOrcThreadSafeModuleRef arg1, LLVMOrcGenericIRModuleOperationFunction arg2, void *arg3) { return LLVMOrcThreadSafeModuleWithModuleDo(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_426fe61196aa83a2 (LLVMOrcJITTargetMachineBuilderRef *arg1) { return LLVMOrcJITTargetMachineBuilderDetectHost(arg1); }\nLLVMOrcJITTargetMachineBuilderRef hs_bindgen_LlvmC_Raw_Orc_11e32d8e8d879228 (LLVMTargetMachineRef arg1) { return LLVMOrcJITTargetMachineBuilderCreateFromTargetMachine(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_9be8d232f268bc19 (LLVMOrcJITTargetMachineBuilderRef arg1) { LLVMOrcDisposeJITTargetMachineBuilder(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Orc_e67cf259873429c1 (LLVMOrcJITTargetMachineBuilderRef arg1) { return LLVMOrcJITTargetMachineBuilderGetTargetTriple(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_50580393911066c1 (LLVMOrcJITTargetMachineBuilderRef arg1, char *arg2) { LLVMOrcJITTargetMachineBuilderSetTargetTriple(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_5dd823fea0ad4032 (LLVMOrcObjectLayerRef arg1, LLVMOrcJITDylibRef arg2, LLVMMemoryBufferRef arg3) { return LLVMOrcObjectLayerAddObjectFile(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_7cb2ffb598aa4e51 (LLVMOrcObjectLayerRef arg1, LLVMOrcResourceTrackerRef arg2, LLVMMemoryBufferRef arg3) { return LLVMOrcObjectLayerAddObjectFileWithRT(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_dd1827541218d53f (LLVMOrcObjectLayerRef arg1, LLVMOrcMaterializationResponsibilityRef arg2, LLVMMemoryBufferRef arg3) { LLVMOrcObjectLayerEmit(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_4fec439763be7824 (LLVMOrcObjectLayerRef arg1) { LLVMOrcDisposeObjectLayer(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_0ea7cdff38c9e224 (LLVMOrcIRTransformLayerRef arg1, LLVMOrcMaterializationResponsibilityRef arg2, LLVMOrcThreadSafeModuleRef arg3) { LLVMOrcIRTransformLayerEmit(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_555b697b852c504e (LLVMOrcIRTransformLayerRef arg1, LLVMOrcIRTransformLayerTransformFunction arg2, void *arg3) { LLVMOrcIRTransformLayerSetTransform(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Orc_56501e799c502a6f (LLVMOrcObjectTransformLayerRef arg1, LLVMOrcObjectTransformLayerTransformFunction arg2, void *arg3) { LLVMOrcObjectTransformLayerSetTransform(arg1, arg2, arg3); }\nLLVMOrcIndirectStubsManagerRef hs_bindgen_LlvmC_Raw_Orc_211c881d6dcd277b (char *arg1) { return LLVMOrcCreateLocalIndirectStubsManager(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Orc_b7b779fae7a32098 (LLVMOrcIndirectStubsManagerRef arg1) { LLVMOrcDisposeIndirectStubsManager(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_4fcf773d747b1220 (char *arg1, LLVMOrcExecutionSessionRef arg2, LLVMOrcJITTargetAddress arg3, LLVMOrcLazyCallThroughManagerRef *arg4) { return LLVMOrcCreateLocalLazyCallThroughManager(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Orc_1874c342d0a81527 (LLVMOrcLazyCallThroughManagerRef arg1) { LLVMOrcDisposeLazyCallThroughManager(arg1); }\nLLVMOrcDumpObjectsRef hs_bindgen_LlvmC_Raw_Orc_9b1fc66586cab827 (char *arg1, char *arg2) { return LLVMOrcCreateDumpObjects(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Orc_f720d0daa9d8f097 (LLVMOrcDumpObjectsRef arg1) { LLVMOrcDisposeDumpObjects(arg1); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Orc_a8533591989dedd5 (LLVMOrcDumpObjectsRef arg1, LLVMMemoryBufferRef *arg2) { return LLVMOrcDumpObjects_CallOperator(arg1, arg2); }\n")

newtype OrcJITTargetAddress = OrcJITTargetAddress
  { un_OrcJITTargetAddress :: HsBindgen.Runtime.Prelude.Word64
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype OrcExecutorAddress = OrcExecutorAddress
  { un_OrcExecutorAddress :: HsBindgen.Runtime.Prelude.Word64
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype JITSymbolGenericFlags = JITSymbolGenericFlags
  { un_JITSymbolGenericFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable JITSymbolGenericFlags where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure JITSymbolGenericFlags
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          JITSymbolGenericFlags un_JITSymbolGenericFlags2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_JITSymbolGenericFlags2

instance HsBindgen.Runtime.CEnum.CEnum JITSymbolGenericFlags where

  type CEnumZ JITSymbolGenericFlags = FC.CUInt

  toCEnum = JITSymbolGenericFlags

  fromCEnum = un_JITSymbolGenericFlags

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "JITSymbolGenericFlagsNone")
                                                     , (1, Data.List.NonEmpty.singleton "JITSymbolGenericFlagsExported")
                                                     , (2, Data.List.NonEmpty.singleton "JITSymbolGenericFlagsWeak")
                                                     , (4, Data.List.NonEmpty.singleton "JITSymbolGenericFlagsCallable")
                                                     , ( 8
                                                       , Data.List.NonEmpty.singleton "JITSymbolGenericFlagsMaterializationSideEffectsOnly"
                                                       )
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "JITSymbolGenericFlags"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "JITSymbolGenericFlags"

instance Show JITSymbolGenericFlags where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read JITSymbolGenericFlags where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern JITSymbolGenericFlagsNone :: JITSymbolGenericFlags
pattern JITSymbolGenericFlagsNone = JITSymbolGenericFlags 0

pattern JITSymbolGenericFlagsExported :: JITSymbolGenericFlags
pattern JITSymbolGenericFlagsExported = JITSymbolGenericFlags 1

pattern JITSymbolGenericFlagsWeak :: JITSymbolGenericFlags
pattern JITSymbolGenericFlagsWeak = JITSymbolGenericFlags 2

pattern JITSymbolGenericFlagsCallable :: JITSymbolGenericFlags
pattern JITSymbolGenericFlagsCallable = JITSymbolGenericFlags 4

pattern JITSymbolGenericFlagsMaterializationSideEffectsOnly :: JITSymbolGenericFlags
pattern JITSymbolGenericFlagsMaterializationSideEffectsOnly = JITSymbolGenericFlags 8

newtype JITSymbolTargetFlags = JITSymbolTargetFlags
  { un_JITSymbolTargetFlags :: HsBindgen.Runtime.Prelude.Word8
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

data JITSymbolFlags = JITSymbolFlags
  { jITSymbolFlags_GenericFlags :: HsBindgen.Runtime.Prelude.Word8
  , jITSymbolFlags_TargetFlags :: HsBindgen.Runtime.Prelude.Word8
  }
  deriving stock (Eq, Show)

instance F.Storable JITSymbolFlags where

  sizeOf = \_ -> (2 :: Int)

  alignment = \_ -> (1 :: Int)

  peek =
    \ptr0 ->
          pure JITSymbolFlags
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (1 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          JITSymbolFlags jITSymbolFlags_GenericFlags2 jITSymbolFlags_TargetFlags3 ->
               F.pokeByteOff ptr0 (0 :: Int) jITSymbolFlags_GenericFlags2
            >> F.pokeByteOff ptr0 (1 :: Int) jITSymbolFlags_TargetFlags3

data JITEvaluatedSymbol = JITEvaluatedSymbol
  { jITEvaluatedSymbol_Address :: OrcExecutorAddress
  , jITEvaluatedSymbol_Flags :: JITSymbolFlags
  }
  deriving stock (Eq, Show)

instance F.Storable JITEvaluatedSymbol where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure JITEvaluatedSymbol
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          JITEvaluatedSymbol jITEvaluatedSymbol_Address2 jITEvaluatedSymbol_Flags3 ->
               F.pokeByteOff ptr0 (0 :: Int) jITEvaluatedSymbol_Address2
            >> F.pokeByteOff ptr0 (8 :: Int) jITEvaluatedSymbol_Flags3

data OrcOpaqueExecutionSession

newtype OrcExecutionSessionRef = OrcExecutionSessionRef
  { un_OrcExecutionSessionRef :: F.Ptr OrcOpaqueExecutionSession
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcErrorReporterFunction = OrcErrorReporterFunction
  { un_OrcErrorReporterFunction :: F.FunPtr ((F.Ptr Void) -> LlvmC.Raw.Error.ErrorRef -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueSymbolStringPool

newtype OrcSymbolStringPoolRef = OrcSymbolStringPoolRef
  { un_OrcSymbolStringPoolRef :: F.Ptr OrcOpaqueSymbolStringPool
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueSymbolStringPoolEntry

newtype OrcSymbolStringPoolEntryRef = OrcSymbolStringPoolEntryRef
  { un_OrcSymbolStringPoolEntryRef :: F.Ptr OrcOpaqueSymbolStringPoolEntry
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcCSymbolFlagsMapPair = OrcCSymbolFlagsMapPair
  { orcCSymbolFlagsMapPair_Name :: OrcSymbolStringPoolEntryRef
  , orcCSymbolFlagsMapPair_Flags :: JITSymbolFlags
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolFlagsMapPair where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolFlagsMapPair
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolFlagsMapPair
            orcCSymbolFlagsMapPair_Name2
            orcCSymbolFlagsMapPair_Flags3 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCSymbolFlagsMapPair_Name2
              >> F.pokeByteOff ptr0 (8 :: Int) orcCSymbolFlagsMapPair_Flags3

newtype OrcCSymbolFlagsMapPairs = OrcCSymbolFlagsMapPairs
  { un_OrcCSymbolFlagsMapPairs :: F.Ptr OrcCSymbolFlagsMapPair
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcCSymbolMapPair = OrcCSymbolMapPair
  { orcCSymbolMapPair_Name :: OrcSymbolStringPoolEntryRef
  , orcCSymbolMapPair_Sym :: JITEvaluatedSymbol
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolMapPair where

  sizeOf = \_ -> (24 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolMapPair
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolMapPair orcCSymbolMapPair_Name2 orcCSymbolMapPair_Sym3 ->
               F.pokeByteOff ptr0 (0 :: Int) orcCSymbolMapPair_Name2
            >> F.pokeByteOff ptr0 (8 :: Int) orcCSymbolMapPair_Sym3

newtype OrcCSymbolMapPairs = OrcCSymbolMapPairs
  { un_OrcCSymbolMapPairs :: F.Ptr OrcCSymbolMapPair
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcCSymbolAliasMapEntry = OrcCSymbolAliasMapEntry
  { orcCSymbolAliasMapEntry_Name :: OrcSymbolStringPoolEntryRef
  , orcCSymbolAliasMapEntry_Flags :: JITSymbolFlags
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolAliasMapEntry where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolAliasMapEntry
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolAliasMapEntry
            orcCSymbolAliasMapEntry_Name2
            orcCSymbolAliasMapEntry_Flags3 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCSymbolAliasMapEntry_Name2
              >> F.pokeByteOff ptr0 (8 :: Int) orcCSymbolAliasMapEntry_Flags3

data OrcCSymbolAliasMapPair = OrcCSymbolAliasMapPair
  { orcCSymbolAliasMapPair_Name :: OrcSymbolStringPoolEntryRef
  , orcCSymbolAliasMapPair_Entry :: OrcCSymbolAliasMapEntry
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolAliasMapPair where

  sizeOf = \_ -> (24 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolAliasMapPair
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolAliasMapPair
            orcCSymbolAliasMapPair_Name2
            orcCSymbolAliasMapPair_Entry3 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCSymbolAliasMapPair_Name2
              >> F.pokeByteOff ptr0 (8 :: Int) orcCSymbolAliasMapPair_Entry3

newtype OrcCSymbolAliasMapPairs = OrcCSymbolAliasMapPairs
  { un_OrcCSymbolAliasMapPairs :: F.Ptr OrcCSymbolAliasMapPair
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueJITDylib

newtype OrcJITDylibRef = OrcJITDylibRef
  { un_OrcJITDylibRef :: F.Ptr OrcOpaqueJITDylib
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcCSymbolsList = OrcCSymbolsList
  { orcCSymbolsList_Symbols :: F.Ptr OrcSymbolStringPoolEntryRef
  , orcCSymbolsList_Length :: HsBindgen.Runtime.Prelude.CSize
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolsList where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolsList
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolsList orcCSymbolsList_Symbols2 orcCSymbolsList_Length3 ->
               F.pokeByteOff ptr0 (0 :: Int) orcCSymbolsList_Symbols2
            >> F.pokeByteOff ptr0 (8 :: Int) orcCSymbolsList_Length3

data OrcCDependenceMapPair = OrcCDependenceMapPair
  { orcCDependenceMapPair_JD :: OrcJITDylibRef
  , orcCDependenceMapPair_Names :: OrcCSymbolsList
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCDependenceMapPair where

  sizeOf = \_ -> (24 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCDependenceMapPair
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCDependenceMapPair orcCDependenceMapPair_JD2 orcCDependenceMapPair_Names3 ->
               F.pokeByteOff ptr0 (0 :: Int) orcCDependenceMapPair_JD2
            >> F.pokeByteOff ptr0 (8 :: Int) orcCDependenceMapPair_Names3

newtype OrcCDependenceMapPairs = OrcCDependenceMapPairs
  { un_OrcCDependenceMapPairs :: F.Ptr OrcCDependenceMapPair
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcCSymbolDependenceGroup = OrcCSymbolDependenceGroup
  { orcCSymbolDependenceGroup_Symbols :: OrcCSymbolsList
  , orcCSymbolDependenceGroup_Dependencies :: OrcCDependenceMapPairs
  , orcCSymbolDependenceGroup_NumDependencies :: HsBindgen.Runtime.Prelude.CSize
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCSymbolDependenceGroup where

  sizeOf = \_ -> (32 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCSymbolDependenceGroup
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (16 :: Int)
      <*> F.peekByteOff ptr0 (24 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCSymbolDependenceGroup
            orcCSymbolDependenceGroup_Symbols2
            orcCSymbolDependenceGroup_Dependencies3
            orcCSymbolDependenceGroup_NumDependencies4 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCSymbolDependenceGroup_Symbols2
              >> F.pokeByteOff ptr0 (16 :: Int) orcCSymbolDependenceGroup_Dependencies3
              >> F.pokeByteOff ptr0 (24 :: Int) orcCSymbolDependenceGroup_NumDependencies4

newtype OrcLookupKind = OrcLookupKind
  { un_OrcLookupKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable OrcLookupKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure OrcLookupKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcLookupKind un_OrcLookupKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_OrcLookupKind2

instance HsBindgen.Runtime.CEnum.CEnum OrcLookupKind where

  type CEnumZ OrcLookupKind = FC.CUInt

  toCEnum = OrcLookupKind

  fromCEnum = un_OrcLookupKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "OrcLookupKindStatic")
                                                     , (1, Data.List.NonEmpty.singleton "OrcLookupKindDLSym")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "OrcLookupKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "OrcLookupKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum OrcLookupKind where

  minDeclaredValue = OrcLookupKindStatic

  maxDeclaredValue = OrcLookupKindDLSym

instance Show OrcLookupKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read OrcLookupKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern OrcLookupKindStatic :: OrcLookupKind
pattern OrcLookupKindStatic = OrcLookupKind 0

pattern OrcLookupKindDLSym :: OrcLookupKind
pattern OrcLookupKindDLSym = OrcLookupKind 1

newtype OrcJITDylibLookupFlags = OrcJITDylibLookupFlags
  { un_OrcJITDylibLookupFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable OrcJITDylibLookupFlags where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure OrcJITDylibLookupFlags
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcJITDylibLookupFlags un_OrcJITDylibLookupFlags2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_OrcJITDylibLookupFlags2

instance HsBindgen.Runtime.CEnum.CEnum OrcJITDylibLookupFlags where

  type CEnumZ OrcJITDylibLookupFlags = FC.CUInt

  toCEnum = OrcJITDylibLookupFlags

  fromCEnum = un_OrcJITDylibLookupFlags

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ ( 0
                                                       , Data.List.NonEmpty.singleton "OrcJITDylibLookupFlagsMatchExportedSymbolsOnly"
                                                       )
                                                     , (1, Data.List.NonEmpty.singleton "OrcJITDylibLookupFlagsMatchAllSymbols")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "OrcJITDylibLookupFlags"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "OrcJITDylibLookupFlags"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum OrcJITDylibLookupFlags where

  minDeclaredValue =
    OrcJITDylibLookupFlagsMatchExportedSymbolsOnly

  maxDeclaredValue =
    OrcJITDylibLookupFlagsMatchAllSymbols

instance Show OrcJITDylibLookupFlags where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read OrcJITDylibLookupFlags where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern OrcJITDylibLookupFlagsMatchExportedSymbolsOnly :: OrcJITDylibLookupFlags
pattern OrcJITDylibLookupFlagsMatchExportedSymbolsOnly = OrcJITDylibLookupFlags 0

pattern OrcJITDylibLookupFlagsMatchAllSymbols :: OrcJITDylibLookupFlags
pattern OrcJITDylibLookupFlagsMatchAllSymbols = OrcJITDylibLookupFlags 1

data OrcCJITDylibSearchOrderElement = OrcCJITDylibSearchOrderElement
  { orcCJITDylibSearchOrderElement_JD :: OrcJITDylibRef
  , orcCJITDylibSearchOrderElement_JDLookupFlags :: OrcJITDylibLookupFlags
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCJITDylibSearchOrderElement where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCJITDylibSearchOrderElement
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCJITDylibSearchOrderElement
            orcCJITDylibSearchOrderElement_JD2
            orcCJITDylibSearchOrderElement_JDLookupFlags3 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCJITDylibSearchOrderElement_JD2
              >> F.pokeByteOff ptr0 (8 :: Int) orcCJITDylibSearchOrderElement_JDLookupFlags3

newtype OrcCJITDylibSearchOrder = OrcCJITDylibSearchOrder
  { un_OrcCJITDylibSearchOrder :: F.Ptr OrcCJITDylibSearchOrderElement
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcSymbolLookupFlags = OrcSymbolLookupFlags
  { un_OrcSymbolLookupFlags :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable OrcSymbolLookupFlags where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure OrcSymbolLookupFlags
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcSymbolLookupFlags un_OrcSymbolLookupFlags2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_OrcSymbolLookupFlags2

instance HsBindgen.Runtime.CEnum.CEnum OrcSymbolLookupFlags where

  type CEnumZ OrcSymbolLookupFlags = FC.CUInt

  toCEnum = OrcSymbolLookupFlags

  fromCEnum = un_OrcSymbolLookupFlags

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "OrcSymbolLookupFlagsRequiredSymbol")
                                                     , (1, Data.List.NonEmpty.singleton "OrcSymbolLookupFlagsWeaklyReferencedSymbol")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "OrcSymbolLookupFlags"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "OrcSymbolLookupFlags"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum OrcSymbolLookupFlags where

  minDeclaredValue = OrcSymbolLookupFlagsRequiredSymbol

  maxDeclaredValue =
    OrcSymbolLookupFlagsWeaklyReferencedSymbol

instance Show OrcSymbolLookupFlags where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read OrcSymbolLookupFlags where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern OrcSymbolLookupFlagsRequiredSymbol :: OrcSymbolLookupFlags
pattern OrcSymbolLookupFlagsRequiredSymbol = OrcSymbolLookupFlags 0

pattern OrcSymbolLookupFlagsWeaklyReferencedSymbol :: OrcSymbolLookupFlags
pattern OrcSymbolLookupFlagsWeaklyReferencedSymbol = OrcSymbolLookupFlags 1

data OrcCLookupSetElement = OrcCLookupSetElement
  { orcCLookupSetElement_Name :: OrcSymbolStringPoolEntryRef
  , orcCLookupSetElement_LookupFlags :: OrcSymbolLookupFlags
  }
  deriving stock (Eq, Show)

instance F.Storable OrcCLookupSetElement where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OrcCLookupSetElement
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OrcCLookupSetElement
            orcCLookupSetElement_Name2
            orcCLookupSetElement_LookupFlags3 ->
                 F.pokeByteOff ptr0 (0 :: Int) orcCLookupSetElement_Name2
              >> F.pokeByteOff ptr0 (8 :: Int) orcCLookupSetElement_LookupFlags3

newtype OrcCLookupSet = OrcCLookupSet
  { un_OrcCLookupSet :: F.Ptr OrcCLookupSetElement
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueMaterializationUnit

newtype OrcMaterializationUnitRef = OrcMaterializationUnitRef
  { un_OrcMaterializationUnitRef :: F.Ptr OrcOpaqueMaterializationUnit
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueMaterializationResponsibility

newtype OrcMaterializationResponsibilityRef = OrcMaterializationResponsibilityRef
  { un_OrcMaterializationResponsibilityRef :: F.Ptr OrcOpaqueMaterializationResponsibility
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcMaterializationUnitMaterializeFunction = OrcMaterializationUnitMaterializeFunction
  { un_OrcMaterializationUnitMaterializeFunction :: F.FunPtr ((F.Ptr Void) -> OrcMaterializationResponsibilityRef -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcMaterializationUnitDiscardFunction = OrcMaterializationUnitDiscardFunction
  { un_OrcMaterializationUnitDiscardFunction :: F.FunPtr ((F.Ptr Void) -> OrcJITDylibRef -> OrcSymbolStringPoolEntryRef -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcMaterializationUnitDestroyFunction = OrcMaterializationUnitDestroyFunction
  { un_OrcMaterializationUnitDestroyFunction :: F.FunPtr ((F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueResourceTracker

newtype OrcResourceTrackerRef = OrcResourceTrackerRef
  { un_OrcResourceTrackerRef :: F.Ptr OrcOpaqueResourceTracker
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueDefinitionGenerator

newtype OrcDefinitionGeneratorRef = OrcDefinitionGeneratorRef
  { un_OrcDefinitionGeneratorRef :: F.Ptr OrcOpaqueDefinitionGenerator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueLookupState

newtype OrcLookupStateRef = OrcLookupStateRef
  { un_OrcLookupStateRef :: F.Ptr OrcOpaqueLookupState
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcCAPIDefinitionGeneratorTryToGenerateFunction = OrcCAPIDefinitionGeneratorTryToGenerateFunction
  { un_OrcCAPIDefinitionGeneratorTryToGenerateFunction :: F.FunPtr (OrcDefinitionGeneratorRef -> (F.Ptr Void) -> (F.Ptr OrcLookupStateRef) -> OrcLookupKind -> OrcJITDylibRef -> OrcJITDylibLookupFlags -> OrcCLookupSet -> HsBindgen.Runtime.Prelude.CSize -> IO LlvmC.Raw.Error.ErrorRef)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcDisposeCAPIDefinitionGeneratorFunction = OrcDisposeCAPIDefinitionGeneratorFunction
  { un_OrcDisposeCAPIDefinitionGeneratorFunction :: F.FunPtr ((F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcSymbolPredicate = OrcSymbolPredicate
  { un_OrcSymbolPredicate :: F.FunPtr ((F.Ptr Void) -> OrcSymbolStringPoolEntryRef -> IO FC.CInt)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueThreadSafeContext

newtype OrcThreadSafeContextRef = OrcThreadSafeContextRef
  { un_OrcThreadSafeContextRef :: F.Ptr OrcOpaqueThreadSafeContext
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueThreadSafeModule

newtype OrcThreadSafeModuleRef = OrcThreadSafeModuleRef
  { un_OrcThreadSafeModuleRef :: F.Ptr OrcOpaqueThreadSafeModule
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcGenericIRModuleOperationFunction = OrcGenericIRModuleOperationFunction
  { un_OrcGenericIRModuleOperationFunction :: F.FunPtr ((F.Ptr Void) -> LlvmC.Raw.Types.ModuleRef -> IO LlvmC.Raw.Error.ErrorRef)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueJITTargetMachineBuilder

newtype OrcJITTargetMachineBuilderRef = OrcJITTargetMachineBuilderRef
  { un_OrcJITTargetMachineBuilderRef :: F.Ptr OrcOpaqueJITTargetMachineBuilder
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueObjectLayer

newtype OrcObjectLayerRef = OrcObjectLayerRef
  { un_OrcObjectLayerRef :: F.Ptr OrcOpaqueObjectLayer
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueObjectLinkingLayer

newtype OrcObjectLinkingLayerRef = OrcObjectLinkingLayerRef
  { un_OrcObjectLinkingLayerRef :: F.Ptr OrcOpaqueObjectLinkingLayer
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueIRTransformLayer

newtype OrcIRTransformLayerRef = OrcIRTransformLayerRef
  { un_OrcIRTransformLayerRef :: F.Ptr OrcOpaqueIRTransformLayer
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcIRTransformLayerTransformFunction = OrcIRTransformLayerTransformFunction
  { un_OrcIRTransformLayerTransformFunction :: F.FunPtr ((F.Ptr Void) -> (F.Ptr OrcThreadSafeModuleRef) -> OrcMaterializationResponsibilityRef -> IO LlvmC.Raw.Error.ErrorRef)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueObjectTransformLayer

newtype OrcObjectTransformLayerRef = OrcObjectTransformLayerRef
  { un_OrcObjectTransformLayerRef :: F.Ptr OrcOpaqueObjectTransformLayer
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OrcObjectTransformLayerTransformFunction = OrcObjectTransformLayerTransformFunction
  { un_OrcObjectTransformLayerTransformFunction :: F.FunPtr ((F.Ptr Void) -> (F.Ptr LlvmC.Raw.Types.MemoryBufferRef) -> IO LlvmC.Raw.Error.ErrorRef)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueIndirectStubsManager

newtype OrcIndirectStubsManagerRef = OrcIndirectStubsManagerRef
  { un_OrcIndirectStubsManagerRef :: F.Ptr OrcOpaqueIndirectStubsManager
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueLazyCallThroughManager

newtype OrcLazyCallThroughManagerRef = OrcLazyCallThroughManagerRef
  { un_OrcLazyCallThroughManagerRef :: F.Ptr OrcOpaqueLazyCallThroughManager
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueDumpObjects

newtype OrcDumpObjectsRef = OrcDumpObjectsRef
  { un_OrcDumpObjectsRef :: F.Ptr OrcOpaqueDumpObjects
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_80cac539f65c98e3" orcExecutionSessionSetErrorReporter
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> OrcErrorReporterFunction
     {- ^ __from C:__ @reportError@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_3fe7853bc1c892b3" orcExecutionSessionGetSymbolStringPool
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> IO OrcSymbolStringPoolRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_8653565e907ad0c4" orcSymbolStringPoolClearDeadEntries
  :: OrcSymbolStringPoolRef
     {- ^ __from C:__ @sSP@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_c45654f85472c38b" orcExecutionSessionIntern
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO OrcSymbolStringPoolEntryRef

newtype OrcExecutionSessionLookupHandleResultFunction = OrcExecutionSessionLookupHandleResultFunction
  { un_OrcExecutionSessionLookupHandleResultFunction :: F.FunPtr (LlvmC.Raw.Error.ErrorRef -> OrcCSymbolMapPairs -> HsBindgen.Runtime.Prelude.CSize -> (F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_af6e3c583251abc0" orcExecutionSessionLookup
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> OrcLookupKind
     {- ^ __from C:__ @k@ -}
  -> OrcCJITDylibSearchOrder
     {- ^ __from C:__ @searchOrder@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @searchOrderSize@ -}
  -> OrcCLookupSet
     {- ^ __from C:__ @symbols@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @symbolsSize@ -}
  -> OrcExecutionSessionLookupHandleResultFunction
     {- ^ __from C:__ @handleResult@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_ae85ff71eb635922" orcRetainSymbolStringPoolEntry
  :: OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @s@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_83e497e3b769bbbf" orcReleaseSymbolStringPoolEntry
  :: OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @s@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_5f15676ce9260838" orcSymbolStringPoolEntryStr
  :: OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @s@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_e3180549942dad3d" orcReleaseResourceTracker
  :: OrcResourceTrackerRef
     {- ^ __from C:__ @rT@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_76a919d380367281" orcResourceTrackerTransferTo
  :: OrcResourceTrackerRef
     {- ^ __from C:__ @srcRT@ -}
  -> OrcResourceTrackerRef
     {- ^ __from C:__ @dstRT@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_fb9c5df70deca22a" orcResourceTrackerRemove
  :: OrcResourceTrackerRef
     {- ^ __from C:__ @rT@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_3ee44d84db9b0096" orcDisposeDefinitionGenerator
  :: OrcDefinitionGeneratorRef
     {- ^ __from C:__ @dG@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_e4190d4f68475f08" orcDisposeMaterializationUnit
  :: OrcMaterializationUnitRef
     {- ^ __from C:__ @mU@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_5e3fcd5dfec681d5" orcCreateCustomMaterializationUnit
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> OrcCSymbolFlagsMapPairs
     {- ^ __from C:__ @syms@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numSyms@ -}
  -> OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @initSym@ -}
  -> OrcMaterializationUnitMaterializeFunction
     {- ^ __from C:__ @materialize@ -}
  -> OrcMaterializationUnitDiscardFunction
     {- ^ __from C:__ @discard@ -}
  -> OrcMaterializationUnitDestroyFunction
     {- ^ __from C:__ @destroy@ -}
  -> IO OrcMaterializationUnitRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_5e3ca1bf3162960a" orcAbsoluteSymbols
  :: OrcCSymbolMapPairs
     {- ^ __from C:__ @syms@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numPairs@ -}
  -> IO OrcMaterializationUnitRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_235a19d63d848c73" orcLazyReexports
  :: OrcLazyCallThroughManagerRef
     {- ^ __from C:__ @lCTM@ -}
  -> OrcIndirectStubsManagerRef
     {- ^ __from C:__ @iSM@ -}
  -> OrcJITDylibRef
     {- ^ __from C:__ @sourceRef@ -}
  -> OrcCSymbolAliasMapPairs
     {- ^ __from C:__ @callableAliases@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numPairs@ -}
  -> IO OrcMaterializationUnitRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_af8dda30a5dc259d" orcDisposeMaterializationResponsibility
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_fd4c60cb48a411bd" orcMaterializationResponsibilityGetTargetDylib
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> IO OrcJITDylibRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_20ba4f5565315eee" orcMaterializationResponsibilityGetExecutionSession
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> IO OrcExecutionSessionRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_7c9c665c342ad7ed" orcMaterializationResponsibilityGetSymbols
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numPairs@ -}
  -> IO OrcCSymbolFlagsMapPairs

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_a06c88ef8a37e2da" orcDisposeCSymbolFlagsMap
  :: OrcCSymbolFlagsMapPairs
     {- ^ __from C:__ @pairs@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_645f2d7335f80a0b" orcMaterializationResponsibilityGetInitializerSymbol
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> IO OrcSymbolStringPoolEntryRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_97cafeb7da90f71e" orcMaterializationResponsibilityGetRequestedSymbols
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numSymbols@ -}
  -> IO (F.Ptr OrcSymbolStringPoolEntryRef)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_25a12914ad25f53c" orcDisposeSymbols
  :: F.Ptr OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @symbols@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_e2f67e0a09be17f4" orcMaterializationResponsibilityNotifyResolved
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> OrcCSymbolMapPairs
     {- ^ __from C:__ @symbols@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numPairs@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_7d0916eb0c14f194" orcMaterializationResponsibilityNotifyEmitted
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> F.Ptr OrcCSymbolDependenceGroup
     {- ^ __from C:__ @symbolDepGroups@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numSymbolDepGroups@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_cbf5d04f11b1a808" orcMaterializationResponsibilityDefineMaterializing
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> OrcCSymbolFlagsMapPairs
     {- ^ __from C:__ @pairs@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numPairs@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_444f59b8560fffde" orcMaterializationResponsibilityFailMaterialization
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_0e96a580c4a36ca3" orcMaterializationResponsibilityReplace
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> OrcMaterializationUnitRef
     {- ^ __from C:__ @mU@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_4d46ec996727d1ec" orcMaterializationResponsibilityDelegate
  :: OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> F.Ptr OrcSymbolStringPoolEntryRef
     {- ^ __from C:__ @symbols@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @numSymbols@ -}
  -> F.Ptr OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @result@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_22da2c0012306c7c" orcExecutionSessionCreateBareJITDylib
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO OrcJITDylibRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_d02c3dc7774da5a7" orcExecutionSessionCreateJITDylib
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> F.Ptr OrcJITDylibRef
     {- ^ __from C:__ @result@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_0e71b205a2540305" orcExecutionSessionGetJITDylibByName
  :: OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO OrcJITDylibRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_d9d42b76a83e37d8" orcJITDylibCreateResourceTracker
  :: OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> IO OrcResourceTrackerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_5a9ae9924b9bf92d" orcJITDylibGetDefaultResourceTracker
  :: OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> IO OrcResourceTrackerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_2e97a49ad0a41a94" orcJITDylibDefine
  :: OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> OrcMaterializationUnitRef
     {- ^ __from C:__ @mU@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_cd318a7d484413bf" orcJITDylibClear
  :: OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_d55f342eb5e3bcf3" orcJITDylibAddGenerator
  :: OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> OrcDefinitionGeneratorRef
     {- ^ __from C:__ @dG@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_3c7d40d88e9f9b0c" orcCreateCustomCAPIDefinitionGenerator
  :: OrcCAPIDefinitionGeneratorTryToGenerateFunction
     {- ^ __from C:__ @f@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> OrcDisposeCAPIDefinitionGeneratorFunction
     {- ^ __from C:__ @dispose@ -}
  -> IO OrcDefinitionGeneratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_81356ea06afd4d01" orcLookupStateContinueLookup
  :: OrcLookupStateRef
     {- ^ __from C:__ @s@ -}
  -> LlvmC.Raw.Error.ErrorRef
     {- ^ __from C:__ @err@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_6299438581db04b1" orcCreateDynamicLibrarySearchGeneratorForProcess
  :: F.Ptr OrcDefinitionGeneratorRef
     {- ^ __from C:__ @result@ -}
  -> FC.CChar
     {- ^ __from C:__ @globalPrefx@ -}
  -> OrcSymbolPredicate
     {- ^ __from C:__ @filter@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @filterCtx@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_f1cbf077b7feea7e" orcCreateDynamicLibrarySearchGeneratorForPath
  :: F.Ptr OrcDefinitionGeneratorRef
     {- ^ __from C:__ @result@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @fileName@ -}
  -> FC.CChar
     {- ^ __from C:__ @globalPrefix@ -}
  -> OrcSymbolPredicate
     {- ^ __from C:__ @filter@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @filterCtx@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_1790b24c5dbafdd7" orcCreateStaticLibrarySearchGeneratorForPath
  :: F.Ptr OrcDefinitionGeneratorRef
     {- ^ __from C:__ @result@ -}
  -> OrcObjectLayerRef
     {- ^ __from C:__ @objLayer@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @fileName@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @targetTriple@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_848b8091895d8f9d" orcCreateNewThreadSafeContext
  :: IO OrcThreadSafeContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_b9bb1dbda13d3161" orcThreadSafeContextGetContext
  :: OrcThreadSafeContextRef
     {- ^ __from C:__ @tSCtx@ -}
  -> IO LlvmC.Raw.Types.ContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_7fee397c0ecb33dd" orcDisposeThreadSafeContext
  :: OrcThreadSafeContextRef
     {- ^ __from C:__ @tSCtx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_dfc9438c9e8bb47d" orcCreateNewThreadSafeModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> OrcThreadSafeContextRef
     {- ^ __from C:__ @tSCtx@ -}
  -> IO OrcThreadSafeModuleRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_641f0e28b2e0c847" orcDisposeThreadSafeModule
  :: OrcThreadSafeModuleRef
     {- ^ __from C:__ @tSM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_26eb77c11b031f34" orcThreadSafeModuleWithModuleDo
  :: OrcThreadSafeModuleRef
     {- ^ __from C:__ @tSM@ -}
  -> OrcGenericIRModuleOperationFunction
     {- ^ __from C:__ @f@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_426fe61196aa83a2" orcJITTargetMachineBuilderDetectHost
  :: F.Ptr OrcJITTargetMachineBuilderRef
     {- ^ __from C:__ @result@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_11e32d8e8d879228" orcJITTargetMachineBuilderCreateFromTargetMachine
  :: LlvmC.Raw.TargetMachine.TargetMachineRef
     {- ^ __from C:__ @tM@ -}
  -> IO OrcJITTargetMachineBuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_9be8d232f268bc19" orcDisposeJITTargetMachineBuilder
  :: OrcJITTargetMachineBuilderRef
     {- ^ __from C:__ @jTMB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_e67cf259873429c1" orcJITTargetMachineBuilderGetTargetTriple
  :: OrcJITTargetMachineBuilderRef
     {- ^ __from C:__ @jTMB@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_50580393911066c1" orcJITTargetMachineBuilderSetTargetTriple
  :: OrcJITTargetMachineBuilderRef
     {- ^ __from C:__ @jTMB@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @targetTriple@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_5dd823fea0ad4032" orcObjectLayerAddObjectFile
  :: OrcObjectLayerRef
     {- ^ __from C:__ @objLayer@ -}
  -> OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_7cb2ffb598aa4e51" orcObjectLayerAddObjectFileWithRT
  :: OrcObjectLayerRef
     {- ^ __from C:__ @objLayer@ -}
  -> OrcResourceTrackerRef
     {- ^ __from C:__ @rT@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_dd1827541218d53f" orcObjectLayerEmit
  :: OrcObjectLayerRef
     {- ^ __from C:__ @objLayer@ -}
  -> OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @r@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_4fec439763be7824" orcDisposeObjectLayer
  :: OrcObjectLayerRef
     {- ^ __from C:__ @objLayer@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_0ea7cdff38c9e224" orcIRTransformLayerEmit
  :: OrcIRTransformLayerRef
     {- ^ __from C:__ @iRTransformLayer@ -}
  -> OrcMaterializationResponsibilityRef
     {- ^ __from C:__ @mR@ -}
  -> OrcThreadSafeModuleRef
     {- ^ __from C:__ @tSM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_555b697b852c504e" orcIRTransformLayerSetTransform
  :: OrcIRTransformLayerRef
     {- ^ __from C:__ @iRTransformLayer@ -}
  -> OrcIRTransformLayerTransformFunction
     {- ^ __from C:__ @transformFunction@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_56501e799c502a6f" orcObjectTransformLayerSetTransform
  :: OrcObjectTransformLayerRef
     {- ^ __from C:__ @objTransformLayer@ -}
  -> OrcObjectTransformLayerTransformFunction
     {- ^ __from C:__ @transformFunction@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_211c881d6dcd277b" orcCreateLocalIndirectStubsManager
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @targetTriple@ -}
  -> IO OrcIndirectStubsManagerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_b7b779fae7a32098" orcDisposeIndirectStubsManager
  :: OrcIndirectStubsManagerRef
     {- ^ __from C:__ @iSM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_4fcf773d747b1220" orcCreateLocalLazyCallThroughManager
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @targetTriple@ -}
  -> OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> OrcJITTargetAddress
     {- ^ __from C:__ @errorHandlerAddr@ -}
  -> F.Ptr OrcLazyCallThroughManagerRef
     {- ^ __from C:__ @lCTM@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_1874c342d0a81527" orcDisposeLazyCallThroughManager
  :: OrcLazyCallThroughManagerRef
     {- ^ __from C:__ @lCTM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_9b1fc66586cab827" orcCreateDumpObjects
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @dumpDir@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @identifierOverride@ -}
  -> IO OrcDumpObjectsRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_f720d0daa9d8f097" orcDisposeDumpObjects
  :: OrcDumpObjectsRef
     {- ^ __from C:__ @dumpObjects@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Orc_a8533591989dedd5" orcDumpObjects_CallOperator
  :: OrcDumpObjectsRef
     {- ^ __from C:__ @dumpObjects@ -}
  -> F.Ptr LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO LlvmC.Raw.Error.ErrorRef
