{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.LLJIT where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Error
import qualified LlvmC.Raw.Orc
import qualified LlvmC.Raw.Types
import Prelude (Eq, IO, Ord, Show)

$(CAPI.addCSource "#define const\n#include <llvm-c/LLJIT.h>\nLLVMOrcLLJITBuilderRef hs_bindgen_LlvmC_Raw_LLJIT_11d358ee1aae3c62 (void) { return LLVMOrcCreateLLJITBuilder(); }\nvoid hs_bindgen_LlvmC_Raw_LLJIT_5dd62ad9d229958f (LLVMOrcLLJITBuilderRef arg1) { LLVMOrcDisposeLLJITBuilder(arg1); }\nvoid hs_bindgen_LlvmC_Raw_LLJIT_2b71b49fa1a35e8c (LLVMOrcLLJITBuilderRef arg1, LLVMOrcJITTargetMachineBuilderRef arg2) { LLVMOrcLLJITBuilderSetJITTargetMachineBuilder(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_LLJIT_4fe1aa27389bcc51 (LLVMOrcLLJITBuilderRef arg1, LLVMOrcLLJITBuilderObjectLinkingLayerCreatorFunction arg2, void *arg3) { LLVMOrcLLJITBuilderSetObjectLinkingLayerCreator(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_a749748ccd88d22b (LLVMOrcLLJITRef *arg1, LLVMOrcLLJITBuilderRef arg2) { return LLVMOrcCreateLLJIT(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_eb705a3bec3a93c7 (LLVMOrcLLJITRef arg1) { return LLVMOrcDisposeLLJIT(arg1); }\nLLVMOrcExecutionSessionRef hs_bindgen_LlvmC_Raw_LLJIT_38045e1fd55757a5 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetExecutionSession(arg1); }\nLLVMOrcJITDylibRef hs_bindgen_LlvmC_Raw_LLJIT_156618771b9b335d (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetMainJITDylib(arg1); }\nchar *hs_bindgen_LlvmC_Raw_LLJIT_144b55f0ebe4f2c9 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetTripleString(arg1); }\nchar hs_bindgen_LlvmC_Raw_LLJIT_15fdf1c4141b5c06 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetGlobalPrefix(arg1); }\nLLVMOrcSymbolStringPoolEntryRef hs_bindgen_LlvmC_Raw_LLJIT_d15150a99e45e7c6 (LLVMOrcLLJITRef arg1, char *arg2) { return LLVMOrcLLJITMangleAndIntern(arg1, arg2); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_aebff8072e18a0a9 (LLVMOrcLLJITRef arg1, LLVMOrcJITDylibRef arg2, LLVMMemoryBufferRef arg3) { return LLVMOrcLLJITAddObjectFile(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_83d06d3d5a111160 (LLVMOrcLLJITRef arg1, LLVMOrcResourceTrackerRef arg2, LLVMMemoryBufferRef arg3) { return LLVMOrcLLJITAddObjectFileWithRT(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_39d2287e4ba8937e (LLVMOrcLLJITRef arg1, LLVMOrcJITDylibRef arg2, LLVMOrcThreadSafeModuleRef arg3) { return LLVMOrcLLJITAddLLVMIRModule(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_26c927db3df039b2 (LLVMOrcLLJITRef arg1, LLVMOrcResourceTrackerRef arg2, LLVMOrcThreadSafeModuleRef arg3) { return LLVMOrcLLJITAddLLVMIRModuleWithRT(arg1, arg2, arg3); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJIT_2cc8325446051644 (LLVMOrcLLJITRef arg1, LLVMOrcExecutorAddress *arg2, char *arg3) { return LLVMOrcLLJITLookup(arg1, arg2, arg3); }\nLLVMOrcObjectLayerRef hs_bindgen_LlvmC_Raw_LLJIT_f17d40d782b2aa60 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetObjLinkingLayer(arg1); }\nLLVMOrcObjectTransformLayerRef hs_bindgen_LlvmC_Raw_LLJIT_c2e04680f5f1bccd (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetObjTransformLayer(arg1); }\nLLVMOrcIRTransformLayerRef hs_bindgen_LlvmC_Raw_LLJIT_a9810c2e8e979286 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetIRTransformLayer(arg1); }\nchar *hs_bindgen_LlvmC_Raw_LLJIT_3410daa6c1130640 (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITGetDataLayoutStr(arg1); }\n")

newtype OrcLLJITBuilderObjectLinkingLayerCreatorFunction = OrcLLJITBuilderObjectLinkingLayerCreatorFunction
  { un_OrcLLJITBuilderObjectLinkingLayerCreatorFunction :: F.FunPtr ((F.Ptr Void) -> LlvmC.Raw.Orc.OrcExecutionSessionRef -> (F.Ptr FC.CChar) -> IO LlvmC.Raw.Orc.OrcObjectLayerRef)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueLLJITBuilder

newtype OrcLLJITBuilderRef = OrcLLJITBuilderRef
  { un_OrcLLJITBuilderRef :: F.Ptr OrcOpaqueLLJITBuilder
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OrcOpaqueLLJIT

newtype OrcLLJITRef = OrcLLJITRef
  { un_OrcLLJITRef :: F.Ptr OrcOpaqueLLJIT
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_11d358ee1aae3c62" orcCreateLLJITBuilder
  :: IO OrcLLJITBuilderRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_5dd62ad9d229958f" orcDisposeLLJITBuilder
  :: OrcLLJITBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_2b71b49fa1a35e8c" orcLLJITBuilderSetJITTargetMachineBuilder
  :: OrcLLJITBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> LlvmC.Raw.Orc.OrcJITTargetMachineBuilderRef
     {- ^ __from C:__ @jTMB@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_4fe1aa27389bcc51" orcLLJITBuilderSetObjectLinkingLayerCreator
  :: OrcLLJITBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> OrcLLJITBuilderObjectLinkingLayerCreatorFunction
     {- ^ __from C:__ @f@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @ctx@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_a749748ccd88d22b" orcCreateLLJIT
  :: F.Ptr OrcLLJITRef
     {- ^ __from C:__ @result@ -}
  -> OrcLLJITBuilderRef
     {- ^ __from C:__ @builder@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_eb705a3bec3a93c7" orcDisposeLLJIT
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_38045e1fd55757a5" orcLLJITGetExecutionSession
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Orc.OrcExecutionSessionRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_156618771b9b335d" orcLLJITGetMainJITDylib
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Orc.OrcJITDylibRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_144b55f0ebe4f2c9" orcLLJITGetTripleString
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_15fdf1c4141b5c06" orcLLJITGetGlobalPrefix
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO FC.CChar

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_d15150a99e45e7c6" orcLLJITMangleAndIntern
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @unmangledName@ -}
  -> IO LlvmC.Raw.Orc.OrcSymbolStringPoolEntryRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_aebff8072e18a0a9" orcLLJITAddObjectFile
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> LlvmC.Raw.Orc.OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_83d06d3d5a111160" orcLLJITAddObjectFileWithRT
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> LlvmC.Raw.Orc.OrcResourceTrackerRef
     {- ^ __from C:__ @rT@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @objBuffer@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_39d2287e4ba8937e" orcLLJITAddLLVMIRModule
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> LlvmC.Raw.Orc.OrcJITDylibRef
     {- ^ __from C:__ @jD@ -}
  -> LlvmC.Raw.Orc.OrcThreadSafeModuleRef
     {- ^ __from C:__ @tSM@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_26c927db3df039b2" orcLLJITAddLLVMIRModuleWithRT
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> LlvmC.Raw.Orc.OrcResourceTrackerRef
     {- ^ __from C:__ @jD@ -}
  -> LlvmC.Raw.Orc.OrcThreadSafeModuleRef
     {- ^ __from C:__ @tSM@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_2cc8325446051644" orcLLJITLookup
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> F.Ptr LlvmC.Raw.Orc.OrcExecutorAddress
     {- ^ __from C:__ @result@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Error.ErrorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_f17d40d782b2aa60" orcLLJITGetObjLinkingLayer
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Orc.OrcObjectLayerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_c2e04680f5f1bccd" orcLLJITGetObjTransformLayer
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Orc.OrcObjectTransformLayerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_a9810c2e8e979286" orcLLJITGetIRTransformLayer
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Orc.OrcIRTransformLayerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJIT_3410daa6c1130640" orcLLJITGetDataLayoutStr
  :: OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO (F.Ptr FC.CChar)
