{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.OrcEE where

import Data.Void (Void)
import qualified Foreign as F
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.ExecutionEngine
import qualified LlvmC.Raw.Orc
import qualified LlvmC.Raw.Types
import Prelude (Eq, IO, Ord, Show)

$(CAPI.addCSource "#define const\n#include <llvm-c/OrcEE.h>\nLLVMOrcObjectLayerRef hs_bindgen_LlvmC_Raw_OrcEE_9f31d8434d27bfd8 (LLVMOrcExecutionSessionRef arg1) { return LLVMOrcCreateRTDyldObjectLinkingLayerWithSectionMemoryManager(arg1); }\nLLVMOrcObjectLayerRef hs_bindgen_LlvmC_Raw_OrcEE_b039cf114528105a (LLVMOrcExecutionSessionRef arg1, void *arg2, LLVMMemoryManagerCreateContextCallback arg3, LLVMMemoryManagerNotifyTerminatingCallback arg4, LLVMMemoryManagerAllocateCodeSectionCallback arg5, LLVMMemoryManagerAllocateDataSectionCallback arg6, LLVMMemoryManagerFinalizeMemoryCallback arg7, LLVMMemoryManagerDestroyCallback arg8) { return LLVMOrcCreateRTDyldObjectLinkingLayerWithMCJITMemoryManagerLikeCallbacks(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8); }\nvoid hs_bindgen_LlvmC_Raw_OrcEE_210a9d9374df3481 (LLVMOrcObjectLayerRef arg1, LLVMJITEventListenerRef arg2) { LLVMOrcRTDyldObjectLinkingLayerRegisterJITEventListener(arg1, arg2); }\n")

newtype MemoryManagerCreateContextCallback = MemoryManagerCreateContextCallback
  { un_MemoryManagerCreateContextCallback :: F.FunPtr ((F.Ptr Void) -> IO (F.Ptr Void))
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype MemoryManagerNotifyTerminatingCallback = MemoryManagerNotifyTerminatingCallback
  { un_MemoryManagerNotifyTerminatingCallback :: F.FunPtr ((F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_OrcEE_9f31d8434d27bfd8" orcCreateRTDyldObjectLinkingLayerWithSectionMemoryManager
  :: LlvmC.Raw.Orc.OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> IO LlvmC.Raw.Orc.OrcObjectLayerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_OrcEE_b039cf114528105a" orcCreateRTDyldObjectLinkingLayerWithMCJITMemoryManagerLikeCallbacks
  :: LlvmC.Raw.Orc.OrcExecutionSessionRef
     {- ^ __from C:__ @eS@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @createContextCtx@ -}
  -> MemoryManagerCreateContextCallback
     {- ^ __from C:__ @createContext@ -}
  -> MemoryManagerNotifyTerminatingCallback
     {- ^ __from C:__ @notifyTerminating@ -}
  -> LlvmC.Raw.ExecutionEngine.MemoryManagerAllocateCodeSectionCallback
     {- ^ __from C:__ @allocateCodeSection@ -}
  -> LlvmC.Raw.ExecutionEngine.MemoryManagerAllocateDataSectionCallback
     {- ^ __from C:__ @allocateDataSection@ -}
  -> LlvmC.Raw.ExecutionEngine.MemoryManagerFinalizeMemoryCallback
     {- ^ __from C:__ @finalizeMemory@ -}
  -> LlvmC.Raw.ExecutionEngine.MemoryManagerDestroyCallback
     {- ^ __from C:__ @destroy@ -}
  -> IO LlvmC.Raw.Orc.OrcObjectLayerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_OrcEE_210a9d9374df3481" orcRTDyldObjectLinkingLayerRegisterJITEventListener
  :: LlvmC.Raw.Orc.OrcObjectLayerRef
     {- ^ __from C:__ @rTDyldObjLinkingLayer@ -}
  -> LlvmC.Raw.Types.JITEventListenerRef
     {- ^ __from C:__ @listener@ -}
  -> IO ()
