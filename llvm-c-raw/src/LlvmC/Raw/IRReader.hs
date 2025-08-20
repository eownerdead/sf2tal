{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.IRReader where

import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Types
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/IRReader.h>\nLLVMBool hs_bindgen_LlvmC_Raw_IRReader_3b026383eca1a148 (LLVMContextRef arg1, LLVMMemoryBufferRef arg2, LLVMModuleRef *arg3, char **arg4) { return LLVMParseIRInContext(arg1, arg2, arg3, arg4); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_IRReader_3b026383eca1a148" parseIRInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @contextRef@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outM@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool
