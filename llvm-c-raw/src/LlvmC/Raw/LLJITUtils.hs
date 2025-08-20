{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.LLJITUtils where

import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Error
import qualified LlvmC.Raw.LLJIT
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/LLJITUtils.h>\nLLVMErrorRef hs_bindgen_LlvmC_Raw_LLJITUtils_43282d3db17cfebc (LLVMOrcLLJITRef arg1) { return LLVMOrcLLJITEnableDebugSupport(arg1); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_LLJITUtils_43282d3db17cfebc" orcLLJITEnableDebugSupport
  :: LlvmC.Raw.LLJIT.OrcLLJITRef
     {- ^ __from C:__ @j@ -}
  -> IO LlvmC.Raw.Error.ErrorRef
