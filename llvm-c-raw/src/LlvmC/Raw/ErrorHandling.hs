{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.ErrorHandling where

import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import Prelude (Eq, IO, Ord, Show)

$(CAPI.addCSource "#define const\n#include <llvm-c/ErrorHandling.h>\nvoid hs_bindgen_LlvmC_Raw_ErrorHandling_13a8084437e6141a (LLVMFatalErrorHandler arg1) { LLVMInstallFatalErrorHandler(arg1); }\nvoid hs_bindgen_LlvmC_Raw_ErrorHandling_dff28cce3e95a535 (void) { LLVMResetFatalErrorHandler(); }\nvoid hs_bindgen_LlvmC_Raw_ErrorHandling_a3e8208b5da585c3 (void) { LLVMEnablePrettyStackTrace(); }\n")

newtype FatalErrorHandler = FatalErrorHandler
  { un_FatalErrorHandler :: F.FunPtr ((F.Ptr FC.CChar) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ErrorHandling_13a8084437e6141a" installFatalErrorHandler
  :: FatalErrorHandler
     {- ^ __from C:__ @handler@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ErrorHandling_dff28cce3e95a535" resetFatalErrorHandler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ErrorHandling_a3e8208b5da585c3" enablePrettyStackTrace
  :: IO ()
