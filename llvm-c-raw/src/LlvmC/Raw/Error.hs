{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.Error where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import Prelude (Eq, IO, Ord, Show)

$(CAPI.addCSource "#define const\n#include <llvm-c/Error.h>\nLLVMErrorTypeId hs_bindgen_LlvmC_Raw_Error_2c107525bd25556e (LLVMErrorRef arg1) { return LLVMGetErrorTypeId(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Error_2e8f7955a5b01e96 (LLVMErrorRef arg1) { LLVMConsumeError(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Error_f775c52a7f7da9f4 (LLVMErrorRef arg1) { return LLVMGetErrorMessage(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Error_d5d83c63069ffb3b (char *arg1) { LLVMDisposeErrorMessage(arg1); }\nLLVMErrorTypeId hs_bindgen_LlvmC_Raw_Error_94207b4887daf5ac (void) { return LLVMGetStringErrorTypeId(); }\nLLVMErrorRef hs_bindgen_LlvmC_Raw_Error_849815ab53541e3d (char *arg1) { return LLVMCreateStringError(arg1); }\n")

data OpaqueError

newtype ErrorRef = ErrorRef
  { un_ErrorRef :: F.Ptr OpaqueError
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype ErrorTypeId = ErrorTypeId
  { un_ErrorTypeId :: F.Ptr Void
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_2c107525bd25556e" getErrorTypeId
  :: ErrorRef
     {- ^ __from C:__ @err@ -}
  -> IO ErrorTypeId

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_2e8f7955a5b01e96" consumeError
  :: ErrorRef
     {- ^ __from C:__ @err@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_f775c52a7f7da9f4" getErrorMessage
  :: ErrorRef
     {- ^ __from C:__ @err@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_d5d83c63069ffb3b" disposeErrorMessage
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @errMsg@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_94207b4887daf5ac" getStringErrorTypeId
  :: IO ErrorTypeId

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Error_849815ab53541e3d" createStringError
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @errMsg@ -}
  -> IO ErrorRef
