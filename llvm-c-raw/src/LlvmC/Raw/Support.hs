{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.Support where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Types
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/Support.h>\nLLVMBool hs_bindgen_LlvmC_Raw_Support_236a15d981789882 (char *arg1) { return LLVMLoadLibraryPermanently(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Support_19caa03a2338854e (signed int arg1, char **arg2, char *arg3) { LLVMParseCommandLineOptions(arg1, arg2, arg3); }\nvoid *hs_bindgen_LlvmC_Raw_Support_7856a581439a1800 (char *arg1) { return LLVMSearchForAddressOfSymbol(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Support_8c981b9374777106 (char *arg1, void *arg2) { LLVMAddSymbol(arg1, arg2); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Support_236a15d981789882" loadLibraryPermanently
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @filename@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Support_19caa03a2338854e" parseCommandLineOptions
  :: FC.CInt
     {- ^ __from C:__ @argc@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @argv@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @overview@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Support_7856a581439a1800" searchForAddressOfSymbol
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @symbolName@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Support_8c981b9374777106" addSymbol
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @symbolName@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @symbolValue@ -}
  -> IO ()
