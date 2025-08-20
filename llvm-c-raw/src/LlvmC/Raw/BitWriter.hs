{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.BitWriter where

import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Types
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/BitWriter.h>\nsigned int hs_bindgen_LlvmC_Raw_BitWriter_5875678484aa46c0 (LLVMModuleRef arg1, char *arg2) { return LLVMWriteBitcodeToFile(arg1, arg2); }\nsigned int hs_bindgen_LlvmC_Raw_BitWriter_7c364f14464ee3c1 (LLVMModuleRef arg1, signed int arg2, signed int arg3, signed int arg4) { return LLVMWriteBitcodeToFD(arg1, arg2, arg3, arg4); }\nsigned int hs_bindgen_LlvmC_Raw_BitWriter_598dc096d0bbca20 (LLVMModuleRef arg1, signed int arg2) { return LLVMWriteBitcodeToFileHandle(arg1, arg2); }\nLLVMMemoryBufferRef hs_bindgen_LlvmC_Raw_BitWriter_104919076b629ac0 (LLVMModuleRef arg1) { return LLVMWriteBitcodeToMemoryBuffer(arg1); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitWriter_5875678484aa46c0" writeBitcodeToFile
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitWriter_7c364f14464ee3c1" writeBitcodeToFD
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> FC.CInt
     {- ^ __from C:__ @fD@ -}
  -> FC.CInt
     {- ^ __from C:__ @shouldClose@ -}
  -> FC.CInt
     {- ^ __from C:__ @unbuffered@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitWriter_598dc096d0bbca20" writeBitcodeToFileHandle
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> FC.CInt
     {- ^ __from C:__ @handle@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitWriter_104919076b629ac0" writeBitcodeToMemoryBuffer
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO LlvmC.Raw.Types.MemoryBufferRef
