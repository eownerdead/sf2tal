{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.BitReader where

import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified LlvmC.Raw.Types
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/BitReader.h>\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_9646cb802f60a889 (LLVMMemoryBufferRef arg1, LLVMModuleRef *arg2, char **arg3) { return LLVMParseBitcode(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_a20318aab129e284 (LLVMMemoryBufferRef arg1, LLVMModuleRef *arg2) { return LLVMParseBitcode2(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_da0428b33348465f (LLVMContextRef arg1, LLVMMemoryBufferRef arg2, LLVMModuleRef *arg3, char **arg4) { return LLVMParseBitcodeInContext(arg1, arg2, arg3, arg4); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_d4a7b31b108533c8 (LLVMContextRef arg1, LLVMMemoryBufferRef arg2, LLVMModuleRef *arg3) { return LLVMParseBitcodeInContext2(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_e8e9ca09be19f177 (LLVMContextRef arg1, LLVMMemoryBufferRef arg2, LLVMModuleRef *arg3, char **arg4) { return LLVMGetBitcodeModuleInContext(arg1, arg2, arg3, arg4); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_20dea00c6e432666 (LLVMContextRef arg1, LLVMMemoryBufferRef arg2, LLVMModuleRef *arg3) { return LLVMGetBitcodeModuleInContext2(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_06f0761fc51c1a5d (LLVMMemoryBufferRef arg1, LLVMModuleRef *arg2, char **arg3) { return LLVMGetBitcodeModule(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_BitReader_d775506fa96c6817 (LLVMMemoryBufferRef arg1, LLVMModuleRef *arg2) { return LLVMGetBitcodeModule2(arg1, arg2); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_9646cb802f60a889" parseBitcode
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outModule@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_a20318aab129e284" parseBitcode2
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outModule@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_da0428b33348465f" parseBitcodeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @contextRef@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outModule@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_d4a7b31b108533c8" parseBitcodeInContext2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @contextRef@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outModule@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_e8e9ca09be19f177" getBitcodeModuleInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @contextRef@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outM@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_20dea00c6e432666" getBitcodeModuleInContext2
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @contextRef@ -}
  -> LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outM@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_06f0761fc51c1a5d" getBitcodeModule
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outM@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_BitReader_d775506fa96c6817" getBitcodeModule2
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outM@ -}
  -> IO LlvmC.Raw.Types.Bool
