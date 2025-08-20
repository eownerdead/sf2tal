{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.Disassembler where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.DisassemblerTypes
import Prelude (IO)

$(CAPI.addCSource "#define const\n#include <llvm-c/Disassembler.h>\nLLVMDisasmContextRef hs_bindgen_LlvmC_Raw_Disassembler_57f73056e17e5bc4 (char *arg1, void *arg2, signed int arg3, LLVMOpInfoCallback arg4, LLVMSymbolLookupCallback arg5) { return LLVMCreateDisasm(arg1, arg2, arg3, arg4, arg5); }\nLLVMDisasmContextRef hs_bindgen_LlvmC_Raw_Disassembler_077d86394f4ebe53 (char *arg1, char *arg2, void *arg3, signed int arg4, LLVMOpInfoCallback arg5, LLVMSymbolLookupCallback arg6) { return LLVMCreateDisasmCPU(arg1, arg2, arg3, arg4, arg5, arg6); }\nLLVMDisasmContextRef hs_bindgen_LlvmC_Raw_Disassembler_ca0cc2c2e7232fdd (char *arg1, char *arg2, char *arg3, void *arg4, signed int arg5, LLVMOpInfoCallback arg6, LLVMSymbolLookupCallback arg7) { return LLVMCreateDisasmCPUFeatures(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nsigned int hs_bindgen_LlvmC_Raw_Disassembler_010c49566d461edb (LLVMDisasmContextRef arg1, uint64_t arg2) { return LLVMSetDisasmOptions(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Disassembler_bd87aec6eed36638 (LLVMDisasmContextRef arg1) { LLVMDisasmDispose(arg1); }\nsize_t hs_bindgen_LlvmC_Raw_Disassembler_5dd8c2daed9faa4b (LLVMDisasmContextRef arg1, uint8_t *arg2, uint64_t arg3, uint64_t arg4, char *arg5, size_t arg6) { return LLVMDisasmInstruction(arg1, arg2, arg3, arg4, arg5, arg6); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_57f73056e17e5bc4" createDisasm
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @tripleName@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @disInfo@ -}
  -> FC.CInt
     {- ^ __from C:__ @tagType@ -}
  -> LlvmC.Raw.DisassemblerTypes.OpInfoCallback
     {- ^ __from C:__ @getOpInfo@ -}
  -> LlvmC.Raw.DisassemblerTypes.SymbolLookupCallback
     {- ^ __from C:__ @symbolLookUp@ -}
  -> IO LlvmC.Raw.DisassemblerTypes.DisasmContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_077d86394f4ebe53" createDisasmCPU
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cPU@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @disInfo@ -}
  -> FC.CInt
     {- ^ __from C:__ @tagType@ -}
  -> LlvmC.Raw.DisassemblerTypes.OpInfoCallback
     {- ^ __from C:__ @getOpInfo@ -}
  -> LlvmC.Raw.DisassemblerTypes.SymbolLookupCallback
     {- ^ __from C:__ @symbolLookUp@ -}
  -> IO LlvmC.Raw.DisassemblerTypes.DisasmContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_ca0cc2c2e7232fdd" createDisasmCPUFeatures
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cPU@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @features@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @disInfo@ -}
  -> FC.CInt
     {- ^ __from C:__ @tagType@ -}
  -> LlvmC.Raw.DisassemblerTypes.OpInfoCallback
     {- ^ __from C:__ @getOpInfo@ -}
  -> LlvmC.Raw.DisassemblerTypes.SymbolLookupCallback
     {- ^ __from C:__ @symbolLookUp@ -}
  -> IO LlvmC.Raw.DisassemblerTypes.DisasmContextRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_010c49566d461edb" setDisasmOptions
  :: LlvmC.Raw.DisassemblerTypes.DisasmContextRef
     {- ^ __from C:__ @dC@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @options@ -}
  -> IO FC.CInt

disassembler_Option_UseMarkup :: FC.CInt
disassembler_Option_UseMarkup = (1 :: FC.CInt)

disassembler_Option_PrintImmHex :: FC.CInt
disassembler_Option_PrintImmHex = (2 :: FC.CInt)

disassembler_Option_AsmPrinterVariant :: FC.CInt
disassembler_Option_AsmPrinterVariant =
  (4 :: FC.CInt)

disassembler_Option_SetInstrComments :: FC.CInt
disassembler_Option_SetInstrComments = (8 :: FC.CInt)

disassembler_Option_PrintLatency :: FC.CInt
disassembler_Option_PrintLatency = (16 :: FC.CInt)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_bd87aec6eed36638" disasmDispose
  :: LlvmC.Raw.DisassemblerTypes.DisasmContextRef
     {- ^ __from C:__ @dC@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Disassembler_5dd8c2daed9faa4b" disasmInstruction
  :: LlvmC.Raw.DisassemblerTypes.DisasmContextRef
     {- ^ __from C:__ @dC@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.Word8
     {- ^ __from C:__ @bytes@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @bytesSize@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @pC@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @outString@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @outStringSize@ -}
  -> IO HsBindgen.Runtime.Prelude.CSize
