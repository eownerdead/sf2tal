{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.ExecutionEngine where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Target
import qualified LlvmC.Raw.TargetMachine
import qualified LlvmC.Raw.Types
import Prelude ((<*>), (>>), Eq, IO, Int, Ord, Show, pure)

$(CAPI.addCSource "#define const\n#include <llvm-c/ExecutionEngine.h>\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_ed1e8e4c1a438456 (void) { LLVMLinkInMCJIT(); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_fec056c4bc09a8e8 (void) { LLVMLinkInInterpreter(); }\nLLVMGenericValueRef hs_bindgen_LlvmC_Raw_ExecutionEngine_b40bd5e5560e6274 (LLVMTypeRef arg1, unsigned long long arg2, LLVMBool arg3) { return LLVMCreateGenericValueOfInt(arg1, arg2, arg3); }\nLLVMGenericValueRef hs_bindgen_LlvmC_Raw_ExecutionEngine_70bba2d45775addb (void *arg1) { return LLVMCreateGenericValueOfPointer(arg1); }\nLLVMGenericValueRef hs_bindgen_LlvmC_Raw_ExecutionEngine_af0dd8d1a356eeb8 (LLVMTypeRef arg1, double arg2) { return LLVMCreateGenericValueOfFloat(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_ExecutionEngine_770b1328ce6443d1 (LLVMGenericValueRef arg1) { return LLVMGenericValueIntWidth(arg1); }\nunsigned long long hs_bindgen_LlvmC_Raw_ExecutionEngine_cd6255970d76d8cf (LLVMGenericValueRef arg1, LLVMBool arg2) { return LLVMGenericValueToInt(arg1, arg2); }\nvoid *hs_bindgen_LlvmC_Raw_ExecutionEngine_5f34d4baf4afbc84 (LLVMGenericValueRef arg1) { return LLVMGenericValueToPointer(arg1); }\ndouble hs_bindgen_LlvmC_Raw_ExecutionEngine_12172240654b204b (LLVMTypeRef arg1, LLVMGenericValueRef arg2) { return LLVMGenericValueToFloat(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_b3ac441572ef04d4 (LLVMGenericValueRef arg1) { LLVMDisposeGenericValue(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_eef5434871d564e6 (LLVMExecutionEngineRef *arg1, LLVMModuleRef arg2, char **arg3) { return LLVMCreateExecutionEngineForModule(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_a305e88f7b06efb8 (LLVMExecutionEngineRef *arg1, LLVMModuleRef arg2, char **arg3) { return LLVMCreateInterpreterForModule(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_98eb039ee1a59622 (LLVMExecutionEngineRef *arg1, LLVMModuleRef arg2, unsigned int arg3, char **arg4) { return LLVMCreateJITCompilerForModule(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_75db5f379acae923 (struct LLVMMCJITCompilerOptions *arg1, size_t arg2) { LLVMInitializeMCJITCompilerOptions(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_494f7db97eea6f1d (LLVMExecutionEngineRef *arg1, LLVMModuleRef arg2, struct LLVMMCJITCompilerOptions *arg3, size_t arg4, char **arg5) { return LLVMCreateMCJITCompilerForModule(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_7ec067ecb8195d25 (LLVMExecutionEngineRef arg1) { LLVMDisposeExecutionEngine(arg1); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_e76b9102a474641e (LLVMExecutionEngineRef arg1) { LLVMRunStaticConstructors(arg1); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_2f763a6998cf45d7 (LLVMExecutionEngineRef arg1) { LLVMRunStaticDestructors(arg1); }\nsigned int hs_bindgen_LlvmC_Raw_ExecutionEngine_6c643fe8189cfb96 (LLVMExecutionEngineRef arg1, LLVMValueRef arg2, unsigned int arg3, char **arg4, char **arg5) { return LLVMRunFunctionAsMain(arg1, arg2, arg3, arg4, arg5); }\nLLVMGenericValueRef hs_bindgen_LlvmC_Raw_ExecutionEngine_d012fef1c8c59a99 (LLVMExecutionEngineRef arg1, LLVMValueRef arg2, unsigned int arg3, LLVMGenericValueRef *arg4) { return LLVMRunFunction(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_c3aa0243f93d20a7 (LLVMExecutionEngineRef arg1, LLVMValueRef arg2) { LLVMFreeMachineCodeForFunction(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_3571143e9118a354 (LLVMExecutionEngineRef arg1, LLVMModuleRef arg2) { LLVMAddModule(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_eb00df27882bb109 (LLVMExecutionEngineRef arg1, LLVMModuleRef arg2, LLVMModuleRef *arg3, char **arg4) { return LLVMRemoveModule(arg1, arg2, arg3, arg4); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_0d852b92dc299536 (LLVMExecutionEngineRef arg1, char *arg2, LLVMValueRef *arg3) { return LLVMFindFunction(arg1, arg2, arg3); }\nvoid *hs_bindgen_LlvmC_Raw_ExecutionEngine_77fb648857ed091b (LLVMExecutionEngineRef arg1, LLVMValueRef arg2) { return LLVMRecompileAndRelinkFunction(arg1, arg2); }\nLLVMTargetDataRef hs_bindgen_LlvmC_Raw_ExecutionEngine_94f6be3a68b1fb50 (LLVMExecutionEngineRef arg1) { return LLVMGetExecutionEngineTargetData(arg1); }\nLLVMTargetMachineRef hs_bindgen_LlvmC_Raw_ExecutionEngine_7a3da5aded3c55a9 (LLVMExecutionEngineRef arg1) { return LLVMGetExecutionEngineTargetMachine(arg1); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_d4347e0e174385bb (LLVMExecutionEngineRef arg1, LLVMValueRef arg2, void *arg3) { LLVMAddGlobalMapping(arg1, arg2, arg3); }\nvoid *hs_bindgen_LlvmC_Raw_ExecutionEngine_a332cac76c1be9aa (LLVMExecutionEngineRef arg1, LLVMValueRef arg2) { return LLVMGetPointerToGlobal(arg1, arg2); }\nuint64_t hs_bindgen_LlvmC_Raw_ExecutionEngine_a1b8b101586dc0af (LLVMExecutionEngineRef arg1, char *arg2) { return LLVMGetGlobalValueAddress(arg1, arg2); }\nuint64_t hs_bindgen_LlvmC_Raw_ExecutionEngine_9a5065f4ad017edb (LLVMExecutionEngineRef arg1, char *arg2) { return LLVMGetFunctionAddress(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_ExecutionEngine_50f1e37cf56d4438 (LLVMExecutionEngineRef arg1, char **arg2) { return LLVMExecutionEngineGetErrMsg(arg1, arg2); }\nLLVMMCJITMemoryManagerRef hs_bindgen_LlvmC_Raw_ExecutionEngine_885234d04599076b (void *arg1, LLVMMemoryManagerAllocateCodeSectionCallback arg2, LLVMMemoryManagerAllocateDataSectionCallback arg3, LLVMMemoryManagerFinalizeMemoryCallback arg4, LLVMMemoryManagerDestroyCallback arg5) { return LLVMCreateSimpleMCJITMemoryManager(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_ExecutionEngine_bc27bcca01a59477 (LLVMMCJITMemoryManagerRef arg1) { LLVMDisposeMCJITMemoryManager(arg1); }\nLLVMJITEventListenerRef hs_bindgen_LlvmC_Raw_ExecutionEngine_3fedb72a6358a17f (void) { return LLVMCreateGDBRegistrationListener(); }\nLLVMJITEventListenerRef hs_bindgen_LlvmC_Raw_ExecutionEngine_2a805c8402d309b6 (void) { return LLVMCreateIntelJITEventListener(); }\nLLVMJITEventListenerRef hs_bindgen_LlvmC_Raw_ExecutionEngine_2b0eed7b71c1f45a (void) { return LLVMCreateOProfileJITEventListener(); }\nLLVMJITEventListenerRef hs_bindgen_LlvmC_Raw_ExecutionEngine_8c506b4d454e5cd6 (void) { return LLVMCreatePerfJITEventListener(); }\n")

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_ed1e8e4c1a438456" linkInMCJIT
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_fec056c4bc09a8e8" linkInInterpreter
  :: IO ()

data OpaqueGenericValue

newtype GenericValueRef = GenericValueRef
  { un_GenericValueRef :: F.Ptr OpaqueGenericValue
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueExecutionEngine

newtype ExecutionEngineRef = ExecutionEngineRef
  { un_ExecutionEngineRef :: F.Ptr OpaqueExecutionEngine
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueMCJITMemoryManager

newtype MCJITMemoryManagerRef = MCJITMemoryManagerRef
  { un_MCJITMemoryManagerRef :: F.Ptr OpaqueMCJITMemoryManager
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data MCJITCompilerOptions = MCJITCompilerOptions
  { mCJITCompilerOptions_OptLevel :: FC.CUInt
  , mCJITCompilerOptions_CodeModel :: LlvmC.Raw.TargetMachine.CodeModel
  , mCJITCompilerOptions_NoFramePointerElim :: LlvmC.Raw.Types.Bool
  , mCJITCompilerOptions_EnableFastISel :: LlvmC.Raw.Types.Bool
  , mCJITCompilerOptions_MCJMM :: MCJITMemoryManagerRef
  }
  deriving stock (Eq, Show)

instance F.Storable MCJITCompilerOptions where

  sizeOf = \_ -> (24 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure MCJITCompilerOptions
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (4 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)
      <*> F.peekByteOff ptr0 (12 :: Int)
      <*> F.peekByteOff ptr0 (16 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          MCJITCompilerOptions
            mCJITCompilerOptions_OptLevel2
            mCJITCompilerOptions_CodeModel3
            mCJITCompilerOptions_NoFramePointerElim4
            mCJITCompilerOptions_EnableFastISel5
            mCJITCompilerOptions_MCJMM6 ->
                 F.pokeByteOff ptr0 (0 :: Int) mCJITCompilerOptions_OptLevel2
              >> F.pokeByteOff ptr0 (4 :: Int) mCJITCompilerOptions_CodeModel3
              >> F.pokeByteOff ptr0 (8 :: Int) mCJITCompilerOptions_NoFramePointerElim4
              >> F.pokeByteOff ptr0 (12 :: Int) mCJITCompilerOptions_EnableFastISel5
              >> F.pokeByteOff ptr0 (16 :: Int) mCJITCompilerOptions_MCJMM6

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_b40bd5e5560e6274" createGenericValueOfInt
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> FC.CULLong
     {- ^ __from C:__ @n@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isSigned@ -}
  -> IO GenericValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_70bba2d45775addb" createGenericValueOfPointer
  :: F.Ptr Void
     {- ^ __from C:__ @p@ -}
  -> IO GenericValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_af0dd8d1a356eeb8" createGenericValueOfFloat
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> FC.CDouble
     {- ^ __from C:__ @n@ -}
  -> IO GenericValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_770b1328ce6443d1" genericValueIntWidth
  :: GenericValueRef
     {- ^ __from C:__ @genValRef@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_cd6255970d76d8cf" genericValueToInt
  :: GenericValueRef
     {- ^ __from C:__ @genVal@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @isSigned@ -}
  -> IO FC.CULLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_5f34d4baf4afbc84" genericValueToPointer
  :: GenericValueRef
     {- ^ __from C:__ @genVal@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_12172240654b204b" genericValueToFloat
  :: LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @tyRef@ -}
  -> GenericValueRef
     {- ^ __from C:__ @genVal@ -}
  -> IO FC.CDouble

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_b3ac441572ef04d4" disposeGenericValue
  :: GenericValueRef
     {- ^ __from C:__ @genVal@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_eef5434871d564e6" createExecutionEngineForModule
  :: F.Ptr ExecutionEngineRef
     {- ^ __from C:__ @outEE@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_a305e88f7b06efb8" createInterpreterForModule
  :: F.Ptr ExecutionEngineRef
     {- ^ __from C:__ @outInterp@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_98eb039ee1a59622" createJITCompilerForModule
  :: F.Ptr ExecutionEngineRef
     {- ^ __from C:__ @outJIT@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> FC.CUInt
     {- ^ __from C:__ @optLevel@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_75db5f379acae923" initializeMCJITCompilerOptions
  :: F.Ptr MCJITCompilerOptions
     {- ^ __from C:__ @options@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sizeOfOptions@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_494f7db97eea6f1d" createMCJITCompilerForModule
  :: F.Ptr ExecutionEngineRef
     {- ^ __from C:__ @outJIT@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr MCJITCompilerOptions
     {- ^ __from C:__ @options@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @sizeOfOptions@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_7ec067ecb8195d25" disposeExecutionEngine
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_e76b9102a474641e" runStaticConstructors
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_2f763a6998cf45d7" runStaticDestructors
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_6c643fe8189cfb96" runFunctionAsMain
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> FC.CUInt
     {- ^ __from C:__ @argC@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @argV@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @envP@ -}
  -> IO FC.CInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_d012fef1c8c59a99" runFunction
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> FC.CUInt
     {- ^ __from C:__ @numArgs@ -}
  -> F.Ptr GenericValueRef
     {- ^ __from C:__ @args@ -}
  -> IO GenericValueRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_c3aa0243f93d20a7" freeMachineCodeForFunction
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @f@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_3571143e9118a354" addModule
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_eb00df27882bb109" removeModule
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @outMod@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_0d852b92dc299536" findFunction
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> F.Ptr LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @outFn@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_77fb648857ed091b" recompileAndRelinkFunction
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_94f6be3a68b1fb50" getExecutionEngineTargetData
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> IO LlvmC.Raw.Target.TargetDataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_7a3da5aded3c55a9" getExecutionEngineTargetMachine
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> IO LlvmC.Raw.TargetMachine.TargetMachineRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_d4347e0e174385bb" addGlobalMapping
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> F.Ptr Void
     {- ^ __from C:__ @addr@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_a332cac76c1be9aa" getPointerToGlobal
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @global@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_a1b8b101586dc0af" getGlobalValueAddress
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_9a5065f4ad017edb" getFunctionAddress
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_50f1e37cf56d4438" executionEngineGetErrMsg
  :: ExecutionEngineRef
     {- ^ __from C:__ @eE@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outError@ -}
  -> IO LlvmC.Raw.Types.Bool

newtype MemoryManagerAllocateCodeSectionCallback = MemoryManagerAllocateCodeSectionCallback
  { un_MemoryManagerAllocateCodeSectionCallback :: F.FunPtr ((F.Ptr Void) -> HsBindgen.Runtime.Prelude.CUIntPtr -> FC.CUInt -> FC.CUInt -> (F.Ptr FC.CChar) -> IO (F.Ptr HsBindgen.Runtime.Prelude.Word8))
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype MemoryManagerAllocateDataSectionCallback = MemoryManagerAllocateDataSectionCallback
  { un_MemoryManagerAllocateDataSectionCallback :: F.FunPtr ((F.Ptr Void) -> HsBindgen.Runtime.Prelude.CUIntPtr -> FC.CUInt -> FC.CUInt -> (F.Ptr FC.CChar) -> LlvmC.Raw.Types.Bool -> IO (F.Ptr HsBindgen.Runtime.Prelude.Word8))
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype MemoryManagerFinalizeMemoryCallback = MemoryManagerFinalizeMemoryCallback
  { un_MemoryManagerFinalizeMemoryCallback :: F.FunPtr ((F.Ptr Void) -> (F.Ptr (F.Ptr FC.CChar)) -> IO LlvmC.Raw.Types.Bool)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype MemoryManagerDestroyCallback = MemoryManagerDestroyCallback
  { un_MemoryManagerDestroyCallback :: F.FunPtr ((F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_885234d04599076b" createSimpleMCJITMemoryManager
  :: F.Ptr Void
     {- ^ __from C:__ @opaque@ -}
  -> MemoryManagerAllocateCodeSectionCallback
     {- ^ __from C:__ @allocateCodeSection@ -}
  -> MemoryManagerAllocateDataSectionCallback
     {- ^ __from C:__ @allocateDataSection@ -}
  -> MemoryManagerFinalizeMemoryCallback
     {- ^ __from C:__ @finalizeMemory@ -}
  -> MemoryManagerDestroyCallback
     {- ^ __from C:__ @destroy@ -}
  -> IO MCJITMemoryManagerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_bc27bcca01a59477" disposeMCJITMemoryManager
  :: MCJITMemoryManagerRef
     {- ^ __from C:__ @mM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_3fedb72a6358a17f" createGDBRegistrationListener
  :: IO LlvmC.Raw.Types.JITEventListenerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_2a805c8402d309b6" createIntelJITEventListener
  :: IO LlvmC.Raw.Types.JITEventListenerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_2b0eed7b71c1f45a" createOProfileJITEventListener
  :: IO LlvmC.Raw.Types.JITEventListenerRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_ExecutionEngine_8c506b4d454e5cd6" createPerfJITEventListener
  :: IO LlvmC.Raw.Types.JITEventListenerRef
