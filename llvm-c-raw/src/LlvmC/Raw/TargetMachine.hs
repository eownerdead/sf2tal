{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.TargetMachine where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified LlvmC.Raw.Target
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/TargetMachine.h>\nLLVMTargetRef hs_bindgen_LlvmC_Raw_TargetMachine_2987e29ee3b0514d (void) { return LLVMGetFirstTarget(); }\nLLVMTargetRef hs_bindgen_LlvmC_Raw_TargetMachine_4b5d30fa0c67aaca (LLVMTargetRef arg1) { return LLVMGetNextTarget(arg1); }\nLLVMTargetRef hs_bindgen_LlvmC_Raw_TargetMachine_c7e8240c2bdd6685 (char *arg1) { return LLVMGetTargetFromName(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_e7cc4ea33280d26a (char *arg1, LLVMTargetRef *arg2, char **arg3) { return LLVMGetTargetFromTriple(arg1, arg2, arg3); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_7256c68f2d7db6b8 (LLVMTargetRef arg1) { return LLVMGetTargetName(arg1); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_a1e9255b2e7e5387 (LLVMTargetRef arg1) { return LLVMGetTargetDescription(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_fdddc58b13a7d9ca (LLVMTargetRef arg1) { return LLVMTargetHasJIT(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_9c6cc35e9332a548 (LLVMTargetRef arg1) { return LLVMTargetHasTargetMachine(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_8298901932bae3ce (LLVMTargetRef arg1) { return LLVMTargetHasAsmBackend(arg1); }\nLLVMTargetMachineOptionsRef hs_bindgen_LlvmC_Raw_TargetMachine_14f9032ba70e7781 (void) { return LLVMCreateTargetMachineOptions(); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_bc9491aecc5c8dce (LLVMTargetMachineOptionsRef arg1) { LLVMDisposeTargetMachineOptions(arg1); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_9b8a005f1a3de7a7 (LLVMTargetMachineOptionsRef arg1, char *arg2) { LLVMTargetMachineOptionsSetCPU(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_25c3cfead1a02115 (LLVMTargetMachineOptionsRef arg1, char *arg2) { LLVMTargetMachineOptionsSetFeatures(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_45d17ac27a178b6d (LLVMTargetMachineOptionsRef arg1, char *arg2) { LLVMTargetMachineOptionsSetABI(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_7cb8c01bb52d268f (LLVMTargetMachineOptionsRef arg1, LLVMCodeGenOptLevel arg2) { LLVMTargetMachineOptionsSetCodeGenOptLevel(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_fb3f096522317381 (LLVMTargetMachineOptionsRef arg1, LLVMRelocMode arg2) { LLVMTargetMachineOptionsSetRelocMode(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_c87bfbd1d12fe684 (LLVMTargetMachineOptionsRef arg1, LLVMCodeModel arg2) { LLVMTargetMachineOptionsSetCodeModel(arg1, arg2); }\nLLVMTargetMachineRef hs_bindgen_LlvmC_Raw_TargetMachine_7d00a59d837bfc84 (LLVMTargetRef arg1, char *arg2, LLVMTargetMachineOptionsRef arg3) { return LLVMCreateTargetMachineWithOptions(arg1, arg2, arg3); }\nLLVMTargetMachineRef hs_bindgen_LlvmC_Raw_TargetMachine_fc404a4fb3ad1e7f (LLVMTargetRef arg1, char *arg2, char *arg3, char *arg4, LLVMCodeGenOptLevel arg5, LLVMRelocMode arg6, LLVMCodeModel arg7) { return LLVMCreateTargetMachine(arg1, arg2, arg3, arg4, arg5, arg6, arg7); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_eefd18d28aa18289 (LLVMTargetMachineRef arg1) { LLVMDisposeTargetMachine(arg1); }\nLLVMTargetRef hs_bindgen_LlvmC_Raw_TargetMachine_464ff95c56e348ff (LLVMTargetMachineRef arg1) { return LLVMGetTargetMachineTarget(arg1); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_331f65357e56598a (LLVMTargetMachineRef arg1) { return LLVMGetTargetMachineTriple(arg1); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_ec7d115f9a80300a (LLVMTargetMachineRef arg1) { return LLVMGetTargetMachineCPU(arg1); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_c9fabdf9583f3a3a (LLVMTargetMachineRef arg1) { return LLVMGetTargetMachineFeatureString(arg1); }\nLLVMTargetDataRef hs_bindgen_LlvmC_Raw_TargetMachine_aa7a694cdd6c9554 (LLVMTargetMachineRef arg1) { return LLVMCreateTargetDataLayout(arg1); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_92436a105e1f9095 (LLVMTargetMachineRef arg1, LLVMBool arg2) { LLVMSetTargetMachineAsmVerbosity(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_c993eb6890beeca9 (LLVMTargetMachineRef arg1, LLVMBool arg2) { LLVMSetTargetMachineFastISel(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_06e4f7f1ea4cff68 (LLVMTargetMachineRef arg1, LLVMBool arg2) { LLVMSetTargetMachineGlobalISel(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_89c627072718bc01 (LLVMTargetMachineRef arg1, LLVMGlobalISelAbortMode arg2) { LLVMSetTargetMachineGlobalISelAbort(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_564805713943f1c2 (LLVMTargetMachineRef arg1, LLVMBool arg2) { LLVMSetTargetMachineMachineOutliner(arg1, arg2); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_8cc214562d0d64e6 (LLVMTargetMachineRef arg1, LLVMModuleRef arg2, char *arg3, LLVMCodeGenFileType arg4, char **arg5) { return LLVMTargetMachineEmitToFile(arg1, arg2, arg3, arg4, arg5); }\nLLVMBool hs_bindgen_LlvmC_Raw_TargetMachine_ecf6e1c2f610d624 (LLVMTargetMachineRef arg1, LLVMModuleRef arg2, LLVMCodeGenFileType arg3, char **arg4, LLVMMemoryBufferRef *arg5) { return LLVMTargetMachineEmitToMemoryBuffer(arg1, arg2, arg3, arg4, arg5); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_2800b63effac0b0a (void) { return LLVMGetDefaultTargetTriple(); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_e8dc12cbeab16d69 (char *arg1) { return LLVMNormalizeTargetTriple(arg1); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_804a0e28f24e7f37 (void) { return LLVMGetHostCPUName(); }\nchar *hs_bindgen_LlvmC_Raw_TargetMachine_2f9a2f3308ecdaa0 (void) { return LLVMGetHostCPUFeatures(); }\nvoid hs_bindgen_LlvmC_Raw_TargetMachine_ba91f030d976f6ca (LLVMTargetMachineRef arg1, LLVMPassManagerRef arg2) { LLVMAddAnalysisPasses(arg1, arg2); }\n")

data OpaqueTargetMachineOptions

newtype TargetMachineOptionsRef = TargetMachineOptionsRef
  { un_TargetMachineOptionsRef :: F.Ptr OpaqueTargetMachineOptions
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueTargetMachine

newtype TargetMachineRef = TargetMachineRef
  { un_TargetMachineRef :: F.Ptr OpaqueTargetMachine
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data Target

newtype TargetRef = TargetRef
  { un_TargetRef :: F.Ptr Target
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype CodeGenOptLevel = CodeGenOptLevel
  { un_CodeGenOptLevel :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable CodeGenOptLevel where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure CodeGenOptLevel
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          CodeGenOptLevel un_CodeGenOptLevel2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_CodeGenOptLevel2

instance HsBindgen.Runtime.CEnum.CEnum CodeGenOptLevel where

  type CEnumZ CodeGenOptLevel = FC.CUInt

  toCEnum = CodeGenOptLevel

  fromCEnum = un_CodeGenOptLevel

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "CodeGenLevelNone")
                                                     , (1, Data.List.NonEmpty.singleton "CodeGenLevelLess")
                                                     , (2, Data.List.NonEmpty.singleton "CodeGenLevelDefault")
                                                     , (3, Data.List.NonEmpty.singleton "CodeGenLevelAggressive")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "CodeGenOptLevel"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "CodeGenOptLevel"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum CodeGenOptLevel where

  minDeclaredValue = CodeGenLevelNone

  maxDeclaredValue = CodeGenLevelAggressive

instance Show CodeGenOptLevel where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read CodeGenOptLevel where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern CodeGenLevelNone :: CodeGenOptLevel
pattern CodeGenLevelNone = CodeGenOptLevel 0

pattern CodeGenLevelLess :: CodeGenOptLevel
pattern CodeGenLevelLess = CodeGenOptLevel 1

pattern CodeGenLevelDefault :: CodeGenOptLevel
pattern CodeGenLevelDefault = CodeGenOptLevel 2

pattern CodeGenLevelAggressive :: CodeGenOptLevel
pattern CodeGenLevelAggressive = CodeGenOptLevel 3

newtype RelocMode = RelocMode
  { un_RelocMode :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable RelocMode where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure RelocMode
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          RelocMode un_RelocMode2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_RelocMode2

instance HsBindgen.Runtime.CEnum.CEnum RelocMode where

  type CEnumZ RelocMode = FC.CUInt

  toCEnum = RelocMode

  fromCEnum = un_RelocMode

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "RelocDefault")
                                                     , (1, Data.List.NonEmpty.singleton "RelocStatic")
                                                     , (2, Data.List.NonEmpty.singleton "RelocPIC")
                                                     , (3, Data.List.NonEmpty.singleton "RelocDynamicNoPic")
                                                     , (4, Data.List.NonEmpty.singleton "RelocROPI")
                                                     , (5, Data.List.NonEmpty.singleton "RelocRWPI")
                                                     , (6, Data.List.NonEmpty.singleton "RelocROPI_RWPI")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "RelocMode"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "RelocMode"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum RelocMode where

  minDeclaredValue = RelocDefault

  maxDeclaredValue = RelocROPI_RWPI

instance Show RelocMode where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read RelocMode where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern RelocDefault :: RelocMode
pattern RelocDefault = RelocMode 0

pattern RelocStatic :: RelocMode
pattern RelocStatic = RelocMode 1

pattern RelocPIC :: RelocMode
pattern RelocPIC = RelocMode 2

pattern RelocDynamicNoPic :: RelocMode
pattern RelocDynamicNoPic = RelocMode 3

pattern RelocROPI :: RelocMode
pattern RelocROPI = RelocMode 4

pattern RelocRWPI :: RelocMode
pattern RelocRWPI = RelocMode 5

pattern RelocROPI_RWPI :: RelocMode
pattern RelocROPI_RWPI = RelocMode 6

newtype CodeModel = CodeModel
  { un_CodeModel :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable CodeModel where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure CodeModel
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          CodeModel un_CodeModel2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_CodeModel2

instance HsBindgen.Runtime.CEnum.CEnum CodeModel where

  type CEnumZ CodeModel = FC.CUInt

  toCEnum = CodeModel

  fromCEnum = un_CodeModel

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "CodeModelDefault")
                                                     , (1, Data.List.NonEmpty.singleton "CodeModelJITDefault")
                                                     , (2, Data.List.NonEmpty.singleton "CodeModelTiny")
                                                     , (3, Data.List.NonEmpty.singleton "CodeModelSmall")
                                                     , (4, Data.List.NonEmpty.singleton "CodeModelKernel")
                                                     , (5, Data.List.NonEmpty.singleton "CodeModelMedium")
                                                     , (6, Data.List.NonEmpty.singleton "CodeModelLarge")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "CodeModel"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "CodeModel"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum CodeModel where

  minDeclaredValue = CodeModelDefault

  maxDeclaredValue = CodeModelLarge

instance Show CodeModel where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read CodeModel where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern CodeModelDefault :: CodeModel
pattern CodeModelDefault = CodeModel 0

pattern CodeModelJITDefault :: CodeModel
pattern CodeModelJITDefault = CodeModel 1

pattern CodeModelTiny :: CodeModel
pattern CodeModelTiny = CodeModel 2

pattern CodeModelSmall :: CodeModel
pattern CodeModelSmall = CodeModel 3

pattern CodeModelKernel :: CodeModel
pattern CodeModelKernel = CodeModel 4

pattern CodeModelMedium :: CodeModel
pattern CodeModelMedium = CodeModel 5

pattern CodeModelLarge :: CodeModel
pattern CodeModelLarge = CodeModel 6

newtype CodeGenFileType = CodeGenFileType
  { un_CodeGenFileType :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable CodeGenFileType where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure CodeGenFileType
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          CodeGenFileType un_CodeGenFileType2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_CodeGenFileType2

instance HsBindgen.Runtime.CEnum.CEnum CodeGenFileType where

  type CEnumZ CodeGenFileType = FC.CUInt

  toCEnum = CodeGenFileType

  fromCEnum = un_CodeGenFileType

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "AssemblyFile")
                                                     , (1, Data.List.NonEmpty.singleton "ObjectFile")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "CodeGenFileType"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "CodeGenFileType"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum CodeGenFileType where

  minDeclaredValue = AssemblyFile

  maxDeclaredValue = ObjectFile

instance Show CodeGenFileType where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read CodeGenFileType where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern AssemblyFile :: CodeGenFileType
pattern AssemblyFile = CodeGenFileType 0

pattern ObjectFile :: CodeGenFileType
pattern ObjectFile = CodeGenFileType 1

newtype GlobalISelAbortMode = GlobalISelAbortMode
  { un_GlobalISelAbortMode :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable GlobalISelAbortMode where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure GlobalISelAbortMode
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          GlobalISelAbortMode un_GlobalISelAbortMode2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_GlobalISelAbortMode2

instance HsBindgen.Runtime.CEnum.CEnum GlobalISelAbortMode where

  type CEnumZ GlobalISelAbortMode = FC.CUInt

  toCEnum = GlobalISelAbortMode

  fromCEnum = un_GlobalISelAbortMode

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "GlobalISelAbortEnable")
                                                     , (1, Data.List.NonEmpty.singleton "GlobalISelAbortDisable")
                                                     , (2, Data.List.NonEmpty.singleton "GlobalISelAbortDisableWithDiag")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "GlobalISelAbortMode"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "GlobalISelAbortMode"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum GlobalISelAbortMode where

  minDeclaredValue = GlobalISelAbortEnable

  maxDeclaredValue = GlobalISelAbortDisableWithDiag

instance Show GlobalISelAbortMode where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read GlobalISelAbortMode where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern GlobalISelAbortEnable :: GlobalISelAbortMode
pattern GlobalISelAbortEnable = GlobalISelAbortMode 0

pattern GlobalISelAbortDisable :: GlobalISelAbortMode
pattern GlobalISelAbortDisable = GlobalISelAbortMode 1

pattern GlobalISelAbortDisableWithDiag :: GlobalISelAbortMode
pattern GlobalISelAbortDisableWithDiag = GlobalISelAbortMode 2

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_2987e29ee3b0514d" getFirstTarget
  :: IO TargetRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_4b5d30fa0c67aaca" getNextTarget
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO TargetRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_c7e8240c2bdd6685" getTargetFromName
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO TargetRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_e7cc4ea33280d26a" getTargetFromTriple
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> F.Ptr TargetRef
     {- ^ __from C:__ @t@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_7256c68f2d7db6b8" getTargetName
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_a1e9255b2e7e5387" getTargetDescription
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_fdddc58b13a7d9ca" targetHasJIT
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_9c6cc35e9332a548" targetHasTargetMachine
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_8298901932bae3ce" targetHasAsmBackend
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_14f9032ba70e7781" createTargetMachineOptions
  :: IO TargetMachineOptionsRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_bc9491aecc5c8dce" disposeTargetMachineOptions
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_9b8a005f1a3de7a7" targetMachineOptionsSetCPU
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cPU@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_25c3cfead1a02115" targetMachineOptionsSetFeatures
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @features@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_45d17ac27a178b6d" targetMachineOptionsSetABI
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @aBI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_7cb8c01bb52d268f" targetMachineOptionsSetCodeGenOptLevel
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> CodeGenOptLevel
     {- ^ __from C:__ @level@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_fb3f096522317381" targetMachineOptionsSetRelocMode
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> RelocMode
     {- ^ __from C:__ @reloc@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_c87bfbd1d12fe684" targetMachineOptionsSetCodeModel
  :: TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> CodeModel
     {- ^ __from C:__ @codeModel@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_7d00a59d837bfc84" createTargetMachineWithOptions
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> TargetMachineOptionsRef
     {- ^ __from C:__ @options@ -}
  -> IO TargetMachineRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_fc404a4fb3ad1e7f" createTargetMachine
  :: TargetRef
     {- ^ __from C:__ @t@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cPU@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @features@ -}
  -> CodeGenOptLevel
     {- ^ __from C:__ @level@ -}
  -> RelocMode
     {- ^ __from C:__ @reloc@ -}
  -> CodeModel
     {- ^ __from C:__ @codeModel@ -}
  -> IO TargetMachineRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_eefd18d28aa18289" disposeTargetMachine
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_464ff95c56e348ff" getTargetMachineTarget
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO TargetRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_331f65357e56598a" getTargetMachineTriple
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_ec7d115f9a80300a" getTargetMachineCPU
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_c9fabdf9583f3a3a" getTargetMachineFeatureString
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_aa7a694cdd6c9554" createTargetDataLayout
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> IO LlvmC.Raw.Target.TargetDataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_92436a105e1f9095" setTargetMachineAsmVerbosity
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @verboseAsm@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_c993eb6890beeca9" setTargetMachineFastISel
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @enable@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_06e4f7f1ea4cff68" setTargetMachineGlobalISel
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @enable@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_89c627072718bc01" setTargetMachineGlobalISelAbort
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> GlobalISelAbortMode
     {- ^ __from C:__ @mode@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_564805713943f1c2" setTargetMachineMachineOutliner
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.Bool
     {- ^ __from C:__ @enable@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_8cc214562d0d64e6" targetMachineEmitToFile
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @filename@ -}
  -> CodeGenFileType
     {- ^ __from C:__ @codegen@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_ecf6e1c2f610d624" targetMachineEmitToMemoryBuffer
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> CodeGenFileType
     {- ^ __from C:__ @codegen@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> F.Ptr LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @outMemBuf@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_2800b63effac0b0a" getDefaultTargetTriple
  :: IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_e8dc12cbeab16d69" normalizeTargetTriple
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_804a0e28f24e7f37" getHostCPUName
  :: IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_2f9a2f3308ecdaa0" getHostCPUFeatures
  :: IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_TargetMachine_ba91f030d976f6ca" addAnalysisPasses
  :: TargetMachineRef
     {- ^ __from C:__ @t@ -}
  -> LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @pM@ -}
  -> IO ()
