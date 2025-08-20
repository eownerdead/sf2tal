{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Remarks where

import qualified Data.List.NonEmpty
import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Remarks.h>\nchar *hs_bindgen_LlvmC_Raw_Remarks_28c9d7986e54e36c (LLVMRemarkStringRef arg1) { return LLVMRemarkStringGetData(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_Remarks_3ab20133bd1ea856 (LLVMRemarkStringRef arg1) { return LLVMRemarkStringGetLen(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_fb5506832f9c3682 (LLVMRemarkDebugLocRef arg1) { return LLVMRemarkDebugLocGetSourceFilePath(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_Remarks_e18009cf846b2348 (LLVMRemarkDebugLocRef arg1) { return LLVMRemarkDebugLocGetSourceLine(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_Remarks_572707b8078deecd (LLVMRemarkDebugLocRef arg1) { return LLVMRemarkDebugLocGetSourceColumn(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_2ada8399431008bb (LLVMRemarkArgRef arg1) { return LLVMRemarkArgGetKey(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_e47e1f66b3d113e5 (LLVMRemarkArgRef arg1) { return LLVMRemarkArgGetValue(arg1); }\nLLVMRemarkDebugLocRef hs_bindgen_LlvmC_Raw_Remarks_bcd5e9e60a0a14eb (LLVMRemarkArgRef arg1) { return LLVMRemarkArgGetDebugLoc(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Remarks_05812bbe1fc89ac2 (LLVMRemarkEntryRef arg1) { LLVMRemarkEntryDispose(arg1); }\nenum LLVMRemarkType hs_bindgen_LlvmC_Raw_Remarks_a2b97d2505a7c0b0 (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetType(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_4d51fbdd2957fd01 (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetPassName(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_01ed20db2f8d585c (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetRemarkName(arg1); }\nLLVMRemarkStringRef hs_bindgen_LlvmC_Raw_Remarks_1d98ed0c5f996874 (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetFunctionName(arg1); }\nLLVMRemarkDebugLocRef hs_bindgen_LlvmC_Raw_Remarks_f6f850fb7543cf4e (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetDebugLoc(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Remarks_16a3c9279387ba90 (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetHotness(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_Remarks_eed2b1a58c260137 (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetNumArgs(arg1); }\nLLVMRemarkArgRef hs_bindgen_LlvmC_Raw_Remarks_18a86929ede2e90d (LLVMRemarkEntryRef arg1) { return LLVMRemarkEntryGetFirstArg(arg1); }\nLLVMRemarkArgRef hs_bindgen_LlvmC_Raw_Remarks_faa11c00490cfeef (LLVMRemarkArgRef arg1, LLVMRemarkEntryRef arg2) { return LLVMRemarkEntryGetNextArg(arg1, arg2); }\nLLVMRemarkParserRef hs_bindgen_LlvmC_Raw_Remarks_6e10d75a7df30eb6 (void *arg1, uint64_t arg2) { return LLVMRemarkParserCreateYAML(arg1, arg2); }\nLLVMRemarkParserRef hs_bindgen_LlvmC_Raw_Remarks_df033d46da997f76 (void *arg1, uint64_t arg2) { return LLVMRemarkParserCreateBitstream(arg1, arg2); }\nLLVMRemarkEntryRef hs_bindgen_LlvmC_Raw_Remarks_06f64ef614a5ee1b (LLVMRemarkParserRef arg1) { return LLVMRemarkParserGetNext(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Remarks_824b08bb7558bdb9 (LLVMRemarkParserRef arg1) { return LLVMRemarkParserHasError(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Remarks_3e7a5251988690c0 (LLVMRemarkParserRef arg1) { return LLVMRemarkParserGetErrorMessage(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Remarks_dd502460b33db8d6 (LLVMRemarkParserRef arg1) { LLVMRemarkParserDispose(arg1); }\nuint32_t hs_bindgen_LlvmC_Raw_Remarks_d478f87a769d0193 (void) { return LLVMRemarkVersion(); }\n")

rEMARKS_API_VERSION :: FC.CInt
rEMARKS_API_VERSION = (1 :: FC.CInt)

newtype RemarkType = RemarkType
  { un_RemarkType :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable RemarkType where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure RemarkType
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          RemarkType un_RemarkType2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_RemarkType2

instance HsBindgen.Runtime.CEnum.CEnum RemarkType where

  type CEnumZ RemarkType = FC.CUInt

  toCEnum = RemarkType

  fromCEnum = un_RemarkType

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "RemarkTypeUnknown")
                                                     , (1, Data.List.NonEmpty.singleton "RemarkTypePassed")
                                                     , (2, Data.List.NonEmpty.singleton "RemarkTypeMissed")
                                                     , (3, Data.List.NonEmpty.singleton "RemarkTypeAnalysis")
                                                     , (4, Data.List.NonEmpty.singleton "RemarkTypeAnalysisFPCommute")
                                                     , (5, Data.List.NonEmpty.singleton "RemarkTypeAnalysisAliasing")
                                                     , (6, Data.List.NonEmpty.singleton "RemarkTypeFailure")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "RemarkType"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "RemarkType"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum RemarkType where

  minDeclaredValue = RemarkTypeUnknown

  maxDeclaredValue = RemarkTypeFailure

instance Show RemarkType where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read RemarkType where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern RemarkTypeUnknown :: RemarkType
pattern RemarkTypeUnknown = RemarkType 0

pattern RemarkTypePassed :: RemarkType
pattern RemarkTypePassed = RemarkType 1

pattern RemarkTypeMissed :: RemarkType
pattern RemarkTypeMissed = RemarkType 2

pattern RemarkTypeAnalysis :: RemarkType
pattern RemarkTypeAnalysis = RemarkType 3

pattern RemarkTypeAnalysisFPCommute :: RemarkType
pattern RemarkTypeAnalysisFPCommute = RemarkType 4

pattern RemarkTypeAnalysisAliasing :: RemarkType
pattern RemarkTypeAnalysisAliasing = RemarkType 5

pattern RemarkTypeFailure :: RemarkType
pattern RemarkTypeFailure = RemarkType 6

data RemarkOpaqueString

newtype RemarkStringRef = RemarkStringRef
  { un_RemarkStringRef :: F.Ptr RemarkOpaqueString
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_28c9d7986e54e36c" remarkStringGetData
  :: RemarkStringRef
     {- ^ __from C:__ @string@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_3ab20133bd1ea856" remarkStringGetLen
  :: RemarkStringRef
     {- ^ __from C:__ @string@ -}
  -> IO HsBindgen.Runtime.Prelude.Word32

data RemarkOpaqueDebugLoc

newtype RemarkDebugLocRef = RemarkDebugLocRef
  { un_RemarkDebugLocRef :: F.Ptr RemarkOpaqueDebugLoc
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_fb5506832f9c3682" remarkDebugLocGetSourceFilePath
  :: RemarkDebugLocRef
     {- ^ __from C:__ @dL@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_e18009cf846b2348" remarkDebugLocGetSourceLine
  :: RemarkDebugLocRef
     {- ^ __from C:__ @dL@ -}
  -> IO HsBindgen.Runtime.Prelude.Word32

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_572707b8078deecd" remarkDebugLocGetSourceColumn
  :: RemarkDebugLocRef
     {- ^ __from C:__ @dL@ -}
  -> IO HsBindgen.Runtime.Prelude.Word32

data RemarkOpaqueArg

newtype RemarkArgRef = RemarkArgRef
  { un_RemarkArgRef :: F.Ptr RemarkOpaqueArg
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_2ada8399431008bb" remarkArgGetKey
  :: RemarkArgRef
     {- ^ __from C:__ @arg@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_e47e1f66b3d113e5" remarkArgGetValue
  :: RemarkArgRef
     {- ^ __from C:__ @arg@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_bcd5e9e60a0a14eb" remarkArgGetDebugLoc
  :: RemarkArgRef
     {- ^ __from C:__ @arg@ -}
  -> IO RemarkDebugLocRef

data RemarkOpaqueEntry

newtype RemarkEntryRef = RemarkEntryRef
  { un_RemarkEntryRef :: F.Ptr RemarkOpaqueEntry
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_05812bbe1fc89ac2" remarkEntryDispose
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_a2b97d2505a7c0b0" remarkEntryGetType
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkType

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_4d51fbdd2957fd01" remarkEntryGetPassName
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_01ed20db2f8d585c" remarkEntryGetRemarkName
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_1d98ed0c5f996874" remarkEntryGetFunctionName
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkStringRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_f6f850fb7543cf4e" remarkEntryGetDebugLoc
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkDebugLocRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_16a3c9279387ba90" remarkEntryGetHotness
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_eed2b1a58c260137" remarkEntryGetNumArgs
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO HsBindgen.Runtime.Prelude.Word32

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_18a86929ede2e90d" remarkEntryGetFirstArg
  :: RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkArgRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_faa11c00490cfeef" remarkEntryGetNextArg
  :: RemarkArgRef
     {- ^ __from C:__ @it@ -}
  -> RemarkEntryRef
     {- ^ __from C:__ @remark@ -}
  -> IO RemarkArgRef

data RemarkOpaqueParser

newtype RemarkParserRef = RemarkParserRef
  { un_RemarkParserRef :: F.Ptr RemarkOpaqueParser
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_6e10d75a7df30eb6" remarkParserCreateYAML
  :: F.Ptr Void
     {- ^ __from C:__ @buf@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @size@ -}
  -> IO RemarkParserRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_df033d46da997f76" remarkParserCreateBitstream
  :: F.Ptr Void
     {- ^ __from C:__ @buf@ -}
  -> HsBindgen.Runtime.Prelude.Word64
     {- ^ __from C:__ @size@ -}
  -> IO RemarkParserRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_06f64ef614a5ee1b" remarkParserGetNext
  :: RemarkParserRef
     {- ^ __from C:__ @parser@ -}
  -> IO RemarkEntryRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_824b08bb7558bdb9" remarkParserHasError
  :: RemarkParserRef
     {- ^ __from C:__ @parser@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_3e7a5251988690c0" remarkParserGetErrorMessage
  :: RemarkParserRef
     {- ^ __from C:__ @parser@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_dd502460b33db8d6" remarkParserDispose
  :: RemarkParserRef
     {- ^ __from C:__ @parser@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Remarks_d478f87a769d0193" remarkVersion
  :: IO HsBindgen.Runtime.Prelude.Word32
