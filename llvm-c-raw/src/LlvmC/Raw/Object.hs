{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Object where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.Prelude
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Object.h>\nLLVMBinaryRef hs_bindgen_LlvmC_Raw_Object_6781d63dfd3d4ef6 (LLVMMemoryBufferRef arg1, LLVMContextRef arg2, char **arg3) { return LLVMCreateBinary(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Object_4f6decdb2ebe8344 (LLVMBinaryRef arg1) { LLVMDisposeBinary(arg1); }\nLLVMMemoryBufferRef hs_bindgen_LlvmC_Raw_Object_4e2c8350e34613ee (LLVMBinaryRef arg1) { return LLVMBinaryCopyMemoryBuffer(arg1); }\nLLVMBinaryType hs_bindgen_LlvmC_Raw_Object_f78e9210a015f044 (LLVMBinaryRef arg1) { return LLVMBinaryGetType(arg1); }\nLLVMBinaryRef hs_bindgen_LlvmC_Raw_Object_1e3cf8c6f604353b (LLVMBinaryRef arg1, char *arg2, size_t arg3, char **arg4) { return LLVMMachOUniversalBinaryCopyObjectForArch(arg1, arg2, arg3, arg4); }\nLLVMSectionIteratorRef hs_bindgen_LlvmC_Raw_Object_87220a37b9e84185 (LLVMBinaryRef arg1) { return LLVMObjectFileCopySectionIterator(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_fca5dfbc4b79d183 (LLVMBinaryRef arg1, LLVMSectionIteratorRef arg2) { return LLVMObjectFileIsSectionIteratorAtEnd(arg1, arg2); }\nLLVMSymbolIteratorRef hs_bindgen_LlvmC_Raw_Object_618cc1d1e2ecb7bc (LLVMBinaryRef arg1) { return LLVMObjectFileCopySymbolIterator(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_0ad33b23328d9513 (LLVMBinaryRef arg1, LLVMSymbolIteratorRef arg2) { return LLVMObjectFileIsSymbolIteratorAtEnd(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Object_b7de1a2d4e2bc9f6 (LLVMSectionIteratorRef arg1) { LLVMDisposeSectionIterator(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Object_79d393c7dddbec20 (LLVMSectionIteratorRef arg1) { LLVMMoveToNextSection(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Object_1fa257e04026cee6 (LLVMSectionIteratorRef arg1, LLVMSymbolIteratorRef arg2) { LLVMMoveToContainingSection(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Object_a8571d16ed080c30 (LLVMSymbolIteratorRef arg1) { LLVMDisposeSymbolIterator(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Object_c20ad1b6747df797 (LLVMSymbolIteratorRef arg1) { LLVMMoveToNextSymbol(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Object_1116fb4fe943c8b6 (LLVMSectionIteratorRef arg1) { return LLVMGetSectionName(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_1edd47b64bda06a7 (LLVMSectionIteratorRef arg1) { return LLVMGetSectionSize(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Object_d398a7d917d02b54 (LLVMSectionIteratorRef arg1) { return LLVMGetSectionContents(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_660604e79cb330a4 (LLVMSectionIteratorRef arg1) { return LLVMGetSectionAddress(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_3b03a91b569a4bf0 (LLVMSectionIteratorRef arg1, LLVMSymbolIteratorRef arg2) { return LLVMGetSectionContainsSymbol(arg1, arg2); }\nLLVMRelocationIteratorRef hs_bindgen_LlvmC_Raw_Object_ad0da2dcc0245218 (LLVMSectionIteratorRef arg1) { return LLVMGetRelocations(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Object_e32b910ae7584029 (LLVMRelocationIteratorRef arg1) { LLVMDisposeRelocationIterator(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_7541562b43b5e9a0 (LLVMSectionIteratorRef arg1, LLVMRelocationIteratorRef arg2) { return LLVMIsRelocationIteratorAtEnd(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Object_f0114389edd98f1f (LLVMRelocationIteratorRef arg1) { LLVMMoveToNextRelocation(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Object_a090402ae8777c0c (LLVMSymbolIteratorRef arg1) { return LLVMGetSymbolName(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_3299fed07a74fc8d (LLVMSymbolIteratorRef arg1) { return LLVMGetSymbolAddress(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_5434000ae14ca3d5 (LLVMSymbolIteratorRef arg1) { return LLVMGetSymbolSize(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_c7952e6df31a3639 (LLVMRelocationIteratorRef arg1) { return LLVMGetRelocationOffset(arg1); }\nLLVMSymbolIteratorRef hs_bindgen_LlvmC_Raw_Object_1aabff55a62183cb (LLVMRelocationIteratorRef arg1) { return LLVMGetRelocationSymbol(arg1); }\nuint64_t hs_bindgen_LlvmC_Raw_Object_9c818f2dfa8b4f52 (LLVMRelocationIteratorRef arg1) { return LLVMGetRelocationType(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Object_a881e7f3f1d5266d (LLVMRelocationIteratorRef arg1) { return LLVMGetRelocationTypeName(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Object_7b573863813771a3 (LLVMRelocationIteratorRef arg1) { return LLVMGetRelocationValueString(arg1); }\nLLVMObjectFileRef hs_bindgen_LlvmC_Raw_Object_3dc776ac6d169d47 (LLVMMemoryBufferRef arg1) { return LLVMCreateObjectFile(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Object_3ed23b5ddd9e9bd3 (LLVMObjectFileRef arg1) { LLVMDisposeObjectFile(arg1); }\nLLVMSectionIteratorRef hs_bindgen_LlvmC_Raw_Object_ebbb24fa505e89ce (LLVMObjectFileRef arg1) { return LLVMGetSections(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_c3cefb2f7400f85c (LLVMObjectFileRef arg1, LLVMSectionIteratorRef arg2) { return LLVMIsSectionIteratorAtEnd(arg1, arg2); }\nLLVMSymbolIteratorRef hs_bindgen_LlvmC_Raw_Object_ac423558da540a41 (LLVMObjectFileRef arg1) { return LLVMGetSymbols(arg1); }\nLLVMBool hs_bindgen_LlvmC_Raw_Object_1a7882c5e84b2a52 (LLVMObjectFileRef arg1, LLVMSymbolIteratorRef arg2) { return LLVMIsSymbolIteratorAtEnd(arg1, arg2); }\n")

data OpaqueSectionIterator

newtype SectionIteratorRef = SectionIteratorRef
  { un_SectionIteratorRef :: F.Ptr OpaqueSectionIterator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueSymbolIterator

newtype SymbolIteratorRef = SymbolIteratorRef
  { un_SymbolIteratorRef :: F.Ptr OpaqueSymbolIterator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueRelocationIterator

newtype RelocationIteratorRef = RelocationIteratorRef
  { un_RelocationIteratorRef :: F.Ptr OpaqueRelocationIterator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype BinaryType = BinaryType
  { un_BinaryType :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable BinaryType where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure BinaryType
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          BinaryType un_BinaryType2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_BinaryType2

instance HsBindgen.Runtime.CEnum.CEnum BinaryType where

  type CEnumZ BinaryType = FC.CUInt

  toCEnum = BinaryType

  fromCEnum = un_BinaryType

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "BinaryTypeArchive")
                                                     , (1, Data.List.NonEmpty.singleton "BinaryTypeMachOUniversalBinary")
                                                     , (2, Data.List.NonEmpty.singleton "BinaryTypeCOFFImportFile")
                                                     , (3, Data.List.NonEmpty.singleton "BinaryTypeIR")
                                                     , (4, Data.List.NonEmpty.singleton "BinaryTypeWinRes")
                                                     , (5, Data.List.NonEmpty.singleton "BinaryTypeCOFF")
                                                     , (6, Data.List.NonEmpty.singleton "BinaryTypeELF32L")
                                                     , (7, Data.List.NonEmpty.singleton "BinaryTypeELF32B")
                                                     , (8, Data.List.NonEmpty.singleton "BinaryTypeELF64L")
                                                     , (9, Data.List.NonEmpty.singleton "BinaryTypeELF64B")
                                                     , (10, Data.List.NonEmpty.singleton "BinaryTypeMachO32L")
                                                     , (11, Data.List.NonEmpty.singleton "BinaryTypeMachO32B")
                                                     , (12, Data.List.NonEmpty.singleton "BinaryTypeMachO64L")
                                                     , (13, Data.List.NonEmpty.singleton "BinaryTypeMachO64B")
                                                     , (14, Data.List.NonEmpty.singleton "BinaryTypeWasm")
                                                     , (15, Data.List.NonEmpty.singleton "BinaryTypeOffload")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "BinaryType"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "BinaryType"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum BinaryType where

  minDeclaredValue = BinaryTypeArchive

  maxDeclaredValue = BinaryTypeOffload

instance Show BinaryType where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read BinaryType where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern BinaryTypeArchive :: BinaryType
pattern BinaryTypeArchive = BinaryType 0

pattern BinaryTypeMachOUniversalBinary :: BinaryType
pattern BinaryTypeMachOUniversalBinary = BinaryType 1

pattern BinaryTypeCOFFImportFile :: BinaryType
pattern BinaryTypeCOFFImportFile = BinaryType 2

pattern BinaryTypeIR :: BinaryType
pattern BinaryTypeIR = BinaryType 3

pattern BinaryTypeWinRes :: BinaryType
pattern BinaryTypeWinRes = BinaryType 4

pattern BinaryTypeCOFF :: BinaryType
pattern BinaryTypeCOFF = BinaryType 5

pattern BinaryTypeELF32L :: BinaryType
pattern BinaryTypeELF32L = BinaryType 6

pattern BinaryTypeELF32B :: BinaryType
pattern BinaryTypeELF32B = BinaryType 7

pattern BinaryTypeELF64L :: BinaryType
pattern BinaryTypeELF64L = BinaryType 8

pattern BinaryTypeELF64B :: BinaryType
pattern BinaryTypeELF64B = BinaryType 9

pattern BinaryTypeMachO32L :: BinaryType
pattern BinaryTypeMachO32L = BinaryType 10

pattern BinaryTypeMachO32B :: BinaryType
pattern BinaryTypeMachO32B = BinaryType 11

pattern BinaryTypeMachO64L :: BinaryType
pattern BinaryTypeMachO64L = BinaryType 12

pattern BinaryTypeMachO64B :: BinaryType
pattern BinaryTypeMachO64B = BinaryType 13

pattern BinaryTypeWasm :: BinaryType
pattern BinaryTypeWasm = BinaryType 14

pattern BinaryTypeOffload :: BinaryType
pattern BinaryTypeOffload = BinaryType 15

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_6781d63dfd3d4ef6" createBinary
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @context@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> IO LlvmC.Raw.Types.BinaryRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_4f6decdb2ebe8344" disposeBinary
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_4e2c8350e34613ee" binaryCopyMemoryBuffer
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> IO LlvmC.Raw.Types.MemoryBufferRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_f78e9210a015f044" binaryGetType
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> IO BinaryType

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1e3cf8c6f604353b" machOUniversalBinaryCopyObjectForArch
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @arch@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @archLen@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @errorMessage@ -}
  -> IO LlvmC.Raw.Types.BinaryRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_87220a37b9e84185" objectFileCopySectionIterator
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> IO SectionIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_fca5dfbc4b79d183" objectFileIsSectionIteratorAtEnd
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_618cc1d1e2ecb7bc" objectFileCopySymbolIterator
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> IO SymbolIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_0ad33b23328d9513" objectFileIsSymbolIteratorAtEnd
  :: LlvmC.Raw.Types.BinaryRef
     {- ^ __from C:__ @bR@ -}
  -> SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_b7de1a2d4e2bc9f6" disposeSectionIterator
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_79d393c7dddbec20" moveToNextSection
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1fa257e04026cee6" moveToContainingSection
  :: SectionIteratorRef
     {- ^ __from C:__ @sect@ -}
  -> SymbolIteratorRef
     {- ^ __from C:__ @sym@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_a8571d16ed080c30" disposeSymbolIterator
  :: SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_c20ad1b6747df797" moveToNextSymbol
  :: SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1116fb4fe943c8b6" getSectionName
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1edd47b64bda06a7" getSectionSize
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_d398a7d917d02b54" getSectionContents
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_660604e79cb330a4" getSectionAddress
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_3b03a91b569a4bf0" getSectionContainsSymbol
  :: SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> SymbolIteratorRef
     {- ^ __from C:__ @sym@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_ad0da2dcc0245218" getRelocations
  :: SectionIteratorRef
     {- ^ __from C:__ @section@ -}
  -> IO RelocationIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_e32b910ae7584029" disposeRelocationIterator
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_7541562b43b5e9a0" isRelocationIteratorAtEnd
  :: SectionIteratorRef
     {- ^ __from C:__ @section@ -}
  -> RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_f0114389edd98f1f" moveToNextRelocation
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_a090402ae8777c0c" getSymbolName
  :: SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_3299fed07a74fc8d" getSymbolAddress
  :: SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_5434000ae14ca3d5" getSymbolSize
  :: SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_c7952e6df31a3639" getRelocationOffset
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1aabff55a62183cb" getRelocationSymbol
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO SymbolIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_9c818f2dfa8b4f52" getRelocationType
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO HsBindgen.Runtime.Prelude.Word64

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_a881e7f3f1d5266d" getRelocationTypeName
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_7b573863813771a3" getRelocationValueString
  :: RelocationIteratorRef
     {- ^ __from C:__ @rI@ -}
  -> IO (F.Ptr FC.CChar)

data OpaqueObjectFile

newtype ObjectFileRef = ObjectFileRef
  { un_ObjectFileRef :: F.Ptr OpaqueObjectFile
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_3dc776ac6d169d47" createObjectFile
  :: LlvmC.Raw.Types.MemoryBufferRef
     {- ^ __from C:__ @memBuf@ -}
  -> IO ObjectFileRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_3ed23b5ddd9e9bd3" disposeObjectFile
  :: ObjectFileRef
     {- ^ __from C:__ @objectFile@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_ebbb24fa505e89ce" getSections
  :: ObjectFileRef
     {- ^ __from C:__ @objectFile@ -}
  -> IO SectionIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_c3cefb2f7400f85c" isSectionIteratorAtEnd
  :: ObjectFileRef
     {- ^ __from C:__ @objectFile@ -}
  -> SectionIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_ac423558da540a41" getSymbols
  :: ObjectFileRef
     {- ^ __from C:__ @objectFile@ -}
  -> IO SymbolIteratorRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Object_1a7882c5e84b2a52" isSymbolIteratorAtEnd
  :: ObjectFileRef
     {- ^ __from C:__ @objectFile@ -}
  -> SymbolIteratorRef
     {- ^ __from C:__ @sI@ -}
  -> IO LlvmC.Raw.Types.Bool
