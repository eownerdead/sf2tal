{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Comdat where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Comdat.h>\nLLVMComdatRef hs_bindgen_LlvmC_Raw_Comdat_b44f74ae5a2875bc (LLVMModuleRef arg1, char *arg2) { return LLVMGetOrInsertComdat(arg1, arg2); }\nLLVMComdatRef hs_bindgen_LlvmC_Raw_Comdat_75d59b3c5ef45a77 (LLVMValueRef arg1) { return LLVMGetComdat(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Comdat_9bc0f0c6988ca5e5 (LLVMValueRef arg1, LLVMComdatRef arg2) { LLVMSetComdat(arg1, arg2); }\nLLVMComdatSelectionKind hs_bindgen_LlvmC_Raw_Comdat_d3b0f2d478edd42b (LLVMComdatRef arg1) { return LLVMGetComdatSelectionKind(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Comdat_42e1206740675686 (LLVMComdatRef arg1, LLVMComdatSelectionKind arg2) { LLVMSetComdatSelectionKind(arg1, arg2); }\n")

newtype ComdatSelectionKind = ComdatSelectionKind
  { un_ComdatSelectionKind :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable ComdatSelectionKind where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure ComdatSelectionKind
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          ComdatSelectionKind un_ComdatSelectionKind2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_ComdatSelectionKind2

instance HsBindgen.Runtime.CEnum.CEnum ComdatSelectionKind where

  type CEnumZ ComdatSelectionKind = FC.CUInt

  toCEnum = ComdatSelectionKind

  fromCEnum = un_ComdatSelectionKind

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "AnyComdatSelectionKind")
                                                     , (1, Data.List.NonEmpty.singleton "ExactMatchComdatSelectionKind")
                                                     , (2, Data.List.NonEmpty.singleton "LargestComdatSelectionKind")
                                                     , (3, Data.List.NonEmpty.singleton "NoDeduplicateComdatSelectionKind")
                                                     , (4, Data.List.NonEmpty.singleton "SameSizeComdatSelectionKind")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "ComdatSelectionKind"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "ComdatSelectionKind"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum ComdatSelectionKind where

  minDeclaredValue = AnyComdatSelectionKind

  maxDeclaredValue = SameSizeComdatSelectionKind

instance Show ComdatSelectionKind where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read ComdatSelectionKind where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern AnyComdatSelectionKind :: ComdatSelectionKind
pattern AnyComdatSelectionKind = ComdatSelectionKind 0

pattern ExactMatchComdatSelectionKind :: ComdatSelectionKind
pattern ExactMatchComdatSelectionKind = ComdatSelectionKind 1

pattern LargestComdatSelectionKind :: ComdatSelectionKind
pattern LargestComdatSelectionKind = ComdatSelectionKind 2

pattern NoDeduplicateComdatSelectionKind :: ComdatSelectionKind
pattern NoDeduplicateComdatSelectionKind = ComdatSelectionKind 3

pattern SameSizeComdatSelectionKind :: ComdatSelectionKind
pattern SameSizeComdatSelectionKind = ComdatSelectionKind 4

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Comdat_b44f74ae5a2875bc" getOrInsertComdat
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> IO LlvmC.Raw.Types.ComdatRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Comdat_75d59b3c5ef45a77" getComdat
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> IO LlvmC.Raw.Types.ComdatRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Comdat_9bc0f0c6988ca5e5" setComdat
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @v@ -}
  -> LlvmC.Raw.Types.ComdatRef
     {- ^ __from C:__ @c@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Comdat_d3b0f2d478edd42b" getComdatSelectionKind
  :: LlvmC.Raw.Types.ComdatRef
     {- ^ __from C:__ @c@ -}
  -> IO ComdatSelectionKind

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Comdat_42e1206740675686" setComdatSelectionKind
  :: LlvmC.Raw.Types.ComdatRef
     {- ^ __from C:__ @c@ -}
  -> ComdatSelectionKind
     {- ^ __from C:__ @kind@ -}
  -> IO ()
