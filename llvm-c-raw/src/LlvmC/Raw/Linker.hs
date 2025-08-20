{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Linker where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Linker.h>\nLLVMBool hs_bindgen_LlvmC_Raw_Linker_e86db08374f0835f (LLVMModuleRef arg1, LLVMModuleRef arg2) { return LLVMLinkModules2(arg1, arg2); }\n")

newtype LinkerMode = LinkerMode
  { un_LinkerMode :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable LinkerMode where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure LinkerMode
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          LinkerMode un_LinkerMode2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_LinkerMode2

instance HsBindgen.Runtime.CEnum.CEnum LinkerMode where

  type CEnumZ LinkerMode = FC.CUInt

  toCEnum = LinkerMode

  fromCEnum = un_LinkerMode

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "LinkerDestroySource")
                                                     , (1, Data.List.NonEmpty.singleton "LinkerPreserveSource_Removed")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "LinkerMode"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "LinkerMode"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum LinkerMode where

  minDeclaredValue = LinkerDestroySource

  maxDeclaredValue = LinkerPreserveSource_Removed

instance Show LinkerMode where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read LinkerMode where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LinkerDestroySource :: LinkerMode
pattern LinkerDestroySource = LinkerMode 0

pattern LinkerPreserveSource_Removed :: LinkerMode
pattern LinkerPreserveSource_Removed = LinkerMode 1

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Linker_e86db08374f0835f" linkModules2
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @dest@ -}
  -> LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @src@ -}
  -> IO LlvmC.Raw.Types.Bool
