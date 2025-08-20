{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell #-}

module LlvmC.Raw.DisassemblerTypes where

import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.Prelude
import Prelude ((<*>), (>>), Eq, IO, Int, Ord, Show, pure)

$(CAPI.addCSource "#define const\n")

newtype DisasmContextRef = DisasmContextRef
  { un_DisasmContextRef :: F.Ptr Void
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype OpInfoCallback = OpInfoCallback
  { un_OpInfoCallback :: F.FunPtr ((F.Ptr Void) -> HsBindgen.Runtime.Prelude.Word64 -> HsBindgen.Runtime.Prelude.Word64 -> HsBindgen.Runtime.Prelude.Word64 -> HsBindgen.Runtime.Prelude.Word64 -> FC.CInt -> (F.Ptr Void) -> IO FC.CInt)
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpInfoSymbol1 = OpInfoSymbol1
  { opInfoSymbol1_Present :: HsBindgen.Runtime.Prelude.Word64
  , opInfoSymbol1_Name :: F.Ptr FC.CChar
  , opInfoSymbol1_Value :: HsBindgen.Runtime.Prelude.Word64
  }
  deriving stock (Eq, Show)

instance F.Storable OpInfoSymbol1 where

  sizeOf = \_ -> (24 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OpInfoSymbol1
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)
      <*> F.peekByteOff ptr0 (16 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OpInfoSymbol1 opInfoSymbol1_Present2 opInfoSymbol1_Name3 opInfoSymbol1_Value4 ->
               F.pokeByteOff ptr0 (0 :: Int) opInfoSymbol1_Present2
            >> F.pokeByteOff ptr0 (8 :: Int) opInfoSymbol1_Name3
            >> F.pokeByteOff ptr0 (16 :: Int) opInfoSymbol1_Value4

data OpInfo1 = OpInfo1
  { opInfo1_AddSymbol :: OpInfoSymbol1
  , opInfo1_SubtractSymbol :: OpInfoSymbol1
  , opInfo1_Value :: HsBindgen.Runtime.Prelude.Word64
  , opInfo1_VariantKind :: HsBindgen.Runtime.Prelude.Word64
  }
  deriving stock (Eq, Show)

instance F.Storable OpInfo1 where

  sizeOf = \_ -> (64 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure OpInfo1
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (24 :: Int)
      <*> F.peekByteOff ptr0 (48 :: Int)
      <*> F.peekByteOff ptr0 (56 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          OpInfo1
            opInfo1_AddSymbol2
            opInfo1_SubtractSymbol3
            opInfo1_Value4
            opInfo1_VariantKind5 ->
                 F.pokeByteOff ptr0 (0 :: Int) opInfo1_AddSymbol2
              >> F.pokeByteOff ptr0 (24 :: Int) opInfo1_SubtractSymbol3
              >> F.pokeByteOff ptr0 (48 :: Int) opInfo1_Value4
              >> F.pokeByteOff ptr0 (56 :: Int) opInfo1_VariantKind5

disassembler_VariantKind_ARM_HI16 :: FC.CInt
disassembler_VariantKind_ARM_HI16 = (1 :: FC.CInt)

disassembler_VariantKind_ARM_LO16 :: FC.CInt
disassembler_VariantKind_ARM_LO16 = (2 :: FC.CInt)

disassembler_VariantKind_ARM64_PAGE :: FC.CInt
disassembler_VariantKind_ARM64_PAGE = (1 :: FC.CInt)

disassembler_VariantKind_ARM64_PAGEOFF :: FC.CInt
disassembler_VariantKind_ARM64_PAGEOFF =
  (2 :: FC.CInt)

disassembler_VariantKind_ARM64_GOTPAGE :: FC.CInt
disassembler_VariantKind_ARM64_GOTPAGE =
  (3 :: FC.CInt)

disassembler_VariantKind_ARM64_GOTPAGEOFF :: FC.CInt
disassembler_VariantKind_ARM64_GOTPAGEOFF =
  (4 :: FC.CInt)

disassembler_VariantKind_ARM64_TLVP :: FC.CInt
disassembler_VariantKind_ARM64_TLVP = (5 :: FC.CInt)

disassembler_VariantKind_ARM64_TLVOFF :: FC.CInt
disassembler_VariantKind_ARM64_TLVOFF =
  (6 :: FC.CInt)

newtype SymbolLookupCallback = SymbolLookupCallback
  { un_SymbolLookupCallback :: F.FunPtr ((F.Ptr Void) -> HsBindgen.Runtime.Prelude.Word64 -> (F.Ptr HsBindgen.Runtime.Prelude.Word64) -> HsBindgen.Runtime.Prelude.Word64 -> (F.Ptr (F.Ptr FC.CChar)) -> IO (F.Ptr FC.CChar))
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

disassembler_ReferenceType_In_Branch :: FC.CInt
disassembler_ReferenceType_In_Branch = (1 :: FC.CInt)

disassembler_ReferenceType_In_PCrel_Load :: FC.CInt
disassembler_ReferenceType_In_PCrel_Load =
  (2 :: FC.CInt)

disassembler_ReferenceType_In_ARM64_ADRP :: FC.CInt
disassembler_ReferenceType_In_ARM64_ADRP =
  (4294967297 :: FC.CInt)

disassembler_ReferenceType_In_ARM64_ADDXri :: FC.CInt
disassembler_ReferenceType_In_ARM64_ADDXri =
  (4294967298 :: FC.CInt)

disassembler_ReferenceType_In_ARM64_LDRXui :: FC.CInt
disassembler_ReferenceType_In_ARM64_LDRXui =
  (4294967299 :: FC.CInt)

disassembler_ReferenceType_In_ARM64_LDRXl :: FC.CInt
disassembler_ReferenceType_In_ARM64_LDRXl =
  (4294967300 :: FC.CInt)

disassembler_ReferenceType_In_ARM64_ADR :: FC.CInt
disassembler_ReferenceType_In_ARM64_ADR =
  (4294967301 :: FC.CInt)

disassembler_ReferenceType_Out_SymbolStub :: FC.CInt
disassembler_ReferenceType_Out_SymbolStub =
  (1 :: FC.CInt)

disassembler_ReferenceType_Out_LitPool_SymAddr :: FC.CInt
disassembler_ReferenceType_Out_LitPool_SymAddr =
  (2 :: FC.CInt)

disassembler_ReferenceType_Out_LitPool_CstrAddr :: FC.CInt
disassembler_ReferenceType_Out_LitPool_CstrAddr =
  (3 :: FC.CInt)

disassembler_ReferenceType_Out_Objc_CFString_Ref :: FC.CInt
disassembler_ReferenceType_Out_Objc_CFString_Ref =
  (4 :: FC.CInt)

disassembler_ReferenceType_Out_Objc_Message :: FC.CInt
disassembler_ReferenceType_Out_Objc_Message =
  (5 :: FC.CInt)

disassembler_ReferenceType_Out_Objc_Message_Ref :: FC.CInt
disassembler_ReferenceType_Out_Objc_Message_Ref =
  (6 :: FC.CInt)

disassembler_ReferenceType_Out_Objc_Selector_Ref :: FC.CInt
disassembler_ReferenceType_Out_Objc_Selector_Ref =
  (7 :: FC.CInt)

disassembler_ReferenceType_Out_Objc_Class_Ref :: FC.CInt
disassembler_ReferenceType_Out_Objc_Class_Ref =
  (8 :: FC.CInt)

disassembler_ReferenceType_DeMangled_Name :: FC.CInt
disassembler_ReferenceType_DeMangled_Name =
  (9 :: FC.CInt)
