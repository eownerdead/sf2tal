{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Analysis where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Analysis.h>\nLLVMBool hs_bindgen_LlvmC_Raw_Analysis_c0c6a8a9638a0022 (LLVMModuleRef arg1, LLVMVerifierFailureAction arg2, char **arg3) { return LLVMVerifyModule(arg1, arg2, arg3); }\nLLVMBool hs_bindgen_LlvmC_Raw_Analysis_69aa8de3ae15b9a3 (LLVMValueRef arg1, LLVMVerifierFailureAction arg2) { return LLVMVerifyFunction(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Analysis_4bd1d340fb3f1e1b (LLVMValueRef arg1) { LLVMViewFunctionCFG(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Analysis_fa11245ddcf04e9b (LLVMValueRef arg1) { LLVMViewFunctionCFGOnly(arg1); }\n")

newtype VerifierFailureAction = VerifierFailureAction
  { un_VerifierFailureAction :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable VerifierFailureAction where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure VerifierFailureAction
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          VerifierFailureAction un_VerifierFailureAction2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_VerifierFailureAction2

instance HsBindgen.Runtime.CEnum.CEnum VerifierFailureAction where

  type CEnumZ VerifierFailureAction = FC.CUInt

  toCEnum = VerifierFailureAction

  fromCEnum = un_VerifierFailureAction

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "AbortProcessAction")
                                                     , (1, Data.List.NonEmpty.singleton "PrintMessageAction")
                                                     , (2, Data.List.NonEmpty.singleton "ReturnStatusAction")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "VerifierFailureAction"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "VerifierFailureAction"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum VerifierFailureAction where

  minDeclaredValue = AbortProcessAction

  maxDeclaredValue = ReturnStatusAction

instance Show VerifierFailureAction where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read VerifierFailureAction where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern AbortProcessAction :: VerifierFailureAction
pattern AbortProcessAction = VerifierFailureAction 0

pattern PrintMessageAction :: VerifierFailureAction
pattern PrintMessageAction = VerifierFailureAction 1

pattern ReturnStatusAction :: VerifierFailureAction
pattern ReturnStatusAction = VerifierFailureAction 2

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Analysis_c0c6a8a9638a0022" verifyModule
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> VerifierFailureAction
     {- ^ __from C:__ @action@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @outMessage@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Analysis_69aa8de3ae15b9a3" verifyFunction
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> VerifierFailureAction
     {- ^ __from C:__ @action@ -}
  -> IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Analysis_4bd1d340fb3f1e1b" viewFunctionCFG
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Analysis_fa11245ddcf04e9b" viewFunctionCFGOnly
  :: LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @fn@ -}
  -> IO ()
