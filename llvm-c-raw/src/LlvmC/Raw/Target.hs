{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Target where

import qualified Data.List.NonEmpty
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified LlvmC.Raw.Types
import Prelude ((<*>), Eq, IO, Int, Ord, Read, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/Target.h>\nvoid hs_bindgen_LlvmC_Raw_Target_369525e61a15b968 (void) { LLVMInitializeAArch64TargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_361f80afe8ecc770 (void) { LLVMInitializeAMDGPUTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_88d05979be4a2393 (void) { LLVMInitializeARMTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_0805a17a403374d1 (void) { LLVMInitializeAVRTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f37614f5dfce7cf9 (void) { LLVMInitializeBPFTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_15e847c5829c5d9a (void) { LLVMInitializeHexagonTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_9ff2bfada7ca5c16 (void) { LLVMInitializeLanaiTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_226d6a04f0218b4e (void) { LLVMInitializeLoongArchTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_2ff8f26bd2775ff4 (void) { LLVMInitializeMipsTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_1816134375a6b369 (void) { LLVMInitializeMSP430TargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_7522ff4618f0366d (void) { LLVMInitializeNVPTXTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_8074efce2bab0d25 (void) { LLVMInitializePowerPCTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_0e275f4655dce3da (void) { LLVMInitializeRISCVTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_cd0027ab11345ad3 (void) { LLVMInitializeSparcTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_727b41cd22e37d80 (void) { LLVMInitializeSystemZTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_faa183ff4ae6d570 (void) { LLVMInitializeVETargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a03a13ac8f58d0db (void) { LLVMInitializeWebAssemblyTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_b7a0439011309eea (void) { LLVMInitializeX86TargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_cf0f9c379e4a3b90 (void) { LLVMInitializeXCoreTargetInfo(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a30d5c4193a3571e (void) { LLVMInitializeAArch64Target(); }\nvoid hs_bindgen_LlvmC_Raw_Target_c8b9a5a23f827d5c (void) { LLVMInitializeAMDGPUTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_70c27ade08484aa2 (void) { LLVMInitializeARMTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_ec52e8a3615d0f5e (void) { LLVMInitializeAVRTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_6fe7a1dcb36b0592 (void) { LLVMInitializeBPFTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_9c4a1e127c089f06 (void) { LLVMInitializeHexagonTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_0ac12080a029bdfc (void) { LLVMInitializeLanaiTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_91b42b67f3d4a4ae (void) { LLVMInitializeLoongArchTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_5af8d41564168725 (void) { LLVMInitializeMipsTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_1c2fc5710aa0950e (void) { LLVMInitializeMSP430Target(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a7d02903356fc2fe (void) { LLVMInitializeNVPTXTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f1736bc35e6d5e79 (void) { LLVMInitializePowerPCTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_c811c3e153feed2b (void) { LLVMInitializeRISCVTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_c4802d6350733eeb (void) { LLVMInitializeSparcTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_fb3e0e46dc466a22 (void) { LLVMInitializeSystemZTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_77a57d7eea16a709 (void) { LLVMInitializeVETarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_85be982ae53ee6a0 (void) { LLVMInitializeWebAssemblyTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_42a9ee858a9e17e1 (void) { LLVMInitializeX86Target(); }\nvoid hs_bindgen_LlvmC_Raw_Target_77abffbe06217f6b (void) { LLVMInitializeXCoreTarget(); }\nvoid hs_bindgen_LlvmC_Raw_Target_34914171daac5ab9 (void) { LLVMInitializeAArch64TargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_5d4b4bde33970452 (void) { LLVMInitializeAMDGPUTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_6f7ac916963aef2f (void) { LLVMInitializeARMTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_6ad52dc90e89c7b6 (void) { LLVMInitializeAVRTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a9fdce72af6362d7 (void) { LLVMInitializeBPFTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a721503a64cc0704 (void) { LLVMInitializeHexagonTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_abdfdddd7163f89a (void) { LLVMInitializeLanaiTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_07ecdf7f9936f23a (void) { LLVMInitializeLoongArchTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f62d5492dda9aa0b (void) { LLVMInitializeMipsTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_0639b1294990ff29 (void) { LLVMInitializeMSP430TargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_36ab5e3f94caa90f (void) { LLVMInitializeNVPTXTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_254d7e8434f8cf9f (void) { LLVMInitializePowerPCTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_fed5296795fe2aa0 (void) { LLVMInitializeRISCVTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_e769f2a8fd0a15d1 (void) { LLVMInitializeSparcTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_1d2b945356e3fc4f (void) { LLVMInitializeSystemZTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_632e506da29d4274 (void) { LLVMInitializeVETargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_07076674bc8f3e0f (void) { LLVMInitializeWebAssemblyTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_e0a699bde1256bb9 (void) { LLVMInitializeX86TargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_4a784177b1e94ed8 (void) { LLVMInitializeXCoreTargetMC(); }\nvoid hs_bindgen_LlvmC_Raw_Target_2a37b1124e036b83 (void) { LLVMInitializeAArch64AsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_4be284bc86abea79 (void) { LLVMInitializeAMDGPUAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_de03d413938bff31 (void) { LLVMInitializeARMAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_d4997ed9274b16ce (void) { LLVMInitializeAVRAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_463a36cf66c5a803 (void) { LLVMInitializeBPFAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_ee48024b80178ed9 (void) { LLVMInitializeHexagonAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_e61c84884b082332 (void) { LLVMInitializeLanaiAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_c220691c13f09965 (void) { LLVMInitializeLoongArchAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_cf9f87833a59bc80 (void) { LLVMInitializeMipsAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_8c59e81f12c907b9 (void) { LLVMInitializeMSP430AsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_348c7af4822d4db2 (void) { LLVMInitializeNVPTXAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_1f0fafd0cfc86a20 (void) { LLVMInitializePowerPCAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_6444e715527e839b (void) { LLVMInitializeRISCVAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_2c2f1e04998b8676 (void) { LLVMInitializeSparcAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_711e6c17caebe606 (void) { LLVMInitializeSystemZAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_65a966fd27c9b1aa (void) { LLVMInitializeVEAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_86b98f0ae20da6d5 (void) { LLVMInitializeWebAssemblyAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_8f446c52505f550c (void) { LLVMInitializeX86AsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_76b6b589654b3ecd (void) { LLVMInitializeXCoreAsmPrinter(); }\nvoid hs_bindgen_LlvmC_Raw_Target_bb029011faf8e4e6 (void) { LLVMInitializeAArch64AsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_215f5f98d25372b7 (void) { LLVMInitializeAMDGPUAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_da3b30b0c1023967 (void) { LLVMInitializeARMAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_bba11dfd796bb691 (void) { LLVMInitializeAVRAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_b4e180e5a994cdbc (void) { LLVMInitializeBPFAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_c05a609784a792bf (void) { LLVMInitializeHexagonAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f95cdb36c481e466 (void) { LLVMInitializeLanaiAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_47ad7f1d3ba8513a (void) { LLVMInitializeLoongArchAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_01943e6c5c709f2e (void) { LLVMInitializeMipsAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_b83bdc680cbdb8fc (void) { LLVMInitializeMSP430AsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_4bc91f24341b994c (void) { LLVMInitializePowerPCAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_904e6751a257e6bf (void) { LLVMInitializeRISCVAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a1717b21c5082a66 (void) { LLVMInitializeSparcAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_b3f93744cc110b5d (void) { LLVMInitializeSystemZAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_117448320ba25f17 (void) { LLVMInitializeVEAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_ea88434e46493686 (void) { LLVMInitializeWebAssemblyAsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_ef4bba46500ea863 (void) { LLVMInitializeX86AsmParser(); }\nvoid hs_bindgen_LlvmC_Raw_Target_333012e3e3b58648 (void) { LLVMInitializeAArch64Disassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_647944f6c657a7cb (void) { LLVMInitializeAMDGPUDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_749d415c9753e238 (void) { LLVMInitializeARMDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_5dfe5b2b8a00f81c (void) { LLVMInitializeAVRDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_0f865307b4d384ff (void) { LLVMInitializeBPFDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_2177911ff9a24cb6 (void) { LLVMInitializeHexagonDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_9e96d203aca4876e (void) { LLVMInitializeLanaiDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_1ea426ecbe92953b (void) { LLVMInitializeLoongArchDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_37bc66906f75eef7 (void) { LLVMInitializeMipsDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_a44a526cdb007637 (void) { LLVMInitializeMSP430Disassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_dae1195e1cffe7bf (void) { LLVMInitializePowerPCDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_fa43cf53f7a621f7 (void) { LLVMInitializeRISCVDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_6b6e07dbb8d64734 (void) { LLVMInitializeSparcDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_132f0edbb5ff47d5 (void) { LLVMInitializeSystemZDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f38593f41125418f (void) { LLVMInitializeVEDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_55d12b6139101582 (void) { LLVMInitializeWebAssemblyDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_f9a97a840bfd502b (void) { LLVMInitializeX86Disassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_d66ceaa645f95f40 (void) { LLVMInitializeXCoreDisassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Target_d2ec1da2337682e8 (void) { LLVMInitializeAllTargetInfos(); }\nvoid hs_bindgen_LlvmC_Raw_Target_dc478e1698db11c0 (void) { LLVMInitializeAllTargets(); }\nvoid hs_bindgen_LlvmC_Raw_Target_578b2f11f4e0223c (void) { LLVMInitializeAllTargetMCs(); }\nvoid hs_bindgen_LlvmC_Raw_Target_5c90bbb3be6fa0d6 (void) { LLVMInitializeAllAsmPrinters(); }\nvoid hs_bindgen_LlvmC_Raw_Target_e2e3821ac7a4b30c (void) { LLVMInitializeAllAsmParsers(); }\nvoid hs_bindgen_LlvmC_Raw_Target_411d36bbf0661ce6 (void) { LLVMInitializeAllDisassemblers(); }\nLLVMBool hs_bindgen_LlvmC_Raw_Target_b3195d8ea920250d (void) { return LLVMInitializeNativeTarget(); }\nLLVMBool hs_bindgen_LlvmC_Raw_Target_8e34a79fc75e43b1 (void) { return LLVMInitializeNativeAsmParser(); }\nLLVMBool hs_bindgen_LlvmC_Raw_Target_605a2a3eeee3485b (void) { return LLVMInitializeNativeAsmPrinter(); }\nLLVMBool hs_bindgen_LlvmC_Raw_Target_3cf9906b4fb8ff32 (void) { return LLVMInitializeNativeDisassembler(); }\nLLVMTargetDataRef hs_bindgen_LlvmC_Raw_Target_1ebc1924d8569459 (LLVMModuleRef arg1) { return LLVMGetModuleDataLayout(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Target_b7dcdb2c54b07fcb (LLVMModuleRef arg1, LLVMTargetDataRef arg2) { LLVMSetModuleDataLayout(arg1, arg2); }\nLLVMTargetDataRef hs_bindgen_LlvmC_Raw_Target_db6528c20202d9da (char *arg1) { return LLVMCreateTargetData(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Target_95deac5453d7f3ce (LLVMTargetDataRef arg1) { LLVMDisposeTargetData(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Target_ab4617097460110e (LLVMTargetLibraryInfoRef arg1, LLVMPassManagerRef arg2) { LLVMAddTargetLibraryInfo(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Target_d4630a9c3ff5c56b (LLVMTargetDataRef arg1) { return LLVMCopyStringRepOfTargetData(arg1); }\nenum LLVMByteOrdering hs_bindgen_LlvmC_Raw_Target_5623e00dc6ac72b6 (LLVMTargetDataRef arg1) { return LLVMByteOrder(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_6c0287a796628e14 (LLVMTargetDataRef arg1) { return LLVMPointerSize(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_12cc9fea7ed254af (LLVMTargetDataRef arg1, unsigned int arg2) { return LLVMPointerSizeForAS(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Target_4aaa4dbb9524cc45 (LLVMTargetDataRef arg1) { return LLVMIntPtrType(arg1); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Target_e4f07f3695c54844 (LLVMTargetDataRef arg1, unsigned int arg2) { return LLVMIntPtrTypeForAS(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Target_536ae76b58aca294 (LLVMContextRef arg1, LLVMTargetDataRef arg2) { return LLVMIntPtrTypeInContext(arg1, arg2); }\nLLVMTypeRef hs_bindgen_LlvmC_Raw_Target_1a9dd9ba121061e6 (LLVMContextRef arg1, LLVMTargetDataRef arg2, unsigned int arg3) { return LLVMIntPtrTypeForASInContext(arg1, arg2, arg3); }\nunsigned long long hs_bindgen_LlvmC_Raw_Target_abc203a0ef4be866 (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMSizeOfTypeInBits(arg1, arg2); }\nunsigned long long hs_bindgen_LlvmC_Raw_Target_8c2e7169b1b4fdd5 (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMStoreSizeOfType(arg1, arg2); }\nunsigned long long hs_bindgen_LlvmC_Raw_Target_b1f59d1e83189024 (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMABISizeOfType(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_faa2779c5b50d97b (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMABIAlignmentOfType(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_9f18f56419f07fa4 (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMCallFrameAlignmentOfType(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_1127b5b1cfe7b283 (LLVMTargetDataRef arg1, LLVMTypeRef arg2) { return LLVMPreferredAlignmentOfType(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_59d8ff32e4fbd38f (LLVMTargetDataRef arg1, LLVMValueRef arg2) { return LLVMPreferredAlignmentOfGlobal(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Target_93691aa42eaa6d10 (LLVMTargetDataRef arg1, LLVMTypeRef arg2, unsigned long long arg3) { return LLVMElementAtOffset(arg1, arg2, arg3); }\nunsigned long long hs_bindgen_LlvmC_Raw_Target_d070621182325aad (LLVMTargetDataRef arg1, LLVMTypeRef arg2, unsigned int arg3) { return LLVMOffsetOfElement(arg1, arg2, arg3); }\n")

newtype ByteOrdering = ByteOrdering
  { un_ByteOrdering :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable ByteOrdering where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure ByteOrdering
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          ByteOrdering un_ByteOrdering2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_ByteOrdering2

instance HsBindgen.Runtime.CEnum.CEnum ByteOrdering where

  type CEnumZ ByteOrdering = FC.CUInt

  toCEnum = ByteOrdering

  fromCEnum = un_ByteOrdering

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "BigEndian")
                                                     , (1, Data.List.NonEmpty.singleton "LittleEndian")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "ByteOrdering"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "ByteOrdering"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum ByteOrdering where

  minDeclaredValue = BigEndian

  maxDeclaredValue = LittleEndian

instance Show ByteOrdering where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read ByteOrdering where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern BigEndian :: ByteOrdering
pattern BigEndian = ByteOrdering 0

pattern LittleEndian :: ByteOrdering
pattern LittleEndian = ByteOrdering 1

data OpaqueTargetData

newtype TargetDataRef = TargetDataRef
  { un_TargetDataRef :: F.Ptr OpaqueTargetData
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueTargetLibraryInfotData

newtype TargetLibraryInfoRef = TargetLibraryInfoRef
  { un_TargetLibraryInfoRef :: F.Ptr OpaqueTargetLibraryInfotData
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_369525e61a15b968" initializeAArch64TargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_361f80afe8ecc770" initializeAMDGPUTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_88d05979be4a2393" initializeARMTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_0805a17a403374d1" initializeAVRTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f37614f5dfce7cf9" initializeBPFTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_15e847c5829c5d9a" initializeHexagonTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_9ff2bfada7ca5c16" initializeLanaiTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_226d6a04f0218b4e" initializeLoongArchTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_2ff8f26bd2775ff4" initializeMipsTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1816134375a6b369" initializeMSP430TargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_7522ff4618f0366d" initializeNVPTXTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_8074efce2bab0d25" initializePowerPCTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_0e275f4655dce3da" initializeRISCVTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_cd0027ab11345ad3" initializeSparcTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_727b41cd22e37d80" initializeSystemZTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_faa183ff4ae6d570" initializeVETargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a03a13ac8f58d0db" initializeWebAssemblyTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b7a0439011309eea" initializeX86TargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_cf0f9c379e4a3b90" initializeXCoreTargetInfo
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a30d5c4193a3571e" initializeAArch64Target
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_c8b9a5a23f827d5c" initializeAMDGPUTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_70c27ade08484aa2" initializeARMTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_ec52e8a3615d0f5e" initializeAVRTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6fe7a1dcb36b0592" initializeBPFTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_9c4a1e127c089f06" initializeHexagonTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_0ac12080a029bdfc" initializeLanaiTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_91b42b67f3d4a4ae" initializeLoongArchTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_5af8d41564168725" initializeMipsTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1c2fc5710aa0950e" initializeMSP430Target
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a7d02903356fc2fe" initializeNVPTXTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f1736bc35e6d5e79" initializePowerPCTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_c811c3e153feed2b" initializeRISCVTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_c4802d6350733eeb" initializeSparcTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_fb3e0e46dc466a22" initializeSystemZTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_77a57d7eea16a709" initializeVETarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_85be982ae53ee6a0" initializeWebAssemblyTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_42a9ee858a9e17e1" initializeX86Target
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_77abffbe06217f6b" initializeXCoreTarget
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_34914171daac5ab9" initializeAArch64TargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_5d4b4bde33970452" initializeAMDGPUTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6f7ac916963aef2f" initializeARMTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6ad52dc90e89c7b6" initializeAVRTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a9fdce72af6362d7" initializeBPFTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a721503a64cc0704" initializeHexagonTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_abdfdddd7163f89a" initializeLanaiTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_07ecdf7f9936f23a" initializeLoongArchTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f62d5492dda9aa0b" initializeMipsTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_0639b1294990ff29" initializeMSP430TargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_36ab5e3f94caa90f" initializeNVPTXTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_254d7e8434f8cf9f" initializePowerPCTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_fed5296795fe2aa0" initializeRISCVTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_e769f2a8fd0a15d1" initializeSparcTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1d2b945356e3fc4f" initializeSystemZTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_632e506da29d4274" initializeVETargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_07076674bc8f3e0f" initializeWebAssemblyTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_e0a699bde1256bb9" initializeX86TargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_4a784177b1e94ed8" initializeXCoreTargetMC
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_2a37b1124e036b83" initializeAArch64AsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_4be284bc86abea79" initializeAMDGPUAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_de03d413938bff31" initializeARMAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_d4997ed9274b16ce" initializeAVRAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_463a36cf66c5a803" initializeBPFAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_ee48024b80178ed9" initializeHexagonAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_e61c84884b082332" initializeLanaiAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_c220691c13f09965" initializeLoongArchAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_cf9f87833a59bc80" initializeMipsAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_8c59e81f12c907b9" initializeMSP430AsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_348c7af4822d4db2" initializeNVPTXAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1f0fafd0cfc86a20" initializePowerPCAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6444e715527e839b" initializeRISCVAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_2c2f1e04998b8676" initializeSparcAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_711e6c17caebe606" initializeSystemZAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_65a966fd27c9b1aa" initializeVEAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_86b98f0ae20da6d5" initializeWebAssemblyAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_8f446c52505f550c" initializeX86AsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_76b6b589654b3ecd" initializeXCoreAsmPrinter
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_bb029011faf8e4e6" initializeAArch64AsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_215f5f98d25372b7" initializeAMDGPUAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_da3b30b0c1023967" initializeARMAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_bba11dfd796bb691" initializeAVRAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b4e180e5a994cdbc" initializeBPFAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_c05a609784a792bf" initializeHexagonAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f95cdb36c481e466" initializeLanaiAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_47ad7f1d3ba8513a" initializeLoongArchAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_01943e6c5c709f2e" initializeMipsAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b83bdc680cbdb8fc" initializeMSP430AsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_4bc91f24341b994c" initializePowerPCAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_904e6751a257e6bf" initializeRISCVAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a1717b21c5082a66" initializeSparcAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b3f93744cc110b5d" initializeSystemZAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_117448320ba25f17" initializeVEAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_ea88434e46493686" initializeWebAssemblyAsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_ef4bba46500ea863" initializeX86AsmParser
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_333012e3e3b58648" initializeAArch64Disassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_647944f6c657a7cb" initializeAMDGPUDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_749d415c9753e238" initializeARMDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_5dfe5b2b8a00f81c" initializeAVRDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_0f865307b4d384ff" initializeBPFDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_2177911ff9a24cb6" initializeHexagonDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_9e96d203aca4876e" initializeLanaiDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1ea426ecbe92953b" initializeLoongArchDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_37bc66906f75eef7" initializeMipsDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_a44a526cdb007637" initializeMSP430Disassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_dae1195e1cffe7bf" initializePowerPCDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_fa43cf53f7a621f7" initializeRISCVDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6b6e07dbb8d64734" initializeSparcDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_132f0edbb5ff47d5" initializeSystemZDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f38593f41125418f" initializeVEDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_55d12b6139101582" initializeWebAssemblyDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_f9a97a840bfd502b" initializeX86Disassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_d66ceaa645f95f40" initializeXCoreDisassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_d2ec1da2337682e8" initializeAllTargetInfos
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_dc478e1698db11c0" initializeAllTargets
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_578b2f11f4e0223c" initializeAllTargetMCs
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_5c90bbb3be6fa0d6" initializeAllAsmPrinters
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_e2e3821ac7a4b30c" initializeAllAsmParsers
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_411d36bbf0661ce6" initializeAllDisassemblers
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b3195d8ea920250d" initializeNativeTarget
  :: IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_8e34a79fc75e43b1" initializeNativeAsmParser
  :: IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_605a2a3eeee3485b" initializeNativeAsmPrinter
  :: IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_3cf9906b4fb8ff32" initializeNativeDisassembler
  :: IO LlvmC.Raw.Types.Bool

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1ebc1924d8569459" getModuleDataLayout
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> IO TargetDataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b7dcdb2c54b07fcb" setModuleDataLayout
  :: LlvmC.Raw.Types.ModuleRef
     {- ^ __from C:__ @m@ -}
  -> TargetDataRef
     {- ^ __from C:__ @dL@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_db6528c20202d9da" createTargetData
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @stringRep@ -}
  -> IO TargetDataRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_95deac5453d7f3ce" disposeTargetData
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_ab4617097460110e" addTargetLibraryInfo
  :: TargetLibraryInfoRef
     {- ^ __from C:__ @tLI@ -}
  -> LlvmC.Raw.Types.PassManagerRef
     {- ^ __from C:__ @pM@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_d4630a9c3ff5c56b" copyStringRepOfTargetData
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_5623e00dc6ac72b6" byteOrder
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO ByteOrdering

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_6c0287a796628e14" pointerSize
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_12cc9fea7ed254af" pointerSizeForAS
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> FC.CUInt
     {- ^ __from C:__ @aS@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_4aaa4dbb9524cc45" intPtrType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_e4f07f3695c54844" intPtrTypeForAS
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> FC.CUInt
     {- ^ __from C:__ @aS@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_536ae76b58aca294" intPtrTypeInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1a9dd9ba121061e6" intPtrTypeForASInContext
  :: LlvmC.Raw.Types.ContextRef
     {- ^ __from C:__ @c@ -}
  -> TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> FC.CUInt
     {- ^ __from C:__ @aS@ -}
  -> IO LlvmC.Raw.Types.TypeRef

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_abc203a0ef4be866" sizeOfTypeInBits
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CULLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_8c2e7169b1b4fdd5" storeSizeOfType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CULLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_b1f59d1e83189024" aBISizeOfType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CULLong

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_faa2779c5b50d97b" aBIAlignmentOfType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_9f18f56419f07fa4" callFrameAlignmentOfType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_1127b5b1cfe7b283" preferredAlignmentOfType
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @ty@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_59d8ff32e4fbd38f" preferredAlignmentOfGlobal
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.ValueRef
     {- ^ __from C:__ @globalVar@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_93691aa42eaa6d10" elementAtOffset
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> FC.CULLong
     {- ^ __from C:__ @offset@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Target_d070621182325aad" offsetOfElement
  :: TargetDataRef
     {- ^ __from C:__ @tD@ -}
  -> LlvmC.Raw.Types.TypeRef
     {- ^ __from C:__ @structTy@ -}
  -> FC.CUInt
     {- ^ __from C:__ @element@ -}
  -> IO FC.CULLong
