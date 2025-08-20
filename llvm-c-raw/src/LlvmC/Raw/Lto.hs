{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module LlvmC.Raw.Lto where

import C.Expr.HostPlatform ((+), (<<), (>=))
import qualified C.Expr.HostPlatform as C
import Data.Bits (FiniteBits)
import qualified Data.Bits as Bits
import qualified Data.Ix as Ix
import qualified Data.List.NonEmpty
import Data.Void (Void)
import qualified Foreign as F
import qualified Foreign.C as FC
import qualified HsBindgen.Runtime.CAPI
import qualified HsBindgen.Runtime.CAPI as CAPI
import qualified HsBindgen.Runtime.CEnum
import qualified HsBindgen.Runtime.ConstantArray
import qualified HsBindgen.Runtime.Prelude
import Prelude ((<*>), (>>), Bounded, Enum, Eq, IO, Int, Integral, Num, Ord, Read, Real, Show, pure, showsPrec)
import qualified Text.Read

$(CAPI.addCSource "#define const\n#include <llvm-c/lto.h>\nchar *hs_bindgen_LlvmC_Raw_Lto_47100290d68e0a67 (void) { return lto_get_version(); }\nchar *hs_bindgen_LlvmC_Raw_Lto_fd4f5a7fefad7964 (void) { return lto_get_error_message(); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_c4068f901f2d522e (char *arg1) { return lto_module_is_object_file(arg1); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_e83f05229dd75926 (char *arg1, char *arg2) { return lto_module_is_object_file_for_target(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_a1a882b7d18c5d55 (void *arg1, size_t arg2) { return lto_module_has_objc_category(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_1cb60185a13472e9 (void *arg1, size_t arg2) { return lto_module_is_object_file_in_memory(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_786aeb363826a839 (void *arg1, size_t arg2, char *arg3) { return lto_module_is_object_file_in_memory_for_target(arg1, arg2, arg3); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_dd33b203ed8d873c (char *arg1) { return lto_module_create(arg1); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_6c5f580546d96ded (void *arg1, size_t arg2) { return lto_module_create_from_memory(arg1, arg2); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_337bd587befeff33 (void *arg1, size_t arg2, char *arg3) { return lto_module_create_from_memory_with_path(arg1, arg2, arg3); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_3dce1b2df5c57e4f (void *arg1, size_t arg2, char *arg3) { return lto_module_create_in_local_context(arg1, arg2, arg3); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_628188f55144d20b (void *arg1, size_t arg2, char *arg3, lto_code_gen_t arg4) { return lto_module_create_in_codegen_context(arg1, arg2, arg3, arg4); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_9bedf167fb4beb9b (signed int arg1, char *arg2, size_t arg3) { return lto_module_create_from_fd(arg1, arg2, arg3); }\nlto_module_t hs_bindgen_LlvmC_Raw_Lto_d1ece35eeb475a53 (signed int arg1, char *arg2, size_t arg3, size_t arg4, off_t arg5) { return lto_module_create_from_fd_at_offset(arg1, arg2, arg3, arg4, arg5); }\nvoid hs_bindgen_LlvmC_Raw_Lto_304ff46b4d545a99 (lto_module_t arg1) { lto_module_dispose(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Lto_62a25fce40b551a2 (lto_module_t arg1) { return lto_module_get_target_triple(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Lto_9277186bf27a4cd0 (lto_module_t arg1, char *arg2) { lto_module_set_target_triple(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Lto_f63deea05d359be4 (lto_module_t arg1) { return lto_module_get_num_symbols(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Lto_b1875f816302c03a (lto_module_t arg1, unsigned int arg2) { return lto_module_get_symbol_name(arg1, arg2); }\nlto_symbol_attributes hs_bindgen_LlvmC_Raw_Lto_327ec77f75227a4a (lto_module_t arg1, unsigned int arg2) { return lto_module_get_symbol_attribute(arg1, arg2); }\nchar *hs_bindgen_LlvmC_Raw_Lto_6ee224fced7a5fb8 (lto_module_t arg1) { return lto_module_get_linkeropts(arg1); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_885699f624e484fb (lto_module_t arg1, unsigned int *arg2, unsigned int *arg3) { return lto_module_get_macho_cputype(arg1, arg2, arg3); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_e27775a2fb0eb169 (lto_module_t arg1) { return lto_module_has_ctor_dtor(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Lto_e7ee7b1955f1ae16 (lto_code_gen_t arg1, lto_diagnostic_handler_t arg2, void *arg3) { lto_codegen_set_diagnostic_handler(arg1, arg2, arg3); }\nlto_code_gen_t hs_bindgen_LlvmC_Raw_Lto_acc06fc19f554e37 (void) { return lto_codegen_create(); }\nlto_code_gen_t hs_bindgen_LlvmC_Raw_Lto_1047db82a2fa4d5a (void) { return lto_codegen_create_in_local_context(); }\nvoid hs_bindgen_LlvmC_Raw_Lto_dc6171a35cbc1334 (lto_code_gen_t arg1) { lto_codegen_dispose(arg1); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_6a18f3fff57435d1 (lto_code_gen_t arg1, lto_module_t arg2) { return lto_codegen_add_module(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_e05d3db925e09ee5 (lto_code_gen_t arg1, lto_module_t arg2) { lto_codegen_set_module(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_3d73f232c1990772 (lto_code_gen_t arg1, lto_debug_model arg2) { return lto_codegen_set_debug_model(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_078403b3e69f87fc (lto_code_gen_t arg1, lto_codegen_model arg2) { return lto_codegen_set_pic_model(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_d0dc7445379e90f8 (lto_code_gen_t arg1, char *arg2) { lto_codegen_set_cpu(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_1a57acb6d97c2bed (lto_code_gen_t arg1, char *arg2) { lto_codegen_set_assembler_path(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_0238791b1e520adf (lto_code_gen_t arg1, char **arg2, signed int arg3) { lto_codegen_set_assembler_args(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Lto_94e76935bc2aac78 (lto_code_gen_t arg1, char *arg2) { lto_codegen_add_must_preserve_symbol(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_890504289993b5d1 (lto_code_gen_t arg1, char *arg2) { return lto_codegen_write_merged_modules(arg1, arg2); }\nvoid *hs_bindgen_LlvmC_Raw_Lto_212c83986d069b0e (lto_code_gen_t arg1, size_t *arg2) { return lto_codegen_compile(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_e75f21f0a9ddadd4 (lto_code_gen_t arg1, char **arg2) { return lto_codegen_compile_to_file(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_f09a979b870f94e5 (lto_code_gen_t arg1) { return lto_codegen_optimize(arg1); }\nvoid *hs_bindgen_LlvmC_Raw_Lto_c10c1cc6c03b90a3 (lto_code_gen_t arg1, size_t *arg2) { return lto_codegen_compile_optimized(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Lto_afff6e41b5e58a2d (void) { return lto_api_version(); }\nvoid hs_bindgen_LlvmC_Raw_Lto_913620f6cf51f9a2 (char **arg1, signed int arg2) { lto_set_debug_options(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_3a2d8ee50b82cead (lto_code_gen_t arg1, char *arg2) { lto_codegen_debug_options(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_557345edbee31b43 (lto_code_gen_t arg1, char **arg2, signed int arg3) { lto_codegen_debug_options_array(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Lto_c40d7079e0b3ad0a (void) { lto_initialize_disassembler(); }\nvoid hs_bindgen_LlvmC_Raw_Lto_3a8dcbcf2d7dade2 (lto_code_gen_t arg1, lto_bool_t arg2) { lto_codegen_set_should_internalize(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_70b06c80a37cb044 (lto_code_gen_t arg1, lto_bool_t arg2) { lto_codegen_set_should_embed_uselists(arg1, arg2); }\nlto_input_t hs_bindgen_LlvmC_Raw_Lto_d5c906a4144f299b (void *arg1, size_t arg2, char *arg3) { return lto_input_create(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Lto_e0aeb9a2e17bb840 (lto_input_t arg1) { lto_input_dispose(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Lto_81b33aa81481c875 (lto_input_t arg1) { return lto_input_get_num_dependent_libraries(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Lto_9e80dbd1ac22f7e2 (lto_input_t arg1, size_t arg2, size_t *arg3) { return lto_input_get_dependent_library(arg1, arg2, arg3); }\nchar **hs_bindgen_LlvmC_Raw_Lto_a768d67809804acd (size_t *arg1) { return lto_runtime_lib_symbols_list(arg1); }\nthinlto_code_gen_t hs_bindgen_LlvmC_Raw_Lto_d76178e818dd2230 (void) { return thinlto_create_codegen(); }\nvoid hs_bindgen_LlvmC_Raw_Lto_ee90376ee94e6266 (thinlto_code_gen_t arg1) { thinlto_codegen_dispose(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Lto_c338315766c58eba (thinlto_code_gen_t arg1, char *arg2, char *arg3, signed int arg4) { thinlto_codegen_add_module(arg1, arg2, arg3, arg4); }\nvoid hs_bindgen_LlvmC_Raw_Lto_7c7f8c38bb911864 (thinlto_code_gen_t arg1) { thinlto_codegen_process(arg1); }\nunsigned int hs_bindgen_LlvmC_Raw_Lto_30c6338fdbe325c0 (thinlto_code_gen_t arg1) { return thinlto_module_get_num_objects(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Lto_b61c47b8d05bb4d7 (thinlto_code_gen_t arg1, unsigned int arg2, LTOObjectBuffer *arg3) { *arg3 = thinlto_module_get_object(arg1, arg2); }\nunsigned int hs_bindgen_LlvmC_Raw_Lto_601250fa8d6e2b23 (thinlto_code_gen_t arg1) { return thinlto_module_get_num_object_files(arg1); }\nchar *hs_bindgen_LlvmC_Raw_Lto_90f810fa51ad534d (thinlto_code_gen_t arg1, unsigned int arg2) { return thinlto_module_get_object_file(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_6551890c711637d7 (thinlto_code_gen_t arg1, lto_codegen_model arg2) { return thinlto_codegen_set_pic_model(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_a2bcfa2847ff975c (thinlto_code_gen_t arg1, char *arg2) { thinlto_codegen_set_savetemps_dir(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_71e912a2c5dbd0fe (thinlto_code_gen_t arg1, char *arg2) { thinlto_set_generated_objects_dir(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_b3bd47f256631191 (thinlto_code_gen_t arg1, char *arg2) { thinlto_codegen_set_cpu(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_de3a769f3ae35b3c (thinlto_code_gen_t arg1, lto_bool_t arg2) { thinlto_codegen_disable_codegen(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_96c1164a79b56cb0 (thinlto_code_gen_t arg1, lto_bool_t arg2) { thinlto_codegen_set_codegen_only(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_67b6eb43208d1468 (char **arg1, signed int arg2) { thinlto_debug_options(arg1, arg2); }\nlto_bool_t hs_bindgen_LlvmC_Raw_Lto_ac90e239d83e8e39 (lto_module_t arg1) { return lto_module_is_thinlto(arg1); }\nvoid hs_bindgen_LlvmC_Raw_Lto_9a04ba7bb30a0e7b (thinlto_code_gen_t arg1, char *arg2, signed int arg3) { thinlto_codegen_add_must_preserve_symbol(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Lto_75b8560045c89ec5 (thinlto_code_gen_t arg1, char *arg2, signed int arg3) { thinlto_codegen_add_cross_referenced_symbol(arg1, arg2, arg3); }\nvoid hs_bindgen_LlvmC_Raw_Lto_5cacc632a09c33f5 (thinlto_code_gen_t arg1, char *arg2) { thinlto_codegen_set_cache_dir(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_4076f261b574123c (thinlto_code_gen_t arg1, signed int arg2) { thinlto_codegen_set_cache_pruning_interval(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_079af0962576667c (thinlto_code_gen_t arg1, unsigned int arg2) { thinlto_codegen_set_final_cache_size_relative_to_available_space(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_20f8610475279b1d (thinlto_code_gen_t arg1, unsigned int arg2) { thinlto_codegen_set_cache_entry_expiration(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_279d30c7208982a4 (thinlto_code_gen_t arg1, unsigned int arg2) { thinlto_codegen_set_cache_size_bytes(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_2df9c7b298e95fb0 (thinlto_code_gen_t arg1, unsigned int arg2) { thinlto_codegen_set_cache_size_megabytes(arg1, arg2); }\nvoid hs_bindgen_LlvmC_Raw_Lto_2c226cd06059e57b (thinlto_code_gen_t arg1, unsigned int arg2) { thinlto_codegen_set_cache_size_files(arg1, arg2); }\n")

__bool_true_false_are_defined :: FC.CInt
__bool_true_false_are_defined = (1 :: FC.CInt)

newtype Bool = Bool
  { un_Bool :: FC.CBool
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

true :: FC.CInt
true = (1 :: FC.CInt)

_BITS_TIME64_H :: FC.CInt
_BITS_TIME64_H = (1 :: FC.CInt)

_BITS_TYPESIZES_H :: FC.CInt
_BITS_TYPESIZES_H = (1 :: FC.CInt)

newtype C__TIMER_T_TYPE = C__TIMER_T_TYPE
  { un_C__TIMER_T_TYPE :: F.Ptr Void
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

__OFF_T_MATCHES_OFF64_T :: FC.CInt
__OFF_T_MATCHES_OFF64_T = (1 :: FC.CInt)

__INO_T_MATCHES_INO64_T :: FC.CInt
__INO_T_MATCHES_INO64_T = (1 :: FC.CInt)

__RLIM_T_MATCHES_RLIM64_T :: FC.CInt
__RLIM_T_MATCHES_RLIM64_T = (1 :: FC.CInt)

__STATFS_MATCHES_STATFS64 :: FC.CInt
__STATFS_MATCHES_STATFS64 = (1 :: FC.CInt)

__KERNEL_OLD_TIMEVAL_MATCHES_TIMEVAL64 :: FC.CInt
__KERNEL_OLD_TIMEVAL_MATCHES_TIMEVAL64 =
  (1 :: FC.CInt)

__FD_SETSIZE :: FC.CInt
__FD_SETSIZE = (1024 :: FC.CInt)

_STDC_PREDEF_H :: FC.CInt
_STDC_PREDEF_H = (1 :: FC.CInt)

__STDC_IEC_559__ :: FC.CInt
__STDC_IEC_559__ = (1 :: FC.CInt)

__STDC_IEC_60559_BFP__ :: FC.CLong
__STDC_IEC_60559_BFP__ = (201404 :: FC.CLong)

__STDC_IEC_559_COMPLEX__ :: FC.CInt
__STDC_IEC_559_COMPLEX__ = (1 :: FC.CInt)

__STDC_IEC_60559_COMPLEX__ :: FC.CLong
__STDC_IEC_60559_COMPLEX__ = (201404 :: FC.CLong)

__STDC_ISO_10646__ :: FC.CLong
__STDC_ISO_10646__ = (201706 :: FC.CLong)

__WORDSIZE :: FC.CInt
__WORDSIZE = (64 :: FC.CInt)

__WORDSIZE_TIME64_COMPAT32 :: FC.CInt
__WORDSIZE_TIME64_COMPAT32 = (1 :: FC.CInt)

__SYSCALL_WORDSIZE :: FC.CInt
__SYSCALL_WORDSIZE = (64 :: FC.CInt)

_SYS_CDEFS_H :: FC.CInt
_SYS_CDEFS_H = (1 :: FC.CInt)

__P :: forall a0. a0 -> a0
__P = \args0 -> args0

__PMT :: forall a0. a0 -> a0
__PMT = \args0 -> args0

newtype C__Ptr_t = C__Ptr_t
  { un_C__Ptr_t :: F.Ptr Void
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

__glibc_c99_flexarr_available :: FC.CInt
__glibc_c99_flexarr_available = (1 :: FC.CInt)

__HAVE_GENERIC_SELECTION :: FC.CInt
__HAVE_GENERIC_SELECTION = (1 :: FC.CInt)

__TIMESIZE :: FC.CInt
__TIMESIZE = __WORDSIZE

__USE_TIME_BITS64 :: FC.CInt
__USE_TIME_BITS64 = (1 :: FC.CInt)

_FEATURES_H :: FC.CInt
_FEATURES_H = (1 :: FC.CInt)

__USE_ISOC11 :: FC.CInt
__USE_ISOC11 = (1 :: FC.CInt)

__USE_ISOC99 :: FC.CInt
__USE_ISOC99 = (1 :: FC.CInt)

__USE_ISOC95 :: FC.CInt
__USE_ISOC95 = (1 :: FC.CInt)

__GNU_LIBRARY__ :: FC.CInt
__GNU_LIBRARY__ = (6 :: FC.CInt)

__GLIBC__ :: FC.CInt
__GLIBC__ = (2 :: FC.CInt)

__GLIBC_MINOR__ :: FC.CInt
__GLIBC_MINOR__ = (40 :: FC.CInt)

__GLIBC_PREREQ :: forall a0 b1. (C.RelOrd FC.CInt) ((C.AddRes (C.ShiftRes a0)) b1) => (C.Add (C.ShiftRes a0)) b1 => (C.Shift a0) FC.CInt => a0 -> b1 -> FC.CInt
__GLIBC_PREREQ =
  \maj0 ->
    \min1 ->
      (>=) ((+) ((<<) __GLIBC__ (16 :: FC.CInt)) __GLIBC_MINOR__) ((+) ((<<) maj0 (16 :: FC.CInt)) min1)

_BITS_TYPES_H :: FC.CInt
_BITS_TYPES_H = (1 :: FC.CInt)

newtype C__U_char = C__U_char
  { un_C__U_char :: FC.CUChar
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U_short = C__U_short
  { un_C__U_short :: FC.CUShort
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U_int = C__U_int
  { un_C__U_int :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U_long = C__U_long
  { un_C__U_long :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int8_t = C__Int8_t
  { un_C__Int8_t :: FC.CSChar
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint8_t = C__Uint8_t
  { un_C__Uint8_t :: FC.CUChar
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int16_t = C__Int16_t
  { un_C__Int16_t :: FC.CShort
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint16_t = C__Uint16_t
  { un_C__Uint16_t :: FC.CUShort
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int32_t = C__Int32_t
  { un_C__Int32_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint32_t = C__Uint32_t
  { un_C__Uint32_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int64_t = C__Int64_t
  { un_C__Int64_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint64_t = C__Uint64_t
  { un_C__Uint64_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int_least8_t = C__Int_least8_t
  { un_C__Int_least8_t :: C__Int8_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint_least8_t = C__Uint_least8_t
  { un_C__Uint_least8_t :: C__Uint8_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int_least16_t = C__Int_least16_t
  { un_C__Int_least16_t :: C__Int16_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint_least16_t = C__Uint_least16_t
  { un_C__Uint_least16_t :: C__Uint16_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int_least32_t = C__Int_least32_t
  { un_C__Int_least32_t :: C__Int32_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint_least32_t = C__Uint_least32_t
  { un_C__Uint_least32_t :: C__Uint32_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Int_least64_t = C__Int_least64_t
  { un_C__Int_least64_t :: C__Int64_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uint_least64_t = C__Uint_least64_t
  { un_C__Uint_least64_t :: C__Uint64_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Quad_t = C__Quad_t
  { un_C__Quad_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U_quad_t = C__U_quad_t
  { un_C__U_quad_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Intmax_t = C__Intmax_t
  { un_C__Intmax_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uintmax_t = C__Uintmax_t
  { un_C__Uintmax_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__S16_TYPE = C__S16_TYPE
  { un_C__S16_TYPE :: FC.CShort
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U16_TYPE = C__U16_TYPE
  { un_C__U16_TYPE :: FC.CUShort
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__S32_TYPE = C__S32_TYPE
  { un_C__S32_TYPE :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U32_TYPE = C__U32_TYPE
  { un_C__U32_TYPE :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__SLONGWORD_TYPE = C__SLONGWORD_TYPE
  { un_C__SLONGWORD_TYPE :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__ULONGWORD_TYPE = C__ULONGWORD_TYPE
  { un_C__ULONGWORD_TYPE :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__SQUAD_TYPE = C__SQUAD_TYPE
  { un_C__SQUAD_TYPE :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__UQUAD_TYPE = C__UQUAD_TYPE
  { un_C__UQUAD_TYPE :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__SWORD_TYPE = C__SWORD_TYPE
  { un_C__SWORD_TYPE :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__UWORD_TYPE = C__UWORD_TYPE
  { un_C__UWORD_TYPE :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__SLONG32_TYPE = C__SLONG32_TYPE
  { un_C__SLONG32_TYPE :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__ULONG32_TYPE = C__ULONG32_TYPE
  { un_C__ULONG32_TYPE :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__S64_TYPE = C__S64_TYPE
  { un_C__S64_TYPE :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__U64_TYPE = C__U64_TYPE
  { un_C__U64_TYPE :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Dev_t = C__Dev_t
  { un_C__Dev_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Uid_t = C__Uid_t
  { un_C__Uid_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Gid_t = C__Gid_t
  { un_C__Gid_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Ino_t = C__Ino_t
  { un_C__Ino_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Ino64_t = C__Ino64_t
  { un_C__Ino64_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Mode_t = C__Mode_t
  { un_C__Mode_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Nlink_t = C__Nlink_t
  { un_C__Nlink_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Off_t = C__Off_t
  { un_C__Off_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Off64_t = C__Off64_t
  { un_C__Off64_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Pid_t = C__Pid_t
  { un_C__Pid_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

data C__Fsid_t = C__Fsid_t
  { __fsid_t___val :: (HsBindgen.Runtime.ConstantArray.ConstantArray 2) FC.CInt
  }
  deriving stock (Eq, Show)

instance F.Storable C__Fsid_t where

  sizeOf = \_ -> (8 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure C__Fsid_t
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          C__Fsid_t __fsid_t___val2 ->
            F.pokeByteOff ptr0 (0 :: Int) __fsid_t___val2

newtype C__Clock_t = C__Clock_t
  { un_C__Clock_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Rlim_t = C__Rlim_t
  { un_C__Rlim_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Rlim64_t = C__Rlim64_t
  { un_C__Rlim64_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Id_t = C__Id_t
  { un_C__Id_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Time_t = C__Time_t
  { un_C__Time_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Useconds_t = C__Useconds_t
  { un_C__Useconds_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Suseconds_t = C__Suseconds_t
  { un_C__Suseconds_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Suseconds64_t = C__Suseconds64_t
  { un_C__Suseconds64_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Daddr_t = C__Daddr_t
  { un_C__Daddr_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Key_t = C__Key_t
  { un_C__Key_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Clockid_t = C__Clockid_t
  { un_C__Clockid_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Timer_t = C__Timer_t
  { un_C__Timer_t :: F.Ptr Void
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype C__Blksize_t = C__Blksize_t
  { un_C__Blksize_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Blkcnt_t = C__Blkcnt_t
  { un_C__Blkcnt_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Blkcnt64_t = C__Blkcnt64_t
  { un_C__Blkcnt64_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Fsblkcnt_t = C__Fsblkcnt_t
  { un_C__Fsblkcnt_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Fsblkcnt64_t = C__Fsblkcnt64_t
  { un_C__Fsblkcnt64_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Fsfilcnt_t = C__Fsfilcnt_t
  { un_C__Fsfilcnt_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Fsfilcnt64_t = C__Fsfilcnt64_t
  { un_C__Fsfilcnt64_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Fsword_t = C__Fsword_t
  { un_C__Fsword_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Ssize_t = C__Ssize_t
  { un_C__Ssize_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Syscall_slong_t = C__Syscall_slong_t
  { un_C__Syscall_slong_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Syscall_ulong_t = C__Syscall_ulong_t
  { un_C__Syscall_ulong_t :: FC.CULong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Loff_t = C__Loff_t
  { un_C__Loff_t :: C__Off64_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Caddr_t = C__Caddr_t
  { un_C__Caddr_t :: F.Ptr FC.CChar
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

newtype C__Intptr_t = C__Intptr_t
  { un_C__Intptr_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Socklen_t = C__Socklen_t
  { un_C__Socklen_t :: FC.CUInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype C__Sig_atomic_t = C__Sig_atomic_t
  { un_C__Sig_atomic_t :: FC.CInt
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

_BITS_STDINT_INTN_H :: FC.CInt
_BITS_STDINT_INTN_H = (1 :: FC.CInt)

newtype Int8_t = Int8_t
  { un_Int8_t :: C__Int8_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Int16_t = Int16_t
  { un_Int16_t :: C__Int16_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Int32_t = Int32_t
  { un_Int32_t :: C__Int32_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Int64_t = Int64_t
  { un_Int64_t :: C__Int64_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

__timer_t_defined :: FC.CInt
__timer_t_defined = (1 :: FC.CInt)

newtype Timer_t = Timer_t
  { un_Timer_t :: C__Timer_t
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

__time_t_defined :: FC.CInt
__time_t_defined = (1 :: FC.CInt)

newtype Time_t = Time_t
  { un_Time_t :: C__Time_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

__clockid_t_defined :: FC.CInt
__clockid_t_defined = (1 :: FC.CInt)

newtype Clockid_t = Clockid_t
  { un_Clockid_t :: C__Clockid_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

_SYS_TYPES_H :: FC.CInt
_SYS_TYPES_H = (1 :: FC.CInt)

newtype Ino_t = Ino_t
  { un_Ino_t :: C__Ino_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Dev_t = Dev_t
  { un_Dev_t :: C__Dev_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Gid_t = Gid_t
  { un_Gid_t :: C__Gid_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Mode_t = Mode_t
  { un_Mode_t :: C__Mode_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Nlink_t = Nlink_t
  { un_Nlink_t :: C__Nlink_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Uid_t = Uid_t
  { un_Uid_t :: C__Uid_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Off_t = Off_t
  { un_Off_t :: C__Off_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Pid_t = Pid_t
  { un_Pid_t :: C__Pid_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Ssize_t = Ssize_t
  { un_Ssize_t :: C__Ssize_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype U_int8_t = U_int8_t
  { un_U_int8_t :: C__Uint8_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype U_int16_t = U_int16_t
  { un_U_int16_t :: C__Uint16_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype U_int32_t = U_int32_t
  { un_U_int32_t :: C__Uint32_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype U_int64_t = U_int64_t
  { un_U_int64_t :: C__Uint64_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Register_t = Register_t
  { un_Register_t :: FC.CLong
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

__BIT_TYPES_DEFINED__ :: FC.CInt
__BIT_TYPES_DEFINED__ = (1 :: FC.CInt)

newtype Blkcnt_t = Blkcnt_t
  { un_Blkcnt_t :: C__Blkcnt_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Fsblkcnt_t = Fsblkcnt_t
  { un_Fsblkcnt_t :: C__Fsblkcnt_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Fsfilcnt_t = Fsfilcnt_t
  { un_Fsfilcnt_t :: C__Fsfilcnt_t
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

newtype Lto_bool_t = Lto_bool_t
  { un_Lto_bool_t :: FC.CBool
  }
  deriving stock (Eq, Ord, Read, Show)
  deriving newtype (F.Storable, Bits.Bits, Bounded, Enum, FiniteBits, Integral, Ix.Ix, Num, Real)

lTO_API_VERSION :: FC.CInt
lTO_API_VERSION = (29 :: FC.CInt)

newtype Lto_symbol_attributes = Lto_symbol_attributes
  { un_Lto_symbol_attributes :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Lto_symbol_attributes where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Lto_symbol_attributes
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Lto_symbol_attributes un_Lto_symbol_attributes2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Lto_symbol_attributes2

instance HsBindgen.Runtime.CEnum.CEnum Lto_symbol_attributes where

  type CEnumZ Lto_symbol_attributes = FC.CUInt

  toCEnum = Lto_symbol_attributes

  fromCEnum = un_Lto_symbol_attributes

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (31, Data.List.NonEmpty.singleton "LTO_SYMBOL_ALIGNMENT_MASK")
                                                     , (128, Data.List.NonEmpty.singleton "LTO_SYMBOL_PERMISSIONS_RODATA")
                                                     , (160, Data.List.NonEmpty.singleton "LTO_SYMBOL_PERMISSIONS_CODE")
                                                     , (192, Data.List.NonEmpty.singleton "LTO_SYMBOL_PERMISSIONS_DATA")
                                                     , (224, Data.List.NonEmpty.singleton "LTO_SYMBOL_PERMISSIONS_MASK")
                                                     , (256, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_REGULAR")
                                                     , (512, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_TENTATIVE")
                                                     , (768, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_WEAK")
                                                     , (1024, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_UNDEFINED")
                                                     , (1280, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_WEAKUNDEF")
                                                     , (1792, Data.List.NonEmpty.singleton "LTO_SYMBOL_DEFINITION_MASK")
                                                     , (2048, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_INTERNAL")
                                                     , (4096, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_HIDDEN")
                                                     , (6144, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_DEFAULT")
                                                     , (8192, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_PROTECTED")
                                                     , (10240, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_DEFAULT_CAN_BE_HIDDEN")
                                                     , (14336, Data.List.NonEmpty.singleton "LTO_SYMBOL_SCOPE_MASK")
                                                     , (16384, Data.List.NonEmpty.singleton "LTO_SYMBOL_COMDAT")
                                                     , (32768, Data.List.NonEmpty.singleton "LTO_SYMBOL_ALIAS")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Lto_symbol_attributes"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Lto_symbol_attributes"

instance Show Lto_symbol_attributes where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Lto_symbol_attributes where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LTO_SYMBOL_ALIGNMENT_MASK :: Lto_symbol_attributes
pattern LTO_SYMBOL_ALIGNMENT_MASK = Lto_symbol_attributes 31

pattern LTO_SYMBOL_PERMISSIONS_MASK :: Lto_symbol_attributes
pattern LTO_SYMBOL_PERMISSIONS_MASK = Lto_symbol_attributes 224

pattern LTO_SYMBOL_PERMISSIONS_CODE :: Lto_symbol_attributes
pattern LTO_SYMBOL_PERMISSIONS_CODE = Lto_symbol_attributes 160

pattern LTO_SYMBOL_PERMISSIONS_DATA :: Lto_symbol_attributes
pattern LTO_SYMBOL_PERMISSIONS_DATA = Lto_symbol_attributes 192

pattern LTO_SYMBOL_PERMISSIONS_RODATA :: Lto_symbol_attributes
pattern LTO_SYMBOL_PERMISSIONS_RODATA = Lto_symbol_attributes 128

pattern LTO_SYMBOL_DEFINITION_MASK :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_MASK = Lto_symbol_attributes 1792

pattern LTO_SYMBOL_DEFINITION_REGULAR :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_REGULAR = Lto_symbol_attributes 256

pattern LTO_SYMBOL_DEFINITION_TENTATIVE :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_TENTATIVE = Lto_symbol_attributes 512

pattern LTO_SYMBOL_DEFINITION_WEAK :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_WEAK = Lto_symbol_attributes 768

pattern LTO_SYMBOL_DEFINITION_UNDEFINED :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_UNDEFINED = Lto_symbol_attributes 1024

pattern LTO_SYMBOL_DEFINITION_WEAKUNDEF :: Lto_symbol_attributes
pattern LTO_SYMBOL_DEFINITION_WEAKUNDEF = Lto_symbol_attributes 1280

pattern LTO_SYMBOL_SCOPE_MASK :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_MASK = Lto_symbol_attributes 14336

pattern LTO_SYMBOL_SCOPE_INTERNAL :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_INTERNAL = Lto_symbol_attributes 2048

pattern LTO_SYMBOL_SCOPE_HIDDEN :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_HIDDEN = Lto_symbol_attributes 4096

pattern LTO_SYMBOL_SCOPE_PROTECTED :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_PROTECTED = Lto_symbol_attributes 8192

pattern LTO_SYMBOL_SCOPE_DEFAULT :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_DEFAULT = Lto_symbol_attributes 6144

pattern LTO_SYMBOL_SCOPE_DEFAULT_CAN_BE_HIDDEN :: Lto_symbol_attributes
pattern LTO_SYMBOL_SCOPE_DEFAULT_CAN_BE_HIDDEN = Lto_symbol_attributes 10240

pattern LTO_SYMBOL_COMDAT :: Lto_symbol_attributes
pattern LTO_SYMBOL_COMDAT = Lto_symbol_attributes 16384

pattern LTO_SYMBOL_ALIAS :: Lto_symbol_attributes
pattern LTO_SYMBOL_ALIAS = Lto_symbol_attributes 32768

newtype Lto_debug_model = Lto_debug_model
  { un_Lto_debug_model :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Lto_debug_model where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Lto_debug_model
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Lto_debug_model un_Lto_debug_model2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Lto_debug_model2

instance HsBindgen.Runtime.CEnum.CEnum Lto_debug_model where

  type CEnumZ Lto_debug_model = FC.CUInt

  toCEnum = Lto_debug_model

  fromCEnum = un_Lto_debug_model

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "LTO_DEBUG_MODEL_NONE")
                                                     , (1, Data.List.NonEmpty.singleton "LTO_DEBUG_MODEL_DWARF")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Lto_debug_model"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Lto_debug_model"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum Lto_debug_model where

  minDeclaredValue = LTO_DEBUG_MODEL_NONE

  maxDeclaredValue = LTO_DEBUG_MODEL_DWARF

instance Show Lto_debug_model where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Lto_debug_model where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LTO_DEBUG_MODEL_NONE :: Lto_debug_model
pattern LTO_DEBUG_MODEL_NONE = Lto_debug_model 0

pattern LTO_DEBUG_MODEL_DWARF :: Lto_debug_model
pattern LTO_DEBUG_MODEL_DWARF = Lto_debug_model 1

newtype Lto_codegen_model = Lto_codegen_model
  { un_Lto_codegen_model :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Lto_codegen_model where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Lto_codegen_model
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Lto_codegen_model un_Lto_codegen_model2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Lto_codegen_model2

instance HsBindgen.Runtime.CEnum.CEnum Lto_codegen_model where

  type CEnumZ Lto_codegen_model = FC.CUInt

  toCEnum = Lto_codegen_model

  fromCEnum = un_Lto_codegen_model

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "LTO_CODEGEN_PIC_MODEL_STATIC")
                                                     , (1, Data.List.NonEmpty.singleton "LTO_CODEGEN_PIC_MODEL_DYNAMIC")
                                                     , (2, Data.List.NonEmpty.singleton "LTO_CODEGEN_PIC_MODEL_DYNAMIC_NO_PIC")
                                                     , (3, Data.List.NonEmpty.singleton "LTO_CODEGEN_PIC_MODEL_DEFAULT")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Lto_codegen_model"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Lto_codegen_model"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum Lto_codegen_model where

  minDeclaredValue = LTO_CODEGEN_PIC_MODEL_STATIC

  maxDeclaredValue = LTO_CODEGEN_PIC_MODEL_DEFAULT

instance Show Lto_codegen_model where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Lto_codegen_model where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LTO_CODEGEN_PIC_MODEL_STATIC :: Lto_codegen_model
pattern LTO_CODEGEN_PIC_MODEL_STATIC = Lto_codegen_model 0

pattern LTO_CODEGEN_PIC_MODEL_DYNAMIC :: Lto_codegen_model
pattern LTO_CODEGEN_PIC_MODEL_DYNAMIC = Lto_codegen_model 1

pattern LTO_CODEGEN_PIC_MODEL_DYNAMIC_NO_PIC :: Lto_codegen_model
pattern LTO_CODEGEN_PIC_MODEL_DYNAMIC_NO_PIC = Lto_codegen_model 2

pattern LTO_CODEGEN_PIC_MODEL_DEFAULT :: Lto_codegen_model
pattern LTO_CODEGEN_PIC_MODEL_DEFAULT = Lto_codegen_model 3

data OpaqueLTOModule

newtype Lto_module_t = Lto_module_t
  { un_Lto_module_t :: F.Ptr OpaqueLTOModule
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueLTOCodeGenerator

newtype Lto_code_gen_t = Lto_code_gen_t
  { un_Lto_code_gen_t :: F.Ptr OpaqueLTOCodeGenerator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

data OpaqueThinLTOCodeGenerator

newtype Thinlto_code_gen_t = Thinlto_code_gen_t
  { un_Thinlto_code_gen_t :: F.Ptr OpaqueThinLTOCodeGenerator
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_47100290d68e0a67" lto_get_version
  :: IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_fd4f5a7fefad7964" lto_get_error_message
  :: IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_c4068f901f2d522e" lto_module_is_object_file
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e83f05229dd75926" lto_module_is_object_file_for_target
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @target_triple_prefix@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_a1a882b7d18c5d55" lto_module_has_objc_category
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_1cb60185a13472e9" lto_module_is_object_file_in_memory
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_786aeb363826a839" lto_module_is_object_file_in_memory_for_target
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @target_triple_prefix@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_dd33b203ed8d873c" lto_module_create
  :: F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_6c5f580546d96ded" lto_module_create_from_memory
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_337bd587befeff33" lto_module_create_from_memory_with_path
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_3dce1b2df5c57e4f" lto_module_create_in_local_context
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_628188f55144d20b" lto_module_create_in_codegen_context
  :: F.Ptr Void
     {- ^ __from C:__ @mem@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_9bedf167fb4beb9b" lto_module_create_from_fd
  :: FC.CInt
     {- ^ __from C:__ @fd@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @file_size@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_d1ece35eeb475a53" lto_module_create_from_fd_at_offset
  :: FC.CInt
     {- ^ __from C:__ @fd@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @file_size@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @map_size@ -}
  -> Off_t
     {- ^ __from C:__ @offset@ -}
  -> IO Lto_module_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_304ff46b4d545a99" lto_module_dispose
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_62a25fce40b551a2" lto_module_get_target_triple
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_9277186bf27a4cd0" lto_module_set_target_triple
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @triple@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_f63deea05d359be4" lto_module_get_num_symbols
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_b1875f816302c03a" lto_module_get_symbol_name
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_327ec77f75227a4a" lto_module_get_symbol_attribute
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO Lto_symbol_attributes

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_6ee224fced7a5fb8" lto_module_get_linkeropts
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_885699f624e484fb" lto_module_get_macho_cputype
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @out_cputype@ -}
  -> F.Ptr FC.CUInt
     {- ^ __from C:__ @out_cpusubtype@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e27775a2fb0eb169" lto_module_has_ctor_dtor
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO Lto_bool_t

newtype Lto_codegen_diagnostic_severity_t = Lto_codegen_diagnostic_severity_t
  { un_Lto_codegen_diagnostic_severity_t :: FC.CUInt
  }
  deriving stock (Eq, Ord)

instance F.Storable Lto_codegen_diagnostic_severity_t where

  sizeOf = \_ -> (4 :: Int)

  alignment = \_ -> (4 :: Int)

  peek =
    \ptr0 ->
          pure Lto_codegen_diagnostic_severity_t
      <*> F.peekByteOff ptr0 (0 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          Lto_codegen_diagnostic_severity_t un_Lto_codegen_diagnostic_severity_t2 ->
            F.pokeByteOff ptr0 (0 :: Int) un_Lto_codegen_diagnostic_severity_t2

instance HsBindgen.Runtime.CEnum.CEnum Lto_codegen_diagnostic_severity_t where

  type CEnumZ Lto_codegen_diagnostic_severity_t =
    FC.CUInt

  toCEnum = Lto_codegen_diagnostic_severity_t

  fromCEnum = un_Lto_codegen_diagnostic_severity_t

  declaredValues =
    \_ ->
      HsBindgen.Runtime.CEnum.declaredValuesFromList [ (0, Data.List.NonEmpty.singleton "LTO_DS_ERROR")
                                                     , (1, Data.List.NonEmpty.singleton "LTO_DS_WARNING")
                                                     , (2, Data.List.NonEmpty.singleton "LTO_DS_NOTE")
                                                     , (3, Data.List.NonEmpty.singleton "LTO_DS_REMARK")
                                                     ]

  showsUndeclared =
    HsBindgen.Runtime.CEnum.showsWrappedUndeclared "Lto_codegen_diagnostic_severity_t"

  readPrecUndeclared =
    HsBindgen.Runtime.CEnum.readPrecWrappedUndeclared "Lto_codegen_diagnostic_severity_t"

  isDeclared = HsBindgen.Runtime.CEnum.seqIsDeclared

  mkDeclared = HsBindgen.Runtime.CEnum.seqMkDeclared

instance HsBindgen.Runtime.CEnum.SequentialCEnum Lto_codegen_diagnostic_severity_t where

  minDeclaredValue = LTO_DS_ERROR

  maxDeclaredValue = LTO_DS_REMARK

instance Show Lto_codegen_diagnostic_severity_t where

  showsPrec = HsBindgen.Runtime.CEnum.showsCEnum

instance Read Lto_codegen_diagnostic_severity_t where

  readPrec = HsBindgen.Runtime.CEnum.readPrecCEnum

  readList = Text.Read.readListDefault

  readListPrec = Text.Read.readListPrecDefault

pattern LTO_DS_ERROR :: Lto_codegen_diagnostic_severity_t
pattern LTO_DS_ERROR = Lto_codegen_diagnostic_severity_t 0

pattern LTO_DS_WARNING :: Lto_codegen_diagnostic_severity_t
pattern LTO_DS_WARNING = Lto_codegen_diagnostic_severity_t 1

pattern LTO_DS_REMARK :: Lto_codegen_diagnostic_severity_t
pattern LTO_DS_REMARK = Lto_codegen_diagnostic_severity_t 3

pattern LTO_DS_NOTE :: Lto_codegen_diagnostic_severity_t
pattern LTO_DS_NOTE = Lto_codegen_diagnostic_severity_t 2

newtype Lto_diagnostic_handler_t = Lto_diagnostic_handler_t
  { un_Lto_diagnostic_handler_t :: F.FunPtr (Lto_codegen_diagnostic_severity_t -> (F.Ptr FC.CChar) -> (F.Ptr Void) -> IO ())
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e7ee7b1955f1ae16" lto_codegen_set_diagnostic_handler
  :: Lto_code_gen_t
  -> Lto_diagnostic_handler_t
  -> F.Ptr Void
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_acc06fc19f554e37" lto_codegen_create
  :: IO Lto_code_gen_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_1047db82a2fa4d5a" lto_codegen_create_in_local_context
  :: IO Lto_code_gen_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_dc6171a35cbc1334" lto_codegen_dispose
  :: Lto_code_gen_t
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_6a18f3fff57435d1" lto_codegen_add_module
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e05d3db925e09ee5" lto_codegen_set_module
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_3d73f232c1990772" lto_codegen_set_debug_model
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_debug_model
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_078403b3e69f87fc" lto_codegen_set_pic_model
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_codegen_model
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_d0dc7445379e90f8" lto_codegen_set_cpu
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cpu@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_1a57acb6d97c2bed" lto_codegen_set_assembler_path
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_0238791b1e520adf" lto_codegen_set_assembler_args
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @args@ -}
  -> FC.CInt
     {- ^ __from C:__ @nargs@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_94e76935bc2aac78" lto_codegen_add_must_preserve_symbol
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @symbol@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_890504289993b5d1" lto_codegen_write_merged_modules
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_212c83986d069b0e" lto_codegen_compile
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e75f21f0a9ddadd4" lto_codegen_compile_to_file
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @name@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_f09a979b870f94e5" lto_codegen_optimize
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_c10c1cc6c03b90a3" lto_codegen_compile_optimized
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @length@ -}
  -> IO (F.Ptr Void)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_afff6e41b5e58a2d" lto_api_version
  :: IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_913620f6cf51f9a2" lto_set_debug_options
  :: F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @options@ -}
  -> FC.CInt
     {- ^ __from C:__ @number@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_3a2d8ee50b82cead" lto_codegen_debug_options
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_557345edbee31b43" lto_codegen_debug_options_array
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr (F.Ptr FC.CChar)
  -> FC.CInt
     {- ^ __from C:__ @number@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_c40d7079e0b3ad0a" lto_initialize_disassembler
  :: IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_3a8dcbcf2d7dade2" lto_codegen_set_should_internalize
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_bool_t
     {- ^ __from C:__ @shouldInternalize@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_70b06c80a37cb044" lto_codegen_set_should_embed_uselists
  :: Lto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_bool_t
     {- ^ __from C:__ @shouldEmbedUselists@ -}
  -> IO ()

data OpaqueLTOInput

newtype Lto_input_t = Lto_input_t
  { un_Lto_input_t :: F.Ptr OpaqueLTOInput
  }
  deriving stock (Eq, Ord, Show)
  deriving newtype (F.Storable)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_d5c906a4144f299b" lto_input_create
  :: F.Ptr Void
     {- ^ __from C:__ @buffer@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @buffer_size@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @path@ -}
  -> IO Lto_input_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_e0aeb9a2e17bb840" lto_input_dispose
  :: Lto_input_t
     {- ^ __from C:__ @input@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_81b33aa81481c875" lto_input_get_num_dependent_libraries
  :: Lto_input_t
     {- ^ __from C:__ @input@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_9e80dbd1ac22f7e2" lto_input_get_dependent_library
  :: Lto_input_t
     {- ^ __from C:__ @input@ -}
  -> HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @index@ -}
  -> F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @size@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_a768d67809804acd" lto_runtime_lib_symbols_list
  :: F.Ptr HsBindgen.Runtime.Prelude.CSize
     {- ^ __from C:__ @size@ -}
  -> IO (F.Ptr (F.Ptr FC.CChar))

data LTOObjectBuffer = LTOObjectBuffer
  { lTOObjectBuffer_Buffer :: F.Ptr FC.CChar
  , lTOObjectBuffer_Size :: HsBindgen.Runtime.Prelude.CSize
  }
  deriving stock (Eq, Show)

instance F.Storable LTOObjectBuffer where

  sizeOf = \_ -> (16 :: Int)

  alignment = \_ -> (8 :: Int)

  peek =
    \ptr0 ->
          pure LTOObjectBuffer
      <*> F.peekByteOff ptr0 (0 :: Int)
      <*> F.peekByteOff ptr0 (8 :: Int)

  poke =
    \ptr0 ->
      \s1 ->
        case s1 of
          LTOObjectBuffer lTOObjectBuffer_Buffer2 lTOObjectBuffer_Size3 ->
               F.pokeByteOff ptr0 (0 :: Int) lTOObjectBuffer_Buffer2
            >> F.pokeByteOff ptr0 (8 :: Int) lTOObjectBuffer_Size3

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_d76178e818dd2230" thinlto_create_codegen
  :: IO Thinlto_code_gen_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_ee90376ee94e6266" thinlto_codegen_dispose
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_c338315766c58eba" thinlto_codegen_add_module
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @identifier@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @data'@ -}
  -> FC.CInt
     {- ^ __from C:__ @length@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_7c7f8c38bb911864" thinlto_codegen_process
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_30c6338fdbe325c0" thinlto_module_get_num_objects
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_b61c47b8d05bb4d7" thinlto_module_get_object_wrapper
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> F.Ptr LTOObjectBuffer
  -> IO ()

thinlto_module_get_object :: Thinlto_code_gen_t -> FC.CUInt -> IO LTOObjectBuffer
thinlto_module_get_object =
  \x0 ->
    \x1 ->
      HsBindgen.Runtime.CAPI.allocaAndPeek (\z2 ->
                                              thinlto_module_get_object_wrapper x0 x1 z2)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_601250fa8d6e2b23" thinlto_module_get_num_object_files
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> IO FC.CUInt

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_90f810fa51ad534d" thinlto_module_get_object_file
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @index@ -}
  -> IO (F.Ptr FC.CChar)

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_6551890c711637d7" thinlto_codegen_set_pic_model
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_codegen_model
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_a2bcfa2847ff975c" thinlto_codegen_set_savetemps_dir
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @save_temps_dir@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_71e912a2c5dbd0fe" thinlto_set_generated_objects_dir
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @save_temps_dir@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_b3bd47f256631191" thinlto_codegen_set_cpu
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cpu@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_de3a769f3ae35b3c" thinlto_codegen_disable_codegen
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_bool_t
     {- ^ __from C:__ @disable@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_96c1164a79b56cb0" thinlto_codegen_set_codegen_only
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> Lto_bool_t
     {- ^ __from C:__ @codegen_only@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_67b6eb43208d1468" thinlto_debug_options
  :: F.Ptr (F.Ptr FC.CChar)
     {- ^ __from C:__ @options@ -}
  -> FC.CInt
     {- ^ __from C:__ @number@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_ac90e239d83e8e39" lto_module_is_thinlto
  :: Lto_module_t
     {- ^ __from C:__ @mod@ -}
  -> IO Lto_bool_t

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_9a04ba7bb30a0e7b" thinlto_codegen_add_must_preserve_symbol
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> FC.CInt
     {- ^ __from C:__ @length@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_75b8560045c89ec5" thinlto_codegen_add_cross_referenced_symbol
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @name@ -}
  -> FC.CInt
     {- ^ __from C:__ @length@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_5cacc632a09c33f5" thinlto_codegen_set_cache_dir
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> F.Ptr FC.CChar
     {- ^ __from C:__ @cache_dir@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_4076f261b574123c" thinlto_codegen_set_cache_pruning_interval
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CInt
     {- ^ __from C:__ @interval@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_079af0962576667c" thinlto_codegen_set_final_cache_size_relative_to_available_space
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @percentage@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_20f8610475279b1d" thinlto_codegen_set_cache_entry_expiration
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @expiration@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_279d30c7208982a4" thinlto_codegen_set_cache_size_bytes
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @max_size_bytes@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_2df9c7b298e95fb0" thinlto_codegen_set_cache_size_megabytes
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @max_size_megabytes@ -}
  -> IO ()

foreign import ccall safe "hs_bindgen_LlvmC_Raw_Lto_2c226cd06059e57b" thinlto_codegen_set_cache_size_files
  :: Thinlto_code_gen_t
     {- ^ __from C:__ @cg@ -}
  -> FC.CUInt
     {- ^ __from C:__ @max_size_files@ -}
  -> IO ()
