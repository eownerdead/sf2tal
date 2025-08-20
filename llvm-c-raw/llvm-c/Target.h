#ifndef LLVM_C_TARGET_H
#define LLVM_C_TARGET_H

#include "llvm-c/ExternC.h"
#include "llvm-c/Types.h"

# 1 "./Target.h"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 400 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "./Target.h" 2
# 26 "./Target.h"
LLVM_C_EXTERN_C_BEGIN
# 35 "./Target.h"
enum LLVMByteOrdering { LLVMBigEndian, LLVMLittleEndian };

typedef struct LLVMOpaqueTargetData *LLVMTargetDataRef;
typedef struct LLVMOpaqueTargetLibraryInfotData *LLVMTargetLibraryInfoRef;




# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
void LLVMInitializeAArch64TargetInfo(void);
void LLVMInitializeAMDGPUTargetInfo(void);
void LLVMInitializeARMTargetInfo(void);
void LLVMInitializeAVRTargetInfo(void);
void LLVMInitializeBPFTargetInfo(void);
void LLVMInitializeHexagonTargetInfo(void);
void LLVMInitializeLanaiTargetInfo(void);
void LLVMInitializeLoongArchTargetInfo(void);
void LLVMInitializeMipsTargetInfo(void);
void LLVMInitializeMSP430TargetInfo(void);
void LLVMInitializeNVPTXTargetInfo(void);
void LLVMInitializePowerPCTargetInfo(void);
void LLVMInitializeRISCVTargetInfo(void);
void LLVMInitializeSparcTargetInfo(void);
void LLVMInitializeSystemZTargetInfo(void);
void LLVMInitializeVETargetInfo(void);
void LLVMInitializeWebAssemblyTargetInfo(void);
void LLVMInitializeX86TargetInfo(void);
void LLVMInitializeXCoreTargetInfo(void);
# 44 "./Target.h" 2



# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
void LLVMInitializeAArch64Target(void);
void LLVMInitializeAMDGPUTarget(void);
void LLVMInitializeARMTarget(void);
void LLVMInitializeAVRTarget(void);
void LLVMInitializeBPFTarget(void);
void LLVMInitializeHexagonTarget(void);
void LLVMInitializeLanaiTarget(void);
void LLVMInitializeLoongArchTarget(void);
void LLVMInitializeMipsTarget(void);
void LLVMInitializeMSP430Target(void);
void LLVMInitializeNVPTXTarget(void);
void LLVMInitializePowerPCTarget(void);
void LLVMInitializeRISCVTarget(void);
void LLVMInitializeSparcTarget(void);
void LLVMInitializeSystemZTarget(void);
void LLVMInitializeVETarget(void);
void LLVMInitializeWebAssemblyTarget(void);
void LLVMInitializeX86Target(void);
void LLVMInitializeXCoreTarget(void);
# 48 "./Target.h" 2



# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
void LLVMInitializeAArch64TargetMC(void);
void LLVMInitializeAMDGPUTargetMC(void);
void LLVMInitializeARMTargetMC(void);
void LLVMInitializeAVRTargetMC(void);
void LLVMInitializeBPFTargetMC(void);
void LLVMInitializeHexagonTargetMC(void);
void LLVMInitializeLanaiTargetMC(void);
void LLVMInitializeLoongArchTargetMC(void);
void LLVMInitializeMipsTargetMC(void);
void LLVMInitializeMSP430TargetMC(void);
void LLVMInitializeNVPTXTargetMC(void);
void LLVMInitializePowerPCTargetMC(void);
void LLVMInitializeRISCVTargetMC(void);
void LLVMInitializeSparcTargetMC(void);
void LLVMInitializeSystemZTargetMC(void);
void LLVMInitializeVETargetMC(void);
void LLVMInitializeWebAssemblyTargetMC(void);
void LLVMInitializeX86TargetMC(void);
void LLVMInitializeXCoreTargetMC(void);
# 52 "./Target.h" 2





# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmPrinters.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmPrinters.def" 3
void LLVMInitializeAArch64AsmPrinter(void);
void LLVMInitializeAMDGPUAsmPrinter(void);
void LLVMInitializeARMAsmPrinter(void);
void LLVMInitializeAVRAsmPrinter(void);
void LLVMInitializeBPFAsmPrinter(void);
void LLVMInitializeHexagonAsmPrinter(void);
void LLVMInitializeLanaiAsmPrinter(void);
void LLVMInitializeLoongArchAsmPrinter(void);
void LLVMInitializeMipsAsmPrinter(void);
void LLVMInitializeMSP430AsmPrinter(void);
void LLVMInitializeNVPTXAsmPrinter(void);
void LLVMInitializePowerPCAsmPrinter(void);
void LLVMInitializeRISCVAsmPrinter(void);
void LLVMInitializeSparcAsmPrinter(void);
void LLVMInitializeSystemZAsmPrinter(void);
void LLVMInitializeVEAsmPrinter(void);
void LLVMInitializeWebAssemblyAsmPrinter(void);
void LLVMInitializeX86AsmPrinter(void);
void LLVMInitializeXCoreAsmPrinter(void);
# 58 "./Target.h" 2





# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmParsers.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmParsers.def" 3
void LLVMInitializeAArch64AsmParser(void);
void LLVMInitializeAMDGPUAsmParser(void);
void LLVMInitializeARMAsmParser(void);
void LLVMInitializeAVRAsmParser(void);
void LLVMInitializeBPFAsmParser(void);
void LLVMInitializeHexagonAsmParser(void);
void LLVMInitializeLanaiAsmParser(void);
void LLVMInitializeLoongArchAsmParser(void);
void LLVMInitializeMipsAsmParser(void);
void LLVMInitializeMSP430AsmParser(void);
void LLVMInitializePowerPCAsmParser(void);
void LLVMInitializeRISCVAsmParser(void);
void LLVMInitializeSparcAsmParser(void);
void LLVMInitializeSystemZAsmParser(void);
void LLVMInitializeVEAsmParser(void);
void LLVMInitializeWebAssemblyAsmParser(void);
void LLVMInitializeX86AsmParser(void);
# 64 "./Target.h" 2





# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Disassemblers.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Disassemblers.def" 3
void LLVMInitializeAArch64Disassembler(void);
void LLVMInitializeAMDGPUDisassembler(void);
void LLVMInitializeARMDisassembler(void);
void LLVMInitializeAVRDisassembler(void);
void LLVMInitializeBPFDisassembler(void);
void LLVMInitializeHexagonDisassembler(void);
void LLVMInitializeLanaiDisassembler(void);
void LLVMInitializeLoongArchDisassembler(void);
void LLVMInitializeMipsDisassembler(void);
void LLVMInitializeMSP430Disassembler(void);
void LLVMInitializePowerPCDisassembler(void);
void LLVMInitializeRISCVDisassembler(void);
void LLVMInitializeSparcDisassembler(void);
void LLVMInitializeSystemZDisassembler(void);
void LLVMInitializeVEDisassembler(void);
void LLVMInitializeWebAssemblyDisassembler(void);
void LLVMInitializeX86Disassembler(void);
void LLVMInitializeXCoreDisassembler(void);
# 70 "./Target.h" 2





static inline void LLVMInitializeAllTargetInfos(void) {

# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
LLVMInitializeAArch64TargetInfo();
LLVMInitializeAMDGPUTargetInfo();
LLVMInitializeARMTargetInfo();
LLVMInitializeAVRTargetInfo();
LLVMInitializeBPFTargetInfo();
LLVMInitializeHexagonTargetInfo();
LLVMInitializeLanaiTargetInfo();
LLVMInitializeLoongArchTargetInfo();
LLVMInitializeMipsTargetInfo();
LLVMInitializeMSP430TargetInfo();
LLVMInitializeNVPTXTargetInfo();
LLVMInitializePowerPCTargetInfo();
LLVMInitializeRISCVTargetInfo();
LLVMInitializeSparcTargetInfo();
LLVMInitializeSystemZTargetInfo();
LLVMInitializeVETargetInfo();
LLVMInitializeWebAssemblyTargetInfo();
LLVMInitializeX86TargetInfo();
LLVMInitializeXCoreTargetInfo();
# 78 "./Target.h" 2

}




static inline void LLVMInitializeAllTargets(void) {

# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
LLVMInitializeAArch64Target();
LLVMInitializeAMDGPUTarget();
LLVMInitializeARMTarget();
LLVMInitializeAVRTarget();
LLVMInitializeBPFTarget();
LLVMInitializeHexagonTarget();
LLVMInitializeLanaiTarget();
LLVMInitializeLoongArchTarget();
LLVMInitializeMipsTarget();
LLVMInitializeMSP430Target();
LLVMInitializeNVPTXTarget();
LLVMInitializePowerPCTarget();
LLVMInitializeRISCVTarget();
LLVMInitializeSparcTarget();
LLVMInitializeSystemZTarget();
LLVMInitializeVETarget();
LLVMInitializeWebAssemblyTarget();
LLVMInitializeX86Target();
LLVMInitializeXCoreTarget();
# 87 "./Target.h" 2

}




static inline void LLVMInitializeAllTargetMCs(void) {

# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 1 3
# 26 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Targets.def" 3
LLVMInitializeAArch64TargetMC();
LLVMInitializeAMDGPUTargetMC();
LLVMInitializeARMTargetMC();
LLVMInitializeAVRTargetMC();
LLVMInitializeBPFTargetMC();
LLVMInitializeHexagonTargetMC();
LLVMInitializeLanaiTargetMC();
LLVMInitializeLoongArchTargetMC();
LLVMInitializeMipsTargetMC();
LLVMInitializeMSP430TargetMC();
LLVMInitializeNVPTXTargetMC();
LLVMInitializePowerPCTargetMC();
LLVMInitializeRISCVTargetMC();
LLVMInitializeSparcTargetMC();
LLVMInitializeSystemZTargetMC();
LLVMInitializeVETargetMC();
LLVMInitializeWebAssemblyTargetMC();
LLVMInitializeX86TargetMC();
LLVMInitializeXCoreTargetMC();
# 96 "./Target.h" 2

}




static inline void LLVMInitializeAllAsmPrinters(void) {

# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmPrinters.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmPrinters.def" 3
LLVMInitializeAArch64AsmPrinter();
LLVMInitializeAMDGPUAsmPrinter();
LLVMInitializeARMAsmPrinter();
LLVMInitializeAVRAsmPrinter();
LLVMInitializeBPFAsmPrinter();
LLVMInitializeHexagonAsmPrinter();
LLVMInitializeLanaiAsmPrinter();
LLVMInitializeLoongArchAsmPrinter();
LLVMInitializeMipsAsmPrinter();
LLVMInitializeMSP430AsmPrinter();
LLVMInitializeNVPTXAsmPrinter();
LLVMInitializePowerPCAsmPrinter();
LLVMInitializeRISCVAsmPrinter();
LLVMInitializeSparcAsmPrinter();
LLVMInitializeSystemZAsmPrinter();
LLVMInitializeVEAsmPrinter();
LLVMInitializeWebAssemblyAsmPrinter();
LLVMInitializeX86AsmPrinter();
LLVMInitializeXCoreAsmPrinter();
# 105 "./Target.h" 2

}




static inline void LLVMInitializeAllAsmParsers(void) {

# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmParsers.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/AsmParsers.def" 3
LLVMInitializeAArch64AsmParser();
LLVMInitializeAMDGPUAsmParser();
LLVMInitializeARMAsmParser();
LLVMInitializeAVRAsmParser();
LLVMInitializeBPFAsmParser();
LLVMInitializeHexagonAsmParser();
LLVMInitializeLanaiAsmParser();
LLVMInitializeLoongArchAsmParser();
LLVMInitializeMipsAsmParser();
LLVMInitializeMSP430AsmParser();
LLVMInitializePowerPCAsmParser();
LLVMInitializeRISCVAsmParser();
LLVMInitializeSparcAsmParser();
LLVMInitializeSystemZAsmParser();
LLVMInitializeVEAsmParser();
LLVMInitializeWebAssemblyAsmParser();
LLVMInitializeX86AsmParser();
# 114 "./Target.h" 2

}




static inline void LLVMInitializeAllDisassemblers(void) {


# 1 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Disassemblers.def" 1 3
# 27 "/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include/llvm/Config/Disassemblers.def" 3
LLVMInitializeAArch64Disassembler();
LLVMInitializeAMDGPUDisassembler();
LLVMInitializeARMDisassembler();
LLVMInitializeAVRDisassembler();
LLVMInitializeBPFDisassembler();
LLVMInitializeHexagonDisassembler();
LLVMInitializeLanaiDisassembler();
LLVMInitializeLoongArchDisassembler();
LLVMInitializeMipsDisassembler();
LLVMInitializeMSP430Disassembler();
LLVMInitializePowerPCDisassembler();
LLVMInitializeRISCVDisassembler();
LLVMInitializeSparcDisassembler();
LLVMInitializeSystemZDisassembler();
LLVMInitializeVEDisassembler();
LLVMInitializeWebAssemblyDisassembler();
LLVMInitializeX86Disassembler();
LLVMInitializeXCoreDisassembler();
# 124 "./Target.h" 2

}




static inline LLVMBool LLVMInitializeNativeTarget(void) {







  return 1;

}




static inline LLVMBool LLVMInitializeNativeAsmParser(void) {




  return 1;

}




static inline LLVMBool LLVMInitializeNativeAsmPrinter(void) {




  return 1;

}




static inline LLVMBool LLVMInitializeNativeDisassembler(void) {




  return 1;

}
# 185 "./Target.h"
LLVMTargetDataRef LLVMGetModuleDataLayout(LLVMModuleRef M);






void LLVMSetModuleDataLayout(LLVMModuleRef M, LLVMTargetDataRef DL);



LLVMTargetDataRef LLVMCreateTargetData(const char *StringRep);



void LLVMDisposeTargetData(LLVMTargetDataRef TD);




void LLVMAddTargetLibraryInfo(LLVMTargetLibraryInfoRef TLI,
                              LLVMPassManagerRef PM);




char *LLVMCopyStringRepOfTargetData(LLVMTargetDataRef TD);




enum LLVMByteOrdering LLVMByteOrder(LLVMTargetDataRef TD);



unsigned LLVMPointerSize(LLVMTargetDataRef TD);




unsigned LLVMPointerSizeForAS(LLVMTargetDataRef TD, unsigned AS);



LLVMTypeRef LLVMIntPtrType(LLVMTargetDataRef TD);




LLVMTypeRef LLVMIntPtrTypeForAS(LLVMTargetDataRef TD, unsigned AS);



LLVMTypeRef LLVMIntPtrTypeInContext(LLVMContextRef C, LLVMTargetDataRef TD);




LLVMTypeRef LLVMIntPtrTypeForASInContext(LLVMContextRef C, LLVMTargetDataRef TD,
                                         unsigned AS);



unsigned long long LLVMSizeOfTypeInBits(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned long long LLVMStoreSizeOfType(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned long long LLVMABISizeOfType(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned LLVMABIAlignmentOfType(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned LLVMCallFrameAlignmentOfType(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned LLVMPreferredAlignmentOfType(LLVMTargetDataRef TD, LLVMTypeRef Ty);



unsigned LLVMPreferredAlignmentOfGlobal(LLVMTargetDataRef TD,
                                        LLVMValueRef GlobalVar);



unsigned LLVMElementAtOffset(LLVMTargetDataRef TD, LLVMTypeRef StructTy,
                             unsigned long long Offset);



unsigned long long LLVMOffsetOfElement(LLVMTargetDataRef TD,
                                       LLVMTypeRef StructTy, unsigned Element);





LLVM_C_EXTERN_C_END

#endif
