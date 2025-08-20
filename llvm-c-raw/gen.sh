#!/usr/bin/env bash

set -xe

HS_BINDGEN_CLI=~/src/hs-bindgen/dist-newstyle/build/x86_64-linux/ghc-9.8.4/hs-bindgen-0.1.0/x/hs-bindgen-cli/build/hs-bindgen-cli/hs-bindgen-cli

export C_INCLUDE_PATH="$PWD:/nix/store/bw1i8r1ilp79xyybr2n633aq3jj1wrrd-llvm-19.1.7-dev/include"


gen() {
    name=$1
    $HS_BINDGEN_CLI preprocess \
	-I . \
        --module "LlvmC.Raw.${name^}" \
	--output "src/LlvmC/Raw/${name^}.hs" \
	--gen-binding-spec "bindings/$name.yaml" \
	--strip-prefix "LLVM" \
	--unique-id "LlvmC_Raw_${name^}" \
	${@:2} \
	"llvm-c/$name.h"
}

gen DataTypes
gen ErrorHandling
gen Types
gen Analysis \
    --external-binding-spec bindings/Types.yaml
gen BitReader \
    --external-binding-spec bindings/Types.yaml
gen BitWriter \
    --external-binding-spec bindings/Types.yaml
gen Comdat \
    --external-binding-spec bindings/Types.yaml
gen Core \
    --external-binding-spec bindings/DataTypes.yaml \
    --external-binding-spec bindings/Types.yaml \
    --enable-program-slicing
gen DebugInfo \
    --external-binding-spec bindings/DataTypes.yaml \
    --external-binding-spec bindings/Types.yaml
gen DisassemblerTypes
gen Disassembler \
    --external-binding-spec bindings/DisassemblerTypes.yaml
gen Error
gen ErrorHandling
gen IRReader \
    --external-binding-spec bindings/Types.yaml
gen Linker \
    --external-binding-spec bindings/Types.yaml
gen lto --select-all --parse-all
gen Object \
    --external-binding-spec bindings/DataTypes.yaml \
    --external-binding-spec bindings/Types.yaml
gen Remarks \
    --external-binding-spec bindings/Types.yaml
gen Support \
    --external-binding-spec bindings/Types.yaml
gen Target \
    --external-binding-spec bindings/Types.yaml
gen TargetMachine \
    --external-binding-spec bindings/Target.yaml \
    --external-binding-spec bindings/Types.yaml
gen ExecutionEngine \
    --external-binding-spec bindings/Target.yaml \
    --external-binding-spec bindings/TargetMachine.yaml \
    --external-binding-spec bindings/Types.yaml
gen Orc \
    --external-binding-spec bindings/Error.yaml \
    --external-binding-spec bindings/TargetMachine.yaml \
    --external-binding-spec bindings/Types.yaml
gen OrcEE \
    --external-binding-spec bindings/Error.yaml \
    --external-binding-spec bindings/ExecutionEngine.yaml \
    --external-binding-spec bindings/Orc.yaml \
    --external-binding-spec bindings/TargetMachine.yaml \
    --external-binding-spec bindings/Types.yaml
gen LLJIT \
    --external-binding-spec bindings/Error.yaml \
    --external-binding-spec bindings/Orc.yaml \
    --external-binding-spec bindings/TargetMachine.yaml \
    --external-binding-spec bindings/Types.yaml
gen LLJITUtils \
    --external-binding-spec bindings/LLJIT.yaml \
    --external-binding-spec bindings/Error.yaml
