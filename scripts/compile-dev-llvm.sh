#!/bin/bash

cmake -S llvm -G Ninja -B build \
  -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_COMPILER=clang++ \
  -DCMAKE_C_COMPILER=clang \
  -DBUILD_SHARED_LIBS=ON \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DLLVM_ENABLE_PROJECTS="llvm;clang" \
  -DLLVM_TARGETS_TO_BUILD="X86;AArch64;RISCV" \
  -DLLVM_USE_LINKER=lld \
  -DLLVM_BUILD_INSTRUMENTED_COVERAGE=ON \
  -DLLVM_CODE_COVERAGE_TARGETS="llvm-mca;llvm-mc" 

# llvm-cov & llvm-profdata for coverage test
# Run your llc commands and use llvm/utils/prepare-code-coverage-artifact.py to get the html report.