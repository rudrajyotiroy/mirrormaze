#!/bin/bash
# Run script for Homework 2 CSE 583 Winter 2025
# Place this script in the benchmarks folder and run it using the name of the file (without the file type)
# e.g. sh run.sh hw2correct1

# ACTION NEEDED: If the path is different, please update it here.
PATH2LIB=../../build/hw2pass/HW2Pass.so       # Specify your build directory in the project

# ACTION NEEDED: Choose the correct pass when running.
PASS1=stacked                   # Choose either -fplicm-correctness ...
PASS2=merged                  # Choose either -fplicm-correctness ...
# PASS=fplicm-performance                 # ... or -fplicm-performance

# Delete outputs from previous runs. Update this when you want to retain some files.
rm -f default.profraw *_prof *_fplicm *.bc *.profdata *_output *.ll

# Convert source code to bitcode (IR).
clang -emit-llvm -c -g -S ${1}.cpp -O0 -Xclang -disable-O0-optnone -fno-discard-value-names -o ${1}.bc

# Canonicalize natural loops (Ref: llvm.org/doxygen/LoopSimplify_8h_source.html)
opt -passes='loop-simplify' ${1}.bc -o ${1}.ls.bc

# Instrument profiler passes.
opt -passes='pgo-instr-gen,instrprof' ${1}.ls.bc -o ${1}.ls.prof.bc

# Note: We are using the New Pass Manager for these passes! 

# Generate binary executable with profiler embedded
clang -fprofile-instr-generate ${1}.ls.prof.bc -o ${1}_prof

# When we run the profiler embedded executable, it generates a default.profraw file that contains the profile data.
./${1}_prof > correct_output

# Converting it to LLVM form. This step can also be used to combine multiple profraw files,
# in case you want to include different profile runs together.
llvm-profdata merge -o ${1}.profdata default.profraw

# The "Profile Guided Optimization Use" pass attaches the profile data to the bc file.
opt -passes="pgo-instr-use" -o ${1}.profdata.bc -pgo-test-profile-file=${1}.profdata < ${1}.ls.prof.bc > /dev/null

echo "Before plugin load"

# We now use the profile augmented bc file as input to your pass.
opt -load-pass-plugin="${PATH2LIB}" -passes="${PASS1}" ${1}.profdata.bc -o ${1}.${PASS1}.bc > /dev/null
opt -load-pass-plugin="${PATH2LIB}" -passes="${PASS2}" ${1}.profdata.bc -o ${1}.${PASS2}.bc > /dev/null

# Vizualise all 3
opt -passes="dot-cfg" ${1}.ls.bc -cfg-dot-filename-prefix=vizdot.${1}.base -disable-output
opt -passes="dot-cfg" ${1}.${PASS1}.bc -cfg-dot-filename-prefix=vizdot.${1}.${PASS1} -disable-output
opt -passes="dot-cfg" ${1}.${PASS2}.bc -cfg-dot-filename-prefix=vizdot.${1}.${PASS2} -disable-output

for DOT_FILE in vizdot.*.dot; do
  # Extract the base name without the .dot extension
  BASE_NAME="${DOT_FILE%.dot}"
  
  # Use dot to generate a PDF with the same name as the .dot file
  dot -Tpdf "$DOT_FILE" -o dot_visualizations/$BASE_NAME.pdf
done


# Generate binary excutable before FPLICM: Unoptimzed code
clang ${1}.ls.bc -o ${1}_base
# Generate binary executable after FPLICM: Optimized code
clang ${1}.${PASS1}.bc -o ${1}_${PASS1}
clang ${1}.${PASS2}.bc -o ${1}_${PASS2}

# Produce output from binary to check correctness
./${1}_${PASS1} > ${PASS1}_output
./${1}_${PASS2} > ${PASS2}_output

echo "\n=== Program Correctness Validation ==="
if [ "$(diff correct_output ${PASS1}_output)" != "" ]; then
    echo ">> Outputs do not match ${PASS1}\n"
else
    echo ">> Outputs match ${PASS1}\n"
fi
if [ "$(diff correct_output ${PASS2}_output)" != "" ]; then
    echo ">> Outputs do not match ${PASS2}\n"
else
    echo ">> Outputs match ${PASS2}\n"
fi

echo ">> Starting benchmarking. If hyperfine is not installed, following will fail. Ignore if you are not benchmarking\n"

hyperfine --min-runs 10000 --export-csv base.csv ./${1}_base ./${1}_${PASS1} ./${1}_${PASS2} --export-json ${1}_perf.json --warmup 1000

# After all runs done, run:
# python3 stats.py <benchmark1>_perf.json <benchmark2>_perf.json <benchmark3>_perf.json <benchmark4>_perf.json <benchmark5>_perf.json -o plot --title "Performance Benchmarking" --labels "Unobfuscated","Stacked","Merged"