# MirrorMaze

MirrorMaze is an LLVM-based pass that automatically balances secret-dependent control-flow by inserting “dummy” operations along the shorter branch, preventing timing side-channels without excessive code bloat. It supports two insertion modes:

- **stacked**: naïvely pads every secret branch with the full supergraph of all dummy operations
- **merged**: uses an LCS-based merging of data-dependence graphs to minimize dummy code while preserving uniform path length

---

## Prerequisites

- LLVM 15 or later (with Clang and `opt`)
- CMake and a C++17-capable compiler
- Graphviz (`dot`) for CFG visualization
- `make`, `bash`

---

## Building the Pass

1. Create a build directory and compile:
   ```sh
   mkdir build && cd build
   cmake ..
   make
   ```
2. After building, the plugin `hw2pass/HW2Pass.so` will be available.

---

## 1. Running a Single C++ File

To obfuscate a standalone C++ source:

1. Copy your C++ file into the `benchmarks/correctness/` folder. For example:
   ```sh
   cp path/to/target.cpp benchmarks/correctness/mycode.cpp
   ```
2. Navigate to the benchmarks directory and invoke the compilation script:
   ```sh
   cd benchmarks/correctness
   # Stacked padding (naïve)
   ./compile.sh mycode stacked
   # Merged padding (optimized)
   ./compile.sh mycode merged
   ```
   This produces three binaries:
   - `mycode_base`    — unobfuscated baseline
   - `mycode_stacked` — dummy-flow stacking
   - `mycode_merged`  — merged padding (highly optimized)

3. Run and verify correctness:
   ```sh
   ./mycode_base      # reference output
   ./mycode_stacked   # should match baseline output
   ./mycode_merged    # should match baseline output
   ```
4. (Optional) Inspect the control-flow graphs in `dot_visualizations/`:
   ```sh
   ls dot_visualizations/vizdot.mycode.*.pdf
   ```

---

## 2. Running the Full Benchmark Suite

MirrorMaze includes a suite of standard and custom benchmarks for end-to-end evaluation.

1. From the project root, run the suite driver (this will compile each benchmark, apply baseline, stacked, and merged modes, and measure performance with `hyperfine`):
   ```sh
   cd benchmarks/correctness
   ./compile.sh suite
   ```
2. Requirements:
   - `hyperfine` and LLVM tools (`clang`, `opt`) must be installed and in your `PATH`.
   - The driver runs 10,000 iterations with 1,000 warmup runs to produce reliable timing data.

3. Results:
   - Execution binaries for each benchmark variant
   - CSV and JSON performance logs (in the current directory)
   - PDF graphs in `dot_visualizations/`

---

## Directory Layout

```text
.
├── benchmarks/
│   └── correctness/
│       ├── mycode.cpp   # example user file
│       ├── mycode_base
│       ├── mycode_stacked
│       ├── mycode_merged
│       ├── base.csv
│       ├── mycode_perf.json
│       └── dot_visualizations/
├── hw2pass/
│   └── HW2Pass.so      # built pass plugin
├── CMakeLists.txt
├── compile.sh          # driver script for single files and suite
└── README.md           # this file
```

---


