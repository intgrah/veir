# Verified Intermediate Representation

VeIR is a compiler infrastructure written in Lean that offers both an
[MLIR](https://mlir.llvm.org/)-style imperative design and
(optional) ITP-level verification.
VeIR connects with MLIR via the MLIR textual format, making it
easy to combine MLIR and VeIR tooling.

| VeIR Features                                         | Complete   | Verified |
|-------------------------------------------------------|------------| ---------|
| MLIR core data structures (block, operation, region)  | ✅         | 🔒        |
| define dialects                                       | ✅ (basic) |           |
| pass infrastructure                                   | ✅         |           |
| peephole rewriter                                     | ✅         |           |
| peephole rewriter (declarative)                       |            |           |
| interpreter framework                                 | ✅         |           |

## Testing

Our testing framework is split into two parts: unit tests written in Lean and
[FileCheck](https://llvm.org/docs/CommandGuide/FileCheck.html) tests for the
command line tool `veir-opt`.

### Unit Tests

Run the unit tests with:

```bash
lake test
```

### FileCheck Tests

FileCheck tests require [uv](https://docs.astral.sh/uv/) to be installed.

First, install dependencies:

```bash
uv sync
```

Then run the tests:

```bash
uv run lit Test/ -v
```

## Running the benchmarks

```bash
lake exe run-benchmarks add-fold-worklist
```

## From C to VeIR

This section gives an example showing how to run code through a VeIR
pass, starting from C code.

Prerequisite: An up-to-date MLIR bin directory in your PATH.

Start with a C function:
```bash
cat << _end_ > demorgan.c
unsigned d1(unsigned p, unsigned q) {
  return ~(~p & ~q);
}

unsigned short d2(unsigned short p, unsigned short q) {
  return ~(~p | ~q);
}
_end_
```

Compile to LLVM IR:
```bash
clang -cc1 -O0 -disable-O0-optnone -emit-llvm demorgan.c
```

Optimize it a little:
```bash
opt -passes=sroa demorgan.ll -S -o demorgan-opt.ll
```

Translate to MLIR:
```bash
mlir-translate --import-llvm demorgan-opt.ll | mlir-opt --mlir-print-op-generic --mlir-print-local-scope > demorgan-opt.mlir
```

Optimize using VeIR's InstCombine and DCE (dead code elimination) passes:
```bash
lake exec veir-opt -p=instcombine,dce demorgan-opt.mlir
```

Alternatively, you can batch up these commands using the provided
compiler driver and emit the optimized MLIR to stdout:
```bash
Tools/vcc demorgan.c --emit-mlir -O -o -
```

Without an explicit emit mode, `vcc` translates VeIR's output back to
LLVM IR and asks `clang` to produce an executable:
```bash
cat << _end_ > hello.c
#include <stdio.h>

int main(void) {
  printf("hello, world\n");
}
_end_

Tools/vcc hello.c -o hello
```

## Reusing deleted IR storage

The buffered context has an exact-size free list. Erasing an operation, block,
or region releases its complete byte allocation; subsequent rewriter
construction reuses a free allocation of the same size before extending the
arena. Operation allocations include the results preceding the operation header
and all reserved capacity. Live pointers do not move.

Free-list lookup, insertion, and removal take expected amortized O(1) time.
Reallocation clears the reused range with `memset`, taking O(allocation size),
then initializes its header and properties. Deletion does not scan or compact
the arena. The existing operand/use unlinking costs still apply to operation
erasure. As with other persistent buffer mutations, keeping an old context
snapshot can require copying the backing buffer on the next write.

`Rewriter.eraseOp` now releases storage after detaching the operation and its
operands. `Rewriter.eraseBlock` and `Rewriter.eraseRegion` release detached
containers; callers must first remove their contents and uses and supply the
`FieldsInBounds` proof ruling out dangling references. These APIs do not
recursively delete a subtree. Their well-formedness theorems, together with the
updated construction and replacement proofs, are exported by
`Veir.Rewriter.WellFormed`.

The free-list invariant proves that free ranges are in bounds, mutually
disjoint, and disjoint from every live allocation. Allocation consumes its slot
and preserves the encoding of all other objects. These invariants and the
specification context are erased from the generated executable rewriter code.

This is arena reuse: memory is retained for future allocations, rather than
returned to the operating system. Free ranges are neither split nor coalesced,
so a workload that continually requests new sizes can still grow the arena.
The separate attribute table remains append-only.

Validation:

```sh
lake build Veir.Rewriter.WellFormed allocator-tests ir-reuse-tests
lake exe allocator-tests
lake exe ir-reuse-tests
```

The tests cover slot clearing, neighboring bytes, shared snapshots, distinct
size classes, spare capacity, and 10,000 allocation/erasure cycles for each IR
object kind without arena growth after warmup.

## Parsing MLIR into the buffered IR

`veir-parse` parses a file in MLIR's generic operation form directly into the buffered
context (`Veir/Parser/`). The parser is the one from the main branch, ported to the buffered
rewriter and verified: the context it builds is well-formed and the operation it returns is in
bounds (`IRState.Result`), and no proof obligation is discharged with `sorry`.

- `Veir/Parser/BuffedIR.lean` defines the IR primitives as `buffed` definitions over the `Sim`
  view of the context. Each takes the well-formedness of the context and the bounds of its
  pointer arguments as hypotheses, discharges every other obligation of the rewriter itself, and
  checks the remaining conditions (such as "this operation has no uses") against the buffer at
  run time. Each comes with theorems that it preserves well-formedness and bounds, and that the
  pointers it returns are in bounds. Pointers are exchanged at the specification level
  (`Veir.OperationPtr`, `Veir.ValuePtr`, ...); buffer addresses are recomputed from the buffer.
- The parser is an ordinary monadic program, so it cannot be a `buffed` definition itself. It
  calls the primitives through runtime wrappers that are, logically, the `buffed` base functions
  (which compute both the buffer and the specification) and are implemented
  (`implemented_by`) by the generated `*Impl` functions, carrying the specification field of the
  context along unchanged. The compiler's ghost check guarantees that the `*Impl` functions do
  not depend on it, so the specification is never computed after the empty context. This
  `implemented_by` step and the ghost check are the only trust in the parser.
- `Veir/Parser/IRState.lean` bundles the context with the parser's tables of pointers (values,
  blocks, forward-reference placeholders, the containers being filled) under an invariant
  stating that the context is well-formed and every stored pointer is in bounds. All IR
  modifications go through its operations, which re-establish the invariant; the parser proper
  (`Veir/Parser/MlirParser.lean`) contains no proofs.
- Forward references to values use detached `builtin.unrealized_conversion_cast` placeholders
  whose uses are replaced on definition; the placeholders are erased at the end of parsing, once
  no table refers to any operation anymore. A block referenced before its definition is created
  with the argument types found by looking ahead in the enclosing region for its label (nested
  regions and references in square brackets are skipped), so blocks are never replaced.
- The attribute parser only covers the attributes and types of this branch's `Attribute`.

```sh
lake build veir-parse
.lake/build/bin/veir-parse input.mlir [--allow-unregistered-dialect] [--print] [--lex-only] [--repeat=N]
```

`--print` prints the parsed module back in generic form (values and blocks are named by their
buffer address), `--lex-only` only runs the lexer, `--repeat=N` parses the input N times.
The parse time is reported on stderr.

### Parser benchmark

Inputs are `add-tree-N.mlir` files as produced by the `print-add-tree` benchmark of the
evaluation scripts: a `builtin.module` with N/2 pairs of `"test.test"() : () -> i32` and
`"arith.addi"(%c, %acc) : (i32, i32) -> i32`, i.e. about N operations. Times are the best of 3
runs on one machine; `mlir-opt` and the main-branch `veir-opt` always print their output and
were run with their verifiers disabled.

| N       | veir-parse, parse only | veir-parse, parse + print | main-branch veir-opt | mlir-opt |
|---------|-----------------------:|--------------------------:|---------------------:|---------:|
| 10 000  | 0.04 s                 | 0.06 s                    | 0.06 s               | 0.06 s   |
| 100 000 | 0.39 s                 | 0.53 s                    | 0.55 s               | 0.19 s   |
| 300 000 | 1.36 s                 | 1.75 s                    | 1.74 s               | 0.57 s   |

Peak resident memory at N = 300 000: 267 MB (`veir-parse`), 304 MB (main-branch `veir-opt`),
240 MB (`mlir-opt`). Before the parser was verified (raw buffer pointers in the tables, no
look-ahead for block labels, `sorry` for the proof obligations), it parsed the same inputs in
0.03 s, 0.34 s and 1.21 s with 235 MB at N = 300 000; the difference is the specification-level
pointers stored in the tables and the extra bookkeeping. Lexing the 3.9 M tokens of the
N = 300 000 input takes 0.14 s and building the 300 000 operations in the buffered context about
0.03 s (`buffed-benchmark add-fold-forwards 150000` reports its `create` time); the rest is spent
in the parser itself. A `perf` profile of the unverified parse was flat: about a third of the
samples in allocation and reference counting, the largest single Lean symbol being the
per-operation insertion into the `opLocations` table (5 %), followed by byte-array comparison
and hashing of value names, the name-table updates when leaving a scope, the lexer (2 %) and the
operation construction itself (1 %).
