# Checked native and seeded global memo receipts

Date: 2026-10-16 08:17 CEST.

## Frozen sources

```text
fa20921764a5bceb96fae1d3007e9ca9fafd2f39b346f11e4c9da46f984980fb  SourceCurrentAllocatedNativeGlobalMemos.lean
2cbb5092804e13627c1ab01a9d03d631d9b425199757ab4cf19063278aab9f79  SourceCurrentAllocatedSeededMemos.lean
```

Only these two new proof modules and their owned evidence changed.
No old proof, Haskell source, Audit, root document, or Git metadata changed.

## Native contracts

Namespace `SourceCurrentAllocatedNativeGlobalMemos` exports:

- `step_receipt control state memo`: every actual checked step outcome
  derives real `SourceGlobalUnfold.Runs` between its exact constructor
  heaps, with the same unfolding memo and `NoGlobal` events.
- `trace_receipt trace memo`: every actual finite physical `Trace` composes
  those primitive runs. It requires no final validity or result law.
- `trace_memos trace good semantic costs fields memos valid`: a returned
  checked trace derives that operational receipt and coherence of the same
  three-family global bundle at its exact final heap.

The proof reuses the existing operational primitive receipts for each
ordinary instruction. It does not replay an old eager edge body or old
whole native execution. Checked edge publication/demand changes no heap.
The actual checked edge body changes equality operations but retains the
native heap on every outcome. Later emitted child and constructor code
appears in the actual trace and is handled instruction by instruction.
Fixed optional-binder callbacks use the existing expanded constructor
operation proof, not an opaque outcome or future effect premise.

`trace_memos` derives physical heap effects from the actual trace's checks
and initial invariants. Those effects retain global bundle coherence.
No final heap or memo validity is a premise.

## Seeded contracts

Namespace `SourceCurrentAllocatedSeededMemos` defines `OperandReads`,
`NativeReads`, `FoldReads`, and `SeededReads`, indexed by literal actual
checked graphs. `OperandReads` retains the actual `Forest` projection and
its recorded global unfolding calls. `NativeReads` retains real primitive
runs and `NoGlobal`, not only a claim that tables are unchanged.
`FoldReads` composes head projection, tail fold, then the actual native
request. `SeededReads` retains the exact `rest ++ [seed]` rotation.

`operand_memos actual ready available memos valid` derives projection
receipts, final bundle validity, unfolding-table extension, and exact query
bundle equality. It needs no whole-forest closedness or anchor premise.

`fold_memos` and `seeded_memos` have argument order:

```text
unconstrained anchor anchorSemantic anchorReady actual ranges
good ready scopes idle available growth supported memos valid
```

They return `exists saved, Reads actual memos saved` with exact final heap
validity, unfolding-table extension, and `saved.query = memos.query`.
Actual operand and fold effects derive all intermediate physical premises.
The finite effects theorem and graph uniqueness identify the actual tail
state; no chosen final state replaces it. Empty seeded input has a literal
identity receipt. Unrelated original siblings can remain open.

Initial `Good`, physical readiness, scoped and idle native caches, original
forest residency, anchor readiness/support, reached ranges, and global
bundle validity remain explicit. These are initial/current conditions,
not desired completed query or future memo invariants.

## Correspondence limits

The event framework has a genuine global-unfold primitive backed by
`UnfoldMemo.run`. These native traces structurally exclude that primitive.
They cover complete resident operands and actual checked code effects.
The three global tables remain separate from the two native request tables
and equality-operation caches. Global query-table coherence/equality is a
model receipt. No additional predicate/descendant runtime call-silence
theorem, GHC delayed-producer forcing equivalence, concurrent publication,
global unsafe-IO correctness, or machine-identity capacity theorem is
claimed. Whole source caller and global-cache initialization remain
separate adapters.

## Validation

Direct source checks used pinned Lean:

```sh
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedNativeGlobalMemos.lean
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/MicroCFTA/SourceCurrentAllocatedSeededMemos.lean
```

Both terminal 0 with no warnings. Logs: `native-direct-1.log` and
`seeded-direct-3.log`. The earlier seeded logs preserve repaired dependent
constructor-binder and proof-index inference errors. Definitions were not
weakened to repair them.

Focused canonical native build:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeGlobalMemos
```

Terminal 0, 1120 jobs (`native-build.log`). The slot was then released to
the next owner. Root's `current-global-build-1.log` records the canonical
seeded dependency build at job 1327 and terminal success at 1330 jobs.
No duplicate canonical build ran. Only the preexisting unused `inputs`
warning appears in these builds.

Direct public and kernel probe command:

```sh
env LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-current-scan-memos/owned-publicprobes.lean
```

Terminal 0 with no warnings (`owned-publicprobes-2.log`). Six public axiom
checks, six full signatures, and nine kernel examples pass. The only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. The examples
include an actual edge constructor event and checked trace, the explicit
global-unfold event's failure of `NoGlobal`, selected projection beside an
open sibling, singleton/empty seeded receipts, and a real silent native
receipt. The first probe log preserves repaired local name and dependent
proof-index inference errors.

```text
c757a926676f1306fa8aaf4af8445b6f5863f4b16efaac7fc148b9cdb84a5880  owned-publicprobes.lean
4e92cb3a515c6270472cca203ba9a63dd4ae5cd63435ed54023c12ed36ee1485  owned-publicprobes-2.log
```
