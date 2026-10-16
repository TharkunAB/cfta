# Checked seeded-query validation

Date: 2026-10-16 06:58 CEST.

The new source file is `lean/MicroCFTA/SourceCurrentAllocatedSeededQuery.lean`.
It has 283 lines. It is frozen at SHA256
`55e0434ab1dd7d232ad4546cd22aa5d8caa5dd91ef9651d7e7f5db4c8fb807bc`.
No older source file was edited for this task.

## Checks

- Pinned Lean 4.34.1 Lake focused build: terminal 0, 1184 jobs.
- Final raw build log: `seeded-build-4.log`.
- Earlier failed logs retain syntax and simplification repairs.
- Standalone public probes: terminal 0, no warnings.
- Eight public axiom probes and eight signature checks passed.
- All axiom probes use only `propext`, `Classical.choice`, and `Quot.sound`.
- Ten kernel examples passed. They check empty input, singleton input,
  seed rotation, table retention, equality-state retention, and complete
  result/state uniqueness.
- The new source has no `sorry`, custom axiom, or old-execution substitution.

## Commands

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedSeededQuery
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-conjunction-scan/seeded-publicprobes.lean
```

## Public API

`Operand path values before result after` records the literal forest
projection. Its final state is `advancePhysical before` with the actual
returned heap and the same equality-operation state.

`Fold values paths before result after` records a singleton projection or
head projection, tail fold, then an actual checked physical request trace.
`Seeded values paths before result after` records empty input or the fold
on `rest ++ [seed]`. Neither graph includes a desired result law or future
state invariant.

`FoldRanges` and `SeededRanges` provide word checks only for native requests
at actual completed prefixes. They do not supply completed requests.

`operand_complete`, `fold_complete`, and `seeded_complete` derive actual
finite graphs. `Seeded.effects` transfers those derived properties to the
same value and complete checked state of an existing graph by deterministic
successful execution. `false_class_complete` derives the projection support
from an actual false secondary class and proper original paths.

Each completion result contains actual graph, final Good, physical Effects,
whole-machine Extension, scoped native cache, Idle, available output, and
empty free list. The false-class endpoint includes the secondary gate in its
physical Effects and Extension. Selected domains allow unrelated siblings
to remain open.

## Fixed assumptions and boundaries

Initial Good, SemanticReady, CostHeap, scoped warm native cells, Idle, and
original-forest availability are explicit. Good includes physical native
cache validity, equality-operation validity, and actual same-cache loaded
fields. Reached machine-word plans remain explicit. No final Good, future
field load, successful child callback, or desired result law is assumed.

Syntactic Original is derived for each generated closed available operand
from current physical coherence. This fact does not prove membership in an
older fixed semantic input inventory. Exact intersection language through
those new identities remains separate.

The graph specifies completed source-shaped operations. It does not prove
GHC demand order, lazy sharing, or runtime correspondence.
