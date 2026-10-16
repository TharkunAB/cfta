# Checked simultaneous edit effects

Source: `lean/MicroCFTA/SourceCurrentAllocatedSharedEditEffects.lean`.
SHA256: `b7c1ad363a7a475306d5eac388c86232c1834eb4c8d7c077b8a2c00517e28c60`.
Frozen at 2026-10-16 09:23 CEST. The source has 500 lines.

## Checked endpoints

- `node_physical ready edges resident`, `edge_physical ready symbol guard children field available`, and `head_physical ready actualHead available` derive actual physical effects, returned SharedReady and residency. They retain the same equality-operation state and do not require all children to be closed.
- `node_effects reads populated nonempty allowed ready available safe valid` derives some returned inventory and a NodeReceipt.
- `children_effects reads populated allowed ready available safe valid`, `rows_effects ...`, and `list_effects ...` derive aligned receipts. ListSafe checks only selected child domains. A list-root leaf makes no call.
- Common receipt fields are SharedReady, actual RowsAllocation.Effects, native machine Extension, earlier slot retention, completed merge table Extends, and the actual three-table global Effect. Node receipts add availability and Transport. Child receipts add Values and All₂ Transport. Row receipts add Edges and aligned child Transport.

The mutual proof follows actual NodeReads/ChildrenReads/RowsReads. A leaf read carries the receipt derived by the new checked Leaf. A recursive read carries actual HeadReads and its derived global Effect. The finite completion module constructs these annotations; these theorems do not independently assert finite completion. Initial global validity is an explicit premise for constructor-only prefixes. No final invariant or universal guard-conjoin law is assumed.

Original resident edge fields are read at the current initial operation state. Their FieldAvailable proofs grow through the actual child effects before raw edge reconstruction. Source `Interned/Type.hs:391–400` uses raw interning in setChildren when arity is unchanged. The graph's `children_length` proves that positional edits preserve this arity. The model does not claim GHC forcing order from this fact.

The current inventory can change at each leaf. Historical slot inventories remain independent. Unselected ordinary siblings can remain open. Recursive-head closedness follows from the actual selected edit-path domain and a retained callback. No whole-forest closedness, old scoped native execution, old uncached producer law, or future output law is used.

## Validation

Focused command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedSharedEditEffects
```

Terminal 0. Built 1,287 jobs. Raw log: `effects-build-1.log`. Only the existing InternedFreshOrdinaryClosedCompletion unused-input warning was replayed. The new module emits no warnings. Direct pinned Lean also passed before the focused build (`effects-direct-4.log`, terminal 0).

Direct public probe command:

```
LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-checked-edits/effects-public-probes.lean
```

Terminal 0. Raw log: `effects-public-probes-4.log`. Seven public axiom checks, eight full signature checks, and eight kernel examples passed. Axioms are only propext, Classical.choice and Quot.sound. Examples cover ignored root callbacks with open children, nil child and row scans, raw open-child edge reconstruction, same operation state after head reads, actual child arity, and returned closed-path transport. Earlier failed proof/probe logs are retained. They record only local elaboration and explicit unfolding corrections.

No source file outside this new module was edited. Evidence includes source text, probes and raw logs. No evidence .olean, .ilean or .o files were generated. No build process remains owned here.

## Remaining boundaries

This module proves effects conditional on the actual annotated read graph. The new finite edit completion and compiled class wrappers must construct those reads. The outer class fold, complete caller correspondence, exact GHC delayed demand/publication/concurrency, host container iteration and machine identity capacity are separate obligations. Stored CostHeap is the existing unfolding invariant, not a running-time estimate.
