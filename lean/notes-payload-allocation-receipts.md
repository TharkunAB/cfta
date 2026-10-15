# Actual equality payload allocation receipts

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Constructor/cache proofs: `ee8964d7`. Guard/precheck proofs: `b09fcb39`.
Recursive memo integration and aggregate audit: `bb35a074`.
This extends [physical identity correspondence](notes-constraint-identity-renaming.md).
Production Haskell and all older proof definitions are unchanged.

## Checked constructor extension

The [checked-edge checkpoint](notes-checked-edge-allocation.md), `261627c4`,
adds raw conjunction, full arity-accessor demand, sentinel empty-field
allocation, and recursive memo preservation. Its aggregate audit passes 1,936
jobs and 50,146 theorem dependency checks. The next target is delayed native
child execution and complete guarded recursion. Earlier next-target and
validation statements below describe this note's original checkpoint.

## Physical constructors and completed operation caches

`SourceEqualityConstraintAllocation.Value` retains the contradiction tag or
the live identity and complete ordered physical records. `Stored` records its
canonical trie key. `Ready` also retains coherent nontrivial ascending records.
Actual interning produces a finite reserve/install receipt or a read-only hit.
Original cached equality fields and normalized raw classes derive ready
outputs, literal class readback, and these atomic receipts.

`SourceEqualityPhysicalPayloadCanonical` proves that equal trie keys determine
literal coherent records and well-formed payloads. This direction justifies
identity-alias reuse in completed operation caches. It does not prove the
reverse direction from path sets to arbitrary trie representations.

`SourceEqualityConstraintMemoAllocation.State` retains the physical interner
and separate completed combination and descent tables. Entries keep original
complete arguments and results. Validity checks Ready values, exact identity
keys, and the actual existing payload computation equation. Empty operation
tables derive validity from any valid existing interner.

Combination uses the ordered identity pair. Only contradiction and two live
empty operands bypass the memo. One empty and one nonempty operand still use
the memo and normalization. Descent bypasses its memo for contradiction and
live empty. Nonempty descent retains the source empty, singleton, and sorted
multi-class output cases (`Equality/Constraint.hs:449-486`).

Completed hits return the stored result and identical full operation state.
Misses intern the actual physical output and retain both completed tables.
`combine_correct` and `descend_correct` derive valid output storage, Ready
results, exact existing physical payloads, and full interner step receipts.
No cached semantic oracle is supplied. The invariant checks actual old entries.
These are completed sequential cache operations. Pending runtime thunks,
concurrent read schedules, and global memo adequacy remain separate.

## Delayed guard payloads and the actual accessor

`SourceEqualityGuardAllocationPlan` separates the pure positive-syntax Maybe
test from demand of the equality payload. The delayed tree retains every
Same normalization and each original right-fold combination. Its class
projection equals the complete existing positiveNormalized result, including
Maybe failure. No cache is accessed during this syntax test.

`SourceEqualityGuardAllocation.demand` executes a demanded plan through the
completed operation caches. A contradictory first operand returns before
demand of the second payload. Unsupported positive syntax and reflexive Same
failure make no allocation. Exact normalized classes, Ready results, valid
completed tables, and allocation receipts follow by constructor induction.
The finite sequential receipt does not establish GHC forcing adequacy.

`SourceEqualityAccessorAllocation.equalities` retains the original stored
payload when extraction fails or yields live empty. Other positive outputs
use the actual completed combination cache. Its result has exactly the source
sourceEqualities class payload (`Constraint.hs:129-136,171-176`).
Literal `SourceEqualityPhysicalPayload.own` equality uses an actual original
normalized-constructor receipt. `read_roundtrip` derives the required literal
reconstruction. General WellFormed data alone is not assumed to establish
that reverse reconstruction. `construct_complete` supplies the original
receipt for a normalized field without supplied cached answers.

## Native precheck and inherited child receipts

`SourceEqualityPrecheckAllocation` preserves the complete no-op state for two
physical empty inputs. Otherwise it combines own before inherited equalities,
retains any allocation, and returns the exact existing source precheck answer.
The contradiction/live tag proof uses the actual combined physical readback
and the proved terminating normalizer. The combined result can allocate an
entry that never becomes an outer request key (`Equality/Operations.hs:185`).

`SourceEqualityPartialPrecheckAllocation` composes the actual accessor and
precheck at their returned operation states. Original constructor receipts
derive literal source own payloads and exact checked precheck branches.

`SourceEqualityPartialPayloadAllocation.childInheritance` combines inherited
before own equalities for one demanded child. Contradiction makes no child
request. Live output descends at the actual child index through the completed
descent cache (`Equality/Operations.hs:92-95,128-130`). The proof derives exact
physical output and allocation receipts. Parent satisfaction supplies actual
child satisfaction. The resulting inherited value is already stored, so
actual result-memo preparation preserves the full state and uses its existing
physical identity.

## Recursive result-memo integration

`SourceEqualityPartialAllocationFrame` derives frame and Sound preservation
through actual interner traces. It retains native state, all original running
requests, all completed result cells, and their current semantic proofs.
Extra source allocation before a corresponding request preserves publication
handles and cells under the proved physical identity relation.

The partial accessor, precheck, and inherited-child modules apply these laws
to their concrete constructor receipts. They derive current Sound and the
full table frame. They do not assume future Sound or equal native effects
from a nonmemoized replay. Native Scope remains a separate existing invariant.

## Remaining source obligations

Thread these concrete effects through the complete guarded native pass.
The selected class fold, intersection calls, edge conjunction, mkEdge arity
checks, and reconstruction can allocate more constraints. Record their actual
constructor receipts. Preserve original guard labels and both gate memo
families. Then connect the effects to the complete recursive worker and
original graph-construction trace. Do not impose a textual source demand order.

Global result-memo prehistory, pending combination/descent thunks, source cache
and hash-library adequacy, IntMap representation and machine indexes, the
complete lifetime reservation bound, unsafe IO, and GHC evaluation remain
open. Signed-key conversion retains its explicit capacity premise. General
caller completion, open contexts, repeated fixed points, getAllAtPath,
decision-model, named measures, parser/decoder bridges, and extraction remain
open. This is not whole-library correspondence or a termination theorem.

## Validation and preservation

Focused final command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialPrecheckAllocation MicroCFTA.SourceEqualityPartialPayloadAllocation
```

This passes 1,074 jobs. Log: `/tmp/mcfta-payload-allocation-focused-20261015.log`.
The complete `lake -d lean build` passes 1,929 jobs and checks 50,083 theorem
dependencies. Only propext, Classical.choice, and Quot.sound occur.
Log: `/tmp/mcfta-payload-allocation-audit-20261015.log`.
The existing unused-input warning remains. No new module has a warning.

All older Lean proofs except Audit imports, retained reproductions, marked
drafts, stashes, and other worktrees remain unchanged. No Haskell file changed.
Earlier Nix, six-suite, Fourmolu, Cabal-gild, metadata, and 205-rank checks
retain their prior source evidence and were not repeated.
