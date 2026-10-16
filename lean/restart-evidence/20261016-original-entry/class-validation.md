# Class entry from original allocation history

Validated 2026-10-16 06:42 CEST. The new module is frozen.

Source: `lean/MicroCFTA/SourceCurrentClassHistoryEntry.lean` (160 lines).
SHA256: `4524cb46bf8349a97c9c396a899075c33405499794d98ab2334f3ae0fcb3fccf`.

## Derived contracts

- `constructed width history valid expression covered value heap built`
  derives cold native readiness, stored costs, normalized fields, the
  original root's closed availability, valid completed operation tables,
  and a successful read-only load for every resident original edge.
- `entry` has the same initial history and construction inputs, then an
  actual resident edge. It derives its literal original load/readback and
  ready stored value. For every ready inherited value, it derives finite
  completion of the actual accessor/precheck, exact physical entry branch,
  and validity and growth of the actual returned operation state.
- `cold_scan_memos` derives the loaded original field. An actual live
  allocated prefix and completed historical Scan then derive the retained
  operation state and all four completed global memo invariants, native
  readiness, costs, normalized fields, original child availability, and
  heap retention.
- `cold_scan_sound` derives the same original load. If the original edge
  accepts a term, an actual live prefix and completed historical Scan
  cannot return a rejected class.

These endpoints take no independent `allowed`, per-field `Origin`, load
answer, or operation-cache validity premise. Normalization follows from
the actual History constructor events. Coverage transfers it to the
syntax. Origins and operation validity follow from that same History and
its valid initial interner. The original constructor run supplies native
heap invariants. The actual accessor/precheck supplies its returned cache
effects. No field is allocated by the read-only lookup.

## Exact remaining premises and boundaries

The initial interner must be valid. The actual History and literal
coverage remain premises. The source construction receipt and resident
edge remain premises. The inherited physical value must be ready in the
retained final interner. `entry` derives its prefix completion; the scan
wrappers still consume its actual live branch and an actual completed
Scan. Acceptance is used only by the soundness endpoint.

The operation state is `MemoAllocation.initial finalCache`. It retains the
entire interner returned by History and starts the model's completed
combine/descent tables empty. This is an explicit cold projection, not a
theorem that the source resets global caches. Arbitrary warm table
validity does not follow from the interner History alone.

The existing `SourceCurrentEqualityClassScan.Scan` uses the historical
native-intersection `SourceCurrentEmptinessMemo` decision. It does not
execute the post-4101746a conjunction worklist. This module derives no
new-source Boolean replay or general class/outer-caller termination.
It also derives no GHC field forcing, lazy publication, concurrency,
native container representation, or unrestricted machine-key capacity.

## Literal source entry order

`cfta/src/Data/CFTA/Equality/Operations.hs:160–168` passes the original
constraint's `equalities` accessor, inherited payload, and original child
list to `reduceEqConstraints`; it passes the original constraint to
`mkEdge`. `Constraint.hs:129–135` retains stored equalities for missing or
empty positive guard equalities and otherwise combines them.

`Equality/Operations.hs:206–213` checks both physical empty inputs first,
then combined contradiction, then refused-class emptiness. The live
partition uses ordered original own classes, not the combined class list.
Its refused check uses the secondary gate before its query (219–224).
Required children and narrowing are later branches (226–240).

The finite completed component orders the accessor before the precheck.
It does not establish Haskell demand order for original field construction
or whole lazy row spines. Coverage describes earlier completed field
constructors at the modeled entry. It is not a proof that Haskell eagerly
constructs the full literal inventory in that order.

## Commands and results

Focused pinned build:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentClassHistoryEntry
```

Terminal exit 0, 1236 jobs. Raw log: `class-build-1.log`. No new warning.
The existing unused `inputs` warning occurs in a dependency.

Public probes:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-original-entry/class-probe.lean
```

Terminal exit 0. Raw final log: `class-probe-3.log`. All four public axiom
reports and four full signatures pass. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. Thirteen kernel examples pass. They check actual
Top allocation and identity, retained interner storage, derived original
lookup, exact empty and contradictory prefix effects, empty syntax,
derived finite entry completion, and duplicate literal coverage.

The contradictory-prefix example starts without an interned empty field.
Demand of positive Top first installs it. The precheck returns
`emptyChildren` in that actual returned cache. The empty-input example
starts with that entry present and retains the full operation state.
The probes do not assume all prefix branches are silent.

Earlier probe logs remain as proof-development evidence. The first probe
had notation and binder errors plus an incorrect expected no-allocation
fixture. The second had one empty-constructor unfolding error. The proof
module built on its first attempt and did not change during these probe
corrections. No `sorry`, new axiom, `native_decide`, or Haskell test was
added. No old proof, Audit, documentation, Haskell, or Git state was edited.
