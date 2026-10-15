# Native checked demand and retained memo state

The [checked provenance checkpoint](notes-native-checked-provenance.md),
`20982f98`, derives stopped native completion and outer memo Sound. Actual
finite heap Keeps follows from reached current-input checks. Accepted
recursive provenance and derivation of the input/field plans remain open.
Its audit passes 1,955 jobs and 50,413 dependency checks. All Sized contracts
and Haskell definitions remain unchanged. Older next targets are historical.

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Field/code proofs: `c8d5d219`. Resumable interpreter: `c82daff4`.
Stopped-language, completion, outer-memo proofs, and audit: `f4687ad9`.
This extends [checked edge allocation](notes-checked-edge-allocation.md).
Production Haskell and all older proof definitions are unchanged.

## Original stored fields

`SourceEqualityConstraintFieldLookup.load` reads the actual original raw
constraint field. It does not intern that field again. Successful lookup
derives Ready physical storage and literal original constraint readback.
Malformed physical construction retains its checked error. A missing live
key returns unavailable model representation, not a fabricated source error.
Actual original constructor receipts and retained canonical table growth
discharge both lookups. No cached semantic answer is supplied.

`SourceEqualityNativeCheckedCode.children` retains the ordered original
zipped node requests and the final complete edge fields. Its accepted code
equals the older compiler under literal actual conjunction readback and
matching arity. Its trace theorem retains exact child arity and final heap.
The separate sentinel code has no child request. This accepted-code equation
does not establish equality of rejected effects or GHC forcing schedules.

## Resumable native demand

`SourceEqualityNativeDemand.State` carries the entire native state and the
completed equality-operation state. It retains the domain, typed node and
edge memo families, constraint interner, combination table, and descent table.
Every done, yielded, failed, constraint-error, and blocked observation keeps
both state components.

`Control.code` uses the existing instruction code. The new step delegates
non-edge instructions to the earlier native step. Compiled node branches
still emit edge instructions. The new interpreter intercepts those requests
again, so recursive child calls carry the returned equality state.

An edge miss publishes its actual request and starts its thunk before
entering `Control.edgeBody`. The body checks arity mismatch before original
field lookup. Equal arities run actual raw conjunction and the checked edge
prefix. Rejection first demands the sentinel empty field and emits only
sentinel code. Only a ready combined constraint creates child instructions.
Those instructions retain their actual domain and operand order.

Missing original field representation blocks at edgeBody. This preserves
the already demanded completion handle. Re-evaluating that body with updated
storage does not publish or demand the running thunk again. A completed hit
returns its stored complete value and identical full state. A busy hit also
retains the entire state. It remains blocked.

Finite execution has exact bound-splitting and completion-stability laws.
Blocked observations remain blocked when only the bound increases. The
complete five-step mismatch receipt includes publication, thunk demand,
empty equality-field allocation, actual sentinel heap, and original native
thunk completion. Fresh publication derives its captured original request.
No original constraint field or child callback is demanded in that branch.

The represented open edge worker uses its captured operand order. The closed
same-symbol wrapper's outer swap and separate cache remain a correspondence
obligation. The interpreter uses the existing represented native word keys.
Machine key safety remains separate from structural table validity.

## Cache and language proofs

`SourceEqualityNativeDemandOperations` derives current valid growing
operation state for every body and step outcome. `FieldsThrough` requires
only normalized source fields on reached controls. It contains no future
Valid, future Sound, or cached-answer premise. Finite execution derives the
complete atomic constraint-interner trace and retains both completed tables.
The original construction and dynamic field-closure proof must still
instantiate this normalized-field requirement for general source execution.

`SourceEqualityNativeDemandMemo` derives native structural Shape and retains
every earlier completed request/result cell in both families. It also retains
all earlier published key-to-handle entries. The laws cover every finite
outcome. A running request can complete, so the relation does not require
all running cells to stay running. Structural Shape is not completed semantic
provenance and is not machine-word injectivity.

`SourceEqualityNativeDemandMeaning` uses independent guarded record language.
Arity mismatch has no common accepted finite term. Actual checked allocation
rejection also has no common accepted term. These proofs use original
complete constraints and derived active classes. They need no child callback,
nonmemoized replay, or future result law.

`SourceEqualityPartialNativeDemand.execute_receipts` connects the actual
returned interner and native state to the surrounding recursive result memo.
Every observation preserves its original physical keys and result cells.
`execute_sound` transports current outer Sound through actual allocation
receipts and an explicit actual heap-preservation receipt. That heap receipt
is a premise. General execution does not derive it yet. No future Sound is
assumed, and native structural Shape is not used as a semantic substitute.

## Next target and full scope

Define completed native node and edge provenance from this interpreter's
actual checked execution and independent language. The earlier NodeGood and
EdgeGood use the eager kernel's Produced relation. Do not assume that relation
for the changed rejected branch or reuse its physical effects as an oracle.
Prove actual heap preservation and input/result availability. Retain original
requests, published handles, completion frames, source errors, and incomplete
observations. Keep machine range premises explicit. Then discharge the
normalized-field plan from original constructor receipts and dynamic edge
construction. Instantiate the outer Sound transport with derived heap effects.

Connect this execution to selected class folds, reconstruction, both gate
memo families, the complete guarded pass, recursive reduction, and original
graph construction. General caller completion is not proved. Open contexts,
repeated fixed points, getAllAtPath, global unrelated result history, pending
equality-operation thunks, cache/hash/IntMap adequacy, signed indexes, lifetime
reservation bounds, unsafe IO, GHC scheduling, decision-model, named measures,
parser/decoder bridges, and extraction remain open. All distinct Sized
contracts remain intact. Whole-library formalization is not complete.

## Validation

Pinned endpoint command:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialNativeDemand MicroCFTA.SourceEqualityNativeDemandMismatch
```

This passes 1,083 jobs. Log: `/tmp/mcfta-native-demand-focused-20261015.log`.
The aggregate build passes 1,945 jobs and checks 50,309 theorem dependencies.
Only propext, Classical.choice, and Quot.sound occur.
Log: `/tmp/mcfta-native-demand-audit-20261015.log`.
The old unused-input warning remains. The nine new modules have no warnings.
No Haskell file changed. Earlier Nix, six-suite, format, metadata, and 205-rank
checks retain their prior source evidence and were not repeated.
