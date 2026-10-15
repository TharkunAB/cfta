# Actual running cells and derived normalized fields

Current source update: main `24a710a3`, merged at `6a02619c`, adds a
constrained-descendant check at ordinary path endpoints. The pure current
policy and actual-record finite checks are proved in `3eed507c`. The older
stateful/memo selection pipeline below retains its earlier policy. Caller-cycle
witnesses remain historical; the preserved cold Haskell fixture now completes.
Read [the current source comparison](notes-main-24a710a3.md). General caller
termination and the new descendant memo remain open.

The [main 6fe34ab8 refresh](notes-main-6fe34ab8.md), merged at `9f8d3afc`,
retains these proofs and their existing source bodies. It adds uncovered
derived-refinement frontends and two verified source counterexamples.
The audit remains 1,975 jobs and 50,686 dependency checks. Older source heads
and next targets below are historical.

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Running cells and current validity: `7ab3b4f7`.
Normalized-field closure: `ad4f21de`. Exact request identity: `4fa1fcfa`.
Scoped language laws and aggregate imports: `b03d0d1f`.
This extends [accepted child execution](notes-native-accepted-child-demand.md).
No Haskell source or earlier proof definition changed.

## Actual request bodies and original completion cells

`SourceEqualityNativeDemandNodeReadback` derives the direct, completed-hit,
and started branches from actual node-call completion. It retains exact full
states, original returned cells, actual compiled body traces, and exact
trace counts. A started call appends its original demanded handle. Its
total yielded-step count is the body count plus two.

`SourceEqualityNativeDemandBodyCode` proves that the actual checked edge
prefix emits source code without explicit completion frames. It includes
the source sentinel and accepted child code.

`SourceEqualityNativeDemandRunning.trace_retains` uses strong induction on
actual checked traces. It splits nested calls into their bodies and finish
frames. Both memo structures and every enclosing running cell survive a
completed clean source body. The proof includes actual edge-prefix effects.
It does not transfer completion from the old eager interpreter.
`node_body_cell` and `edge_body_cell` derive the exact original evaluating
cell at the matching finish frame. Structural Shape and actual completion
suffice. No semantic receipt or future validity premise is used.

`SourceEqualityNativeDemandRequestExact` identifies the actual complete
request selected for evaluation. Current checked validity, current original
inputs, explicit word bounds, and actual lookup/demand receipts give literal
request equality. This includes ordered edge payloads.

## Current validity and dynamic normalized-field closure

`SourceEqualityNativeDemandValidity.Inputs` checks only the current
instruction and state. Constructors use their actual physical operands.
Domain entry uses its original domain and available operands. Node and edge
requests retain Ready and KeySafe. Finish instructions require the current
original evaluating cell and its checked NodeProduced or EdgeProduced.
`step_valid` derives checked native validity on every outcome. Actual
machine Extension also follows. These semantic finish receipts remain
explicit obligations. The structural running-cell theorem supplies the
cell-survival part, not the semantic receipt.

`StateValid` retains checked native validity, the full ready physical heap,
and valid equality-operation caches. `execute_invariants` composes these
invariants and actual physical/domain/operation histories along reached
current checks. It assumes no future valid state.

`SourceEqualityNativeDemandFieldHeap.Heap` specializes the existing generic
constraint-heap invariant to normalized stored equalities. Actual resident
edge keys derive their original Cached fields. Raw work with normalized
new annotations retains this invariant. Actual optional-binder construction
also retains it. This uses the existing stored encoder and repaired builder
through nested substitution, both probes, reservation, and completion.

`SourceEqualityNativeDemandCodeFields` proves static annotation closure
through arbitrary appended code, ordered walks, and every compileNode
branch. Node and union construction add no edge annotation. The sentinel
uses the normalized top constraint. Accepted child code uses the normalized
annotation derived by its actual ready prefix.

`SourceEqualityNativeDemandFieldClosure` preserves these facts on every
actual step. A started edge derives its actual original EdgeReady from
the current checked native cell. A yielded accepted prefix derives its
normalized conjunction. Arity mismatch, load errors, absent field storage,
prefix errors, rejection, busy memo cells, and pending binders remain
distinct outcomes.

`SourceEqualityNativeDemandFieldExecution.derive_checks` derives normalized
field checks along finite execution. Its inputs are the initial normalized
physical heap, the compiled continuation annotation facts, StateValid, and
native-only InputsThrough. The earlier FieldsThrough plan is now derived
from those facts. Its aggregate endpoint retains all three cache invariants
and their actual histories. Native InputsThrough is still explicit. Its
physical operand, key-bound, and semantic finish checks are not derived for
every recursive branch. Normalized annotations do not prove that the
sidecar field storage exists. No-missing-field and general completion
claims still require allocation coverage.

## Open language laws and their remaining Mu obligation

`SourceEqualityNativeDemandOpenMeaning` defines explicit source and result
environments. BoundContext resolves names in the actual free map through
physical readback. SeenContext assigns languages only to actual seen pairs.
The local laws cover empty, coherent closed self, swap, closed reset, and
actual repeated branches. Repeated branches require available originals and
their bound-name scope. Environment transport uses actual result scope.
Closed inputs in the exact empty domain give the existing NodeMeaning law.
`contexts_of_closed_readbacks` constructs compatible environments when the
physical bound readbacks are closed.

The module does not replace checked cell NodeMeaning. Its Meaning relation
is a local finite-context law. General contextual Mu correctness is open.
`seen_override_forces` proves the obstruction: a seen-pair assignment fixes
that pair to its operand language. The optional-binder least-language
equation must instead support every fixed-point candidate. The optional
binder equation and scoped environment transport are proved. A suitable
candidate-parametric recursive-domain invariant is not proved.

`repeated_nodeMeaning_any` proves that the existing closed-only law holds
for every hypothetical result at an actually selected repeated branch.
`repeated_reference_boundary` gives exact one-step checked body execution,
that old law, and a concrete failure of unrestricted ambient intersection.
This is a boundary of the language invariant. It is not a proof that every
chosen physical domain and state is reachable from the source entry point.

## Next target and full scope

Derive native InputsThrough from original physical inputs and the actual
compiled branch continuations. Connect exact request identity and proved
running-cell survival to semantic finish receipts. Retain internal word
ranges. Establish a candidate-parametric Mu/repeated-pair language law
before strengthening checked completed-cell semantics. Prove sidecar field
allocation coverage separately from normalized annotations.

Then derive general reached-child checks and connect class folds,
reconstruction, both gate memo families, full guarded passes, recursive
reduction, and original construction. General completion, global causal
prehistory, pending equality-operation thunks, cache/hash/IntMap and signed
index adequacy, lifetime capacity, unsafe IO, GHC, repeated fixed points,
getAllAtPath, decision-model, named measures, parser/decoder bridges, and
extraction remain open. Whole-library scope is incomplete. The optimized
interned core and older constructor/equality work remain. Exact Sized
classes, finite execution, sequence, distinct size order, and both signed
inverse implications remain separate contracts.

## Validation

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityNativeDemandFieldExecution MicroCFTA.SourceEqualityNativeDemandRunning MicroCFTA.SourceEqualityNativeDemandRequestExact MicroCFTA.SourceEqualityNativeDemandOpenMeaning
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

Focused endpoints pass 1,074 jobs. The aggregate audit passes 1,975 jobs
and 50,686 theorem dependency checks. Only propext, Classical.choice, and
Quot.sound occur. Logs: `/tmp/mcfta-native-field-running-focused-20261015.log`
and `/tmp/mcfta-native-field-running-audit-20261015.log`. The older unused
input warning remains. The ten new modules have no warnings. No Haskell
file changed. Prior Nix, six-suite, format, metadata, and 205-rank checks
were not repeated.
