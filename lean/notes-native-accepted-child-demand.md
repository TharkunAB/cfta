# Accepted native edges and actual ordered child execution

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Trace proof: `c3896b48`. Accepted receipt proof: `ff2d49be`.
Fresh node and self-child proof: `970ef848`.
This extends [checked native provenance](notes-native-checked-provenance.md).
Haskell sources and all earlier proof definitions remain unchanged.

## Actual continuation and trace composition

`SourceEqualityNativeDemandContinuation` appends code to both ordinary code
and an already demanded edgeBody. Actual steps retain the appended control,
complete native state, and equality-operation state. The proof covers source
failures, constraint errors, missing storage, busy demands, and pending
constructors. It uses no semantic callback premise.

`SourceEqualityNativeDemandTrace` derives finite traces from yielded or
completed execution. A completed run reaches its returned pure value after
a trace shorter than the supplied bound. One further instruction completes
that trace. These laws do not prove that every request completes.

`TraceSplit` decomposes a completed bound computation into its actual inner
and continuation traces. Their common state is exact. Their lengths sum to
the original yielded-step count. `WalkExecution` derives each ordered child
call from an actual completed source walk. Its child trace lengths sum to
the exact walk trace length. No child result or trace plan is supplied.

## Physical and language receipts

`AcceptedLanguage.forest_zip` combines ordered child intersection laws.
`edge_exact` also requires matching input symbols, equal arity, and the
actual Boolean constraint-conjunction law. Matching arity alone does not
establish matching symbols. `ready_readback` derives literal combined
constraint readback from current normalized fields, actual field loads,
operation validity, and the actual ready prefix.

`edgeMeaning_of_nodes` combines these facts with the independent PCS guard
law. Its child NodeMeaning receipts give closed empty-domain EdgeMeaning.
This does not extend the existing invariant to open contexts or Mu domains.

`ChildWalk.Walk` retains each actual child trace, heap Keeps, physical/domain
Extension, and checked NodeProduced receipt. Its fold derives final available
children, complete histories, ordered child language receipts, and exact
arity. These child facts are explicit recursive proof obligations.

`ChildWalk.Checks` refers to the actual calls and states of a particular raw
walk. `certify` builds the checked fold from those reached-call receipts.
An earlier draft quantified over arbitrary child states, including invalid
states. That premise was too strong to serve as a useful induction
hypothesis. The current theorem checks only walks from the exact post-prefix
state. The superseded compiled drafts remain in `/tmp` and are not imported:
`mcfta-native-accepted-readback-unrestricted-calls-20261015.lean` and
`mcfta-native-accepted-child-walk-unrestricted-calls-20261015.lean`.

`AcceptedReceipt.body_produced` composes the actual ready prefix, ordered
checked child fold, and final constructor. It derives an actual completed
edgeBody execution, resident result, heap Keeps, literal children, arity,
and checked EdgeProduced. If the child fold has n yielded steps, the body
completes in n + 3 instructions. Its actual operation state is retained.
It does not infer correctness of arbitrary children from their completion.

## Observed completion and derived child classes

`AcceptedReadback` derives child calls and the exact final constructor state
from observed accepted-body completion. Its child fold length plus one is
strictly below the parent bound. Thus each actual child's completing bound
is also below the parent bound. Physical effects are not replayed.

`body_produced_of_done` derives provenance and heap preservation of that
observed result if bounded physical and semantic receipts are proved for
its reached child walks. The premise is anchored at the exact prefix state.
General reached-child receipt derivation remains open. This is conditional
accepted-body correctness, not a completed general fuel-induction proof.

`NodeCalls` derives actual fresh pure/self/empty calls and completed hits.
Fresh pure calls yield twice and complete on instruction three. The earlier
four-instruction pure completion bound remains valid but is not minimal.
Completed hits yield once and complete on instruction two. These calls
retain the physical machine and equality-operation state. Fresh publication
and completion preserve the new checked native Valid invariant. Word bounds
and actual key absence remain explicit.

`AcceptedSelfChild` derives a complete accepted parent body for singleton
original child lists whose actual fresh child selects the self branch.
Original edge residency derives child availability. Source guard tests and
actual publication derive the child receipt. The parent then completes in
five instructions with checked EdgeProduced, heap Keeps, a resident result,
literal child output, and the actual prefix operation state. No child
receipt or future validity is supplied. This proves a one-child source
class. It does not assert that the accepted language is inhabited.

## Next target and full scope

Derive reached-child checks through general checked node branches and their
continuations. Retain current native validity, real completion frames, and
word bounds. Mu and repeated-pair cases need a suitable open-context
language invariant. Derive InputsThrough and FieldsThrough from original
physical arguments, constructor receipts, and dynamic constraint closure.
Keep matched-symbol facts from the actual row join.

Then connect the checked caller to selected class folds, reconstruction,
both gate memo families, full guarded passes, recursive reduction, and
original construction. General completion, global unrelated prehistory,
pending equality-operation thunks, native container and signed-index
adequacy, lifetime capacity, unsafe IO, GHC, open contexts, repeated fixed
points, getAllAtPath, decision-model, named measures, parser/decoder bridges,
and extraction remain open. Existential checked-body receipts do not supply
complete causal history correspondence. Whole-library scope is incomplete.
The optimized interned core and older constructor/equality targets remain.
All distinct Sized contracts remain unchanged.

## Validation

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityNativeDemandAcceptedReadback MicroCFTA.SourceEqualityNativeDemandAcceptedSelfChild
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

Focused endpoints pass 1,069 jobs. The aggregate audit passes 1,965 jobs and
50,512 theorem dependency checks. Only propext, Classical.choice, and
Quot.sound occur. Logs: `/tmp/mcfta-native-accepted-focused-20261015.log` and
`/tmp/mcfta-native-accepted-audit-20261015.log`. The old unused-input warning
remains. The ten new modules have no warnings. No Haskell file changed.
Earlier Nix, six-suite, format, metadata, and 205-rank checks retain their
prior source evidence and were not repeated.
