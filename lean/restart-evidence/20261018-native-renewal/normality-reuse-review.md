# Reuse of actual union-normality producers

Reviewed on 2026-10-19 in Europe/Stockholm. This component adds no Lean
declaration, proof pair, or Lean run. It does not change the frozen
`selected-*` component.

The required preservation results already exist. A new native normality
module would duplicate them. `Good` and union normality remain separate
invariants.

## Exact invariant and initial construction

`SourceCurrentRequiredUnionNormal.ValueNormal` requires
`ordinaryEdges members = none` for a stored union. It imposes no condition
on other value constructors. `UnionNormal heap` checks this condition for
every value in `heap.nodeRecords`.

`SourceCurrentRequiredUnionNormal.source expression` proves this invariant
for the state of the literal `FreshOrdinary.build expression [] empty`.
It does not require a supplied successful result. For a caller whose
physical heap equals that state, rewriting the equality gives initial
normality. Constraint allocation that leaves the physical heap unchanged
does not need a new normality proof.

The same module exposes `build`, `buildMany`, `buildEdges`, `execute`, and
`unfold`. They preserve initial normality through their actual returned
states, including pending outcomes. `request` and `complete` handle the
actual first-writer Mu protocol.

## Native producers already available

The following heads are in
`SourceCurrentRequiredUnionNormalNative`:

- `callback`, `construct`, and `optional` preserve initial normality through
  the actual substitution, filtering, binder construction, and `maybeMu`.
  They need no closure, availability, language, or future-call premise.
- `work_normal` requires the current primitive's `WorkInputs` certificate.
- `step_normal` requires current `SourceEqualityNativeDemandHeap.Inputs`.
  It preserves normality at every stopping state of that one instruction.
- `trace_normal actual normal` requires an actual checked physical
  `Trace`. It gives normality at the exact trace endpoint. No semantic heap
  or successful final result is an extra premise.
- `execute_normal` accepts `InputsThrough`. This head is available, but it
  is not needed when the caller starts an actual compiled node request.
- `query` applies `trace_normal` to an actual `AllocatedTargetQuery.Step`.

`SourceCurrentUnionNormalNativePrograms.request` removes the
`InputsThrough` premise for the actual compiler entry:

```lean
request fuel domain left right before normal :
  UnionNormal
    (NativeDemand.execute fuel (.code (requestNode domain left right))
      before).state.native.machine.heap
```

Its only heap premise is initial `UnionNormal`. The implementation derives
constructor-write safety from every compiler branch. It includes ordinary
rows, unions, references, Mu compilation, checked edge bodies, and yielded
continuations. It covers every bounded outcome. It does not prove that the
query completes or that a failing query has a particular diagnosis.

`SourceCurrentNativePublicationTrace` produces semantic heaps and actual
publication histories. Its `step`, `trace`, `execute`, and `from_history`
heads serve that separate purpose. They need not be changed to recover
union normality. The existing normality producers apply to the same literal
execution. No backwards inference of publication history is required.

## Final record-scan heap

`SourceCurrentUnionNormalScan.records` has the exact record-scan endpoint:

```lean
records g s p h n budget values records before fourth initialNormal :
  UnionNormal
    (AllocatedRecordScanWorker.scan g s p h n budget values records
      before fourth).state.native.machine.heap
```

It has no `Good`, available-input, successful-result, or supplied-graph
premise. Its implementation follows the actual primary gate, secondary
gate, seeded native query, conjunction decision, and record suffix.
Therefore, for an observed scan equation
`scan ... before fourth = .done (stopped, kept) after saved`, rewriting that
equation gives `UnionNormal after.native.machine.heap`.

`SourceCurrentSelectedPrimaryOrigins.selected_class` and `selected_path`
retain the false primary certificate for the same original forest at that
final scan heap. These heads additionally require initial physical `Good`
and availability of the original forest. Their replay uses actual scan
effects. They do not infer normality from `Good`.

The reviewed `selected_source` addition is the direct composition. It
takes the same actual scan, `Good`, availability, initial normality,
selected-record membership, and original-path membership. It returns both
final normality and the false final-heap `PathTrace`.

## Composition with the positive source route

For a nonempty selected path `index :: path`, use the final scan heap for
both gate endpoints. `selected_source` supplies its normality and its false
`PathTrace`. Existing physical scan effects supply final semantic readiness
and availability of the unchanged original forest. The exact growth into a
later target entry remains explicit.

`SourceCurrentPositiveForestProjectionOrigins.forest_read` consumes this
certificate with an actual forest projection and an actual row read. It
derives the exact original forest index, the selected source value, the
actual projection, and an ordinary-only `Route` to the same complete row.
It retains the full symbol, guard, and ordered children. It derives smaller
mass for each child of that source row. Its implementation extracts the
selected node trace from the actual forest lookup; no unrelated node trace
is supplied.

`SourceCurrentActualTargetOperandSourceOrigins.operand` already composes
that result with a literal successful target operand and its physical Merge
writer. Besides the gate certificate, it requires the stated semantic,
cost, availability, `Stored`, causal `Raw`, and plain-guard heap premises.
A positive nonempty own-class output supplies the nonplain source row. The
conclusion retains the literal projection and Merge calls, exact forest
slot, exact full source row, smaller original children, and either row
identity or the actual ordered recursive Merge run.

Normality reuse discharges one independent premise of this composition.
It does not discharge the other physical or causal premises. The source
route starts in the named projection forest. That forest can already be an
edited forest. The theorem does not identify it with an initial outer input
or prove renewal through every selected class edit. An empty forest path
does not select an original slot and is outside this nonempty-path result.

## Other existing execution coverage

There is no need to expand the requested native proof into lower workers.
The following producers already exist:

- `SourceCurrentUnionNormalProjectionGate.forest` and `gate` cover actual
  projection and endpoint-gate outcomes.
- `SourceCurrentUnionNormalTargets.seeded`, `target`, `force`, and
  `shared_leaf` cover literal target operations.
- `SourceCurrentUnionNormalEdits.edit`, `editList`, and `pass` cover shared
  edits and class passes.
- `SourceCurrentUnionNormalLocalParent.reduce` and `parent` cover actual
  local reduction and Parent calls.
- `SourceCurrentUnionNormalOuter.node_call`, `node_body`, `edge_call`,
  `edge_body`, `row_pass`, `descendant_pass`, `child_pass`, and `indexed_walk`
  cover every bounded stopping outcome of the outer workers.

These endpoints preserve an explicit initial normality premise. They do not
assert that arbitrary new records added by an unconstrained `Grows`
relation are normal. No public `Reached`-entry normality producer was found
in this search. Such a producer could compose the existing literal worker
endpoints if an unfinished outer-entry consumer needs it. It is not a
missing native preservation result and is not implemented here.

## Source pins and validation scope

`normality-reuse-manifest.json` lists exact reviewed source hashes and the
separate review files. It uses an explicit allowlist. It pins no root
working fixture, shared runner, peaks file, or mutable probe selection.
This is a read-only source review. It adds zero Lean runs and zero proof
pairs. It does not recount earlier public or constructed probes.
