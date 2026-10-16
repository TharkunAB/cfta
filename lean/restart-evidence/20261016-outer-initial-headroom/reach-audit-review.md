# Outer entry reach and initial resource admission

Reviewed at 2026-10-16 23:53 CEST. This review changes no production source.

No counterexample to literal execution was found. The bare prefix graphs do
not permit arbitrary results or arbitrary caller states. Each graph has an
unconditional realization as a successful bounded literal worker execution.
The completed worker return is unique across all sufficient bounds. These
facts need no Context, strict Reads, numeric Plan, or final invariant.

This does not prove automatic strict Reads or admission from initial Context
alone. That stronger theorem is not supplied by the existing admission proof.
The distinction is necessary when deriving a numeric Plan from headroom.

## Exact graph and read boundary

`SourceCurrentAllocatedFiniteOrdinaryOuterEntries.Step` has three transitions
past earlier completed work: `rows_descendants`, `rows_tail`, and `walk_tail`.
They contain an earlier EdgeCall, EdgeCall plus Descendants, or NodeCall.
All other transitions use literal current operations or enter a control
without assuming that control completes. Reach is their reflexive transitive
closure. A transition never contains its current or enclosing completion.

`SourceCurrentAllocatedPartialGraph` pins begin/demand observations, the
captured owner, actual parent field load, inherited-prefix return, descent
state, finish handle, and raw constructor return. In particular, rows use
the returned narrowed edge before processing its descendants. The original
suffix runs at the descendants' actual returned caller. The physical query
Step used by lower target graphs contains a literal native Trace, including
its current physical Inputs and machine-key checks.

`SourceCurrentAllocatedPartialWorkerCompletion` lines 355, 367, and 385
realize NodeCall, EdgeCall, and Descendants graphs as StableRun. These
statements have no semantic or range premises. The corresponding
`SourceCurrentAllocatedPartialWorkerStability` whole-return uniqueness
theorems identify both the result and every caller state field.

The imported `reach-audit-kernels.lean` proves four explicit statements:
node-prefix uniqueness, edge-prefix uniqueness, descendants-prefix
uniqueness, and exact alignment of two complete edge-then-descendants row
prefixes. All four axiom/signature pairs pass. Their proof uses only the
unconditional graph realizations and literal worker equality at common
bounds. It does not use proof irrelevance to equate intermediate states.

The historical unanchored primary receipt defect does not create a new raw
trace alternative here. The raw primary NodeTrace is indexed by its actual
input node. `SourceCurrentAllocatedPrimaryCompletion.lift_node` constructs
anchored strict primary Reads from that same trace and initial availability,
readiness, and memo validity. Its closed endpoint uses the actual node in
SourceEndpointMemo.run. The older unanchored Reads family is not used as a
strict admission theorem.

## Remaining bootstrap obligation

`SourceCurrentAllocatedFiniteOrdinaryOuterRawReads` derives strict Reads for
the supplied raw graph, but each public family still takes a NumericPlan.
`OuterAdmission.step` uses that theorem at the three completed-prefix
transitions. `OuterAdmission.reach` then retains the same root Plan, and
`OuterAdmission.ranges` derives the older range plan. These are valid
conditional results. They cannot be reused to establish that very Plan from
initial headroom without a new independent quantitative argument.

Unconditional graph realization proves operational fidelity. It does not
prove semantic admission of every successful intermediate heap. A proof of
initial headroom must still establish current Context, stored certificates,
profiles, and remaining supplies before each reached parent. It must not
silently obtain them through OuterRawReads with the Plan being proved.

## Smallest additive route

Keep the existing Entry, Reach, Plan, and conditional completion theorems.
First prove a parent-entry adapter from initial Context, inherited Ready,
resident quantitative input, causal stores, and uniform initial headroom to
ParentCapacity. This adapter needs no parent completion or outer Plan.
GuardOwn and ParentUniformBudgets supply the actual own-prefix class/path
bounds needed by ParentInitialCapacity.

Next use a mutual induction on supplied smaller raw prefix graphs. At a
parent leaf, the independent entry headroom derives ParentCapacity and then
strict parent Reads. At each earlier prefix, derive its own Work trace,
request bound, strict Reads, and Post before using the exact returned state.
The outer recurrence must pay earlier work and retain the amount required
for the next entry. A Reach induction can then derive the old NumericPlan
from initial supplies. Neither proof needs an enclosing completed root.

An alternative additive interface can index Reach by the actual memo bundle
and attach strict Reads to the three earlier-prefix transitions. This has a
valid erasure to old Reach and supports direct admission induction. Its
Plan is weaker than the old all-raw-Reach Plan. Erasure alone cannot convert
that weaker Plan to the old one. Using this alternative requires a new
construction theorem whose own produced Reads establish each next reach
witness, or a separate raw-prefix refinement theorem. It is not a shortcut
that discharges the existing Plan by definition.

The present audit establishes exact literal prefix fidelity and uniqueness.
It does not establish initial-only total outer headroom, automatic strict
Reads without numeric assumptions, general Mu progress, or host scheduling.
