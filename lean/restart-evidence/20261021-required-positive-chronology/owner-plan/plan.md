# A retained same-child pair from finite positive paths

Status: SOURCE-ONLY PLAN. The proposed geometry theorem is unproved. This package runs zero Lean or canonical commands and changes no official source. The previous Required-entry plan stays frozen.

The finite-path argument is sound. It does not need an assumed common anchor. An ancestry relation is total on every positive path of the copied owner. If every class drops at the copied child index, `child_separate` makes that relation injective at any collision. Its image lies in the same finite owner path set but omits the positive root. The existing finite-relation cardinality theorem gives a contradiction. [R1, R2]

## Smallest proposed public scope

Use one additive geometry module, `SourceCurrentPositiveOwnerPair`, with sole public `same_child_pair`. Its full proposed type is in `proposed-signature.lean.txt`.

Inputs are a literal ordinary owner, one member row with a nonplain guard, the copied output child index, a congruence fixed-point class family, and the backwards positive law to that SAME row's literal child forest. The conclusion is a SAME-child pair in one class:

```lean
∃ paths ∈ classes, ∃ left right,
  index :: left ∈ paths ∧ index :: right ∈ paths ∧ left ≠ right
```

The ancestry input is exactly:

```lean
∀ q, PositiveAt (.node ownerEntry ownerRows ownerDepth ownerFree) q →
  ∃ j p child,
    row.children[j]? = some child ∧ PositiveAt child p ∧
    Rel classes (index :: q) (j :: p)
```

This is a geometry CONSUMER of the proved ancestry law. It is not a new execution producer. It must not appear as a desired-origin premise in a later claim that an arbitrary execution derives ancestry. The later execution corollary must call the actual checked Required/class producer and connect its exact source forest and class family. No caller supplies a finite enumeration, a map, a common anchor, an output callback, or a path-count bound.

## Exact finite object

Let `P(value)` be the set of DISTINCT natural paths `q` for which `PositiveAt value q` holds. Implement it privately as a deduplicated finite list. Prove private membership equivalence and `Nodup`. No public path-set framework is needed. [R3]

- Empty, references, and Mu values contribute no path. `PositiveAt` has no constructor for these heads. Mu stored bodies stay opaque.
- An ordinary node contributes `[]` if some raw row has a nonplain guard. For each raw row, each child at natural index `j`, and each child positive path `p`, add `j::p`.
- A union takes the union of its members' positive path lists. Its membership constructor adds NO path component.
- Deduplicate paths across rows, repeated children, and union alternatives. Do not count row occurrences or alternative indices.

The recursion is on the finite literal `Value` data. It follows ordinary children and union members. It does not unfold Mu or follow heap references. An internal structural termination argument is not a count of positive paths and is not a runtime renewal measure.

The existing `AllocatedFiniteOrdinaryValuePositions` is not this object: it counts literal row/child occurrences, counts Empty as one position, and makes unions opaque. Do not use its cardinalities for this theorem. No existing public exact `PositiveAt` path enumeration was found in the inspected sources. [R4]

## Finite-relation proof

1. Let `L` be the deduplicated private positive path list of the owner. Row membership gives an actual row index. The nonplain row therefore gives `PositiveAt owner []`, so `[] ∈ L`.
2. Suppose no class contains two different suffixes through `index`. This gives exactly the `dropped` premise of `NormalizedChildSeparation.child_separate` for every class in the SAME fixed family. [R1]
3. Use the relation `R(q,r) := Rel classes (index::q) r` from `L` into `L.erase []`.
4. For any `q ∈ L`, the supplied ancestry yields `j,p,child`. Its actual `row.children[j]?` lookup and `PositiveAt child p` give `PositiveAt owner (j::p)` by `PositiveAt.child` using the SAME member row. Thus `j::p ∈ L`. The path is nonempty, so it belongs to `L.erase []`. This proves totality into the smaller list. It does not identify two source occurrences in advance. [R3]
5. If `R(q1,r)` and `R(q2,r)`, `child_separate fixed index dropped` gives `q1=q2`. The common anchor is the collision `r` inside this injectivity proof. It is not an additional hypothesis. [R1]
6. Apply public `SymbolicDriver.relation_cardinality_le L (L.erase []) [] L_nodup R total injective`. The fallback may be `[]`; the lemma does not require it to belong to the target list. It returns `L.length ≤ (L.erase []).length`. Since `[] ∈ L`, erasing it gives length `L.length-1`, a contradiction. [R2]
7. Negate the universal dropped condition to return the actual class and distinct same-child suffixes.

This uses the existing total relational injection lemma. It needs no explicit choice-map API, `Finset`, cardinality framework, or new dependency. Multiple positive proofs at one path do not increase the list length. A nullary row needs no special premise: its source forest has no positive witness, so ancestry at the positive root already fails. A family with no same-child pair, including the empty family, is handled by the same contradiction.

Estimate 180–250 lines including imports, private finite enumeration and its exact membership proof, and the sole public geometry theorem. The new proof work is finite path enumeration and this cardinality application. No native or Parent induction belongs in this module. Review the scope before adding public machinery or going beyond that estimate.

## Actual execution boundaries

The pure theorem has two genuine inputs that an execution corollary must derive.

First, a selected owner copy can derive a nonplain original row. `ActualOwnerSelection.selected` retains actual field loading, precheck, Scan, and `kept ≠ []`. If the effective own equalities were empty, `AllocatedLocalPlain.of_load` and `prefix_cases` would force unchanged, erased, or `.classes []`. The first two contradict the actual classes branch; the third makes the actual empty-record Scan return `kept=[]`. Therefore effective own equalities are not empty, which makes the first conjunct of `SourceMemoGate.plain` false. This route is source-grounded but is not proved by this plan. It needs the selected tuple's real field/readiness facts. [R5–R7]

Second, a class pass returns `Rel` under the selected family. Actual `Retained.fields` gives a sublist of the original Scan records and exact selected paths; `Retained.input` names the original record family. This supports inclusion into that own family. It does NOT imply each own class is literally a member of a later normalized inherited-plus-own family. Normalization can merge classes. [R8]

For the actual combined family, use genuine whole-class `Covers`, not mere path membership. `OuterOriginDependencies.combine_covers` retains each input class inside one normalized output component and returns the same actual combine result, its readiness, and fixedness. Lift a `Rel.member` by placing BOTH original class paths in that one component and keeping its exact suffix; lift `refl` and `trans` structurally. The inherited prefix runs in inherited-first order. Preserve its actual own accessor and combine occurrence. The actual accepted MkEdge and field-load readback must identify the returned row's raw constraint with the original row's constraint before connecting those families. [R9–R11]

Once the pair is in the SAME actual combined payload, `DelayedCombinedOwnerProgress.key_ne_top` consumes that pair and the actual prefix/later-growth/indexed descent receipts. It gives a nonempty child payload and separation from an initial Top-owner key. The pure geometry theorem does not manufacture any of those runtime receipts. A contradictory combined payload has no live child walk; keep that branch separate. [R12]

The warm historical Parent certificate currently retains its writer-entry Merge support, UnionNormal, and GuardHeap Plain, with original false gates at its final Scan. It does not yet supply the writer's Scan `Current`, native positive support, or causal publication history required by the positive chronology entry adapter. Current caller support does not imply those past laws. Thus this geometry closes the proposed common-anchor/counting inference, not historical writer-state admission. [R13]

The result does not prove arbitrary outer completion, a decreasing runtime rank, all failed prefixes, or global termination. It counts finite literal positive paths with opaque Mu barriers. It does not count observational language paths or original syntax occurrences.

## Source references

Whole-file hashes and exact reviewed ranges are in `source-pins.json` and `ranges.json`.

- R1: `SourceCurrentNormalizedChildSeparation.lean` 15–24, 118–145.
- R2: `SymbolicBijections.lean` 94–122.
- R3: `SourceCurrentRequiredPositivePosition.lean` 25–41.
- R4: `SourceCurrentAllocatedFiniteOrdinaryValuePositions.lean` 1–42.
- R5: `SourceCurrentActualOwnerSelection.lean` 59–113.
- R6: `SourceCurrentAllocatedLocalPlain.lean` 27–77; `SourceCurrentAllocatedRecordScanWorker.lean` 64–72.
- R7: `SourceMemoGate.lean` 23–27.
- R8: `SourceCurrentConjunctionSelectedRecords.lean` 73–101.
- R9: `EqualityNormalize.lean` 919–928; `SourceCurrentOuterOriginDependencies.lean` 84–123.
- R10: `SourceCurrentAllocatedInheritedPrefix.lean` 30–42, 65–76; `SourceCurrentEqualityOperationFixed.lean` 112–135.
- R11: `SourceCurrentAllocatedMkEdge.lean` 64–77; `SourceEqualityConstraintFieldLookup.lean` 92–104.
- R12: `SourceCurrentDelayedCombinedOwnerProgress.lean` 52–83.
- R13: `SourceCurrentOuterSupportedParentHistory.lean` 40–57, 466–515.
