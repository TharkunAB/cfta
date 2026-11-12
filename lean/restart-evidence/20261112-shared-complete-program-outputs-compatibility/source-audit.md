# No-stop Program-output and eager forecast scope

Base `747866e8aa062b3fa430b3d62a4e8c4b1b3b5f0a`. Integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`.
Four modules contain 713 lines and five public laws. All current own-source
strict compiler and explicit public declaration/axiom checks pass. Only
propext, Classical.choice and Quot.sound occur. Full closure and portable
results are recorded in checked.json and portable-check.json.
All 265222 prior Audit bytes remain an exact suffix.

## Source pins and exact public declarations


### SourcePruningEnumerationSharedEagerCapturedBounds

51 lines; SHA256 `8c116a2a1a1ba962fa9045d89498aa5551ef0a228229505bc8edd5b32617eaa9`.

```lean
theorem captured_payload_bounds
    (seed : Seed) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (linked : InternedEdgeResidency.Linked heap)
    (bounded : SourceCurrentConstrainedCapRequiredResources.HeapFits seed.2 heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) heap) :
    (∀ value, InternedProbeProvenance.Available heap value →
      MergedOrdinaryHeight.height value ≤ scalar seed.2) ∧
    (∀ entry rows depth free,
      InternedProbeProvenance.Available heap (.node entry rows depth free) →
      rows.length ≤ scalar seed.2 ∧
      ∀ edge ∈ rows, edge.children.length ≤ scalar seed.2 ∧
        ∀ tries residual,
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ SourcePruningEnumerationGuardWidth.width seed.1)
```

### SourcePruningEnumerationSharedEagerReservation

224 lines; SHA256 `f8bcdd4c5f695c32321e831270ec5703105f4384214a2bf1d0f87c5793610246`.

```lean
theorem eagerFinal_ge (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le seed.2 (eagerFinal depth seed ceiling).2 ∧
      seed.1 ⊆ (eagerFinal depth seed ceiling).1
```

```lean
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```

### SourceSynthesisSharedPreparedOutputControl

317 lines; SHA256 `e6cb60f9fdec07a8dce2d3ce3e88558e5602d21983388c3d63a234e3c641967c`.

```lean
theorem run_output_control
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) (output : Output width Typing)
    (member : output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before)) :
    (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
      (stop = none → output.metadata = none)
```

### SourceSynthesisSharedPreparedProgramOutputs

121 lines; SHA256 `509cf19617920893163688e76434d0f83d917928dc2f8432e0510d8b00add9e0`.

```lean
theorem run_finite_complete_resources_program_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      caller.checked.native.machine.heap before.core marked) (root : marked 0) :
    ∃ bound outcome,
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf none order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, marked uv → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked ∧
        output.metadata = none ∧
        EnumerationPureSelection.next (fun _ => none) output.cache = .done ∧
          ∃ (next : Inventory) (final : Memos) (outputMetadata : Metadata Typing),
            SourceCurrentAllocatedPartialInvariant.Post formulas solver next caller output.caller final ∧
            final.query = output.queries ∧
            Packet formulas solver next output.caller final outputMetadata output.cache ∧
            (output.metadata = none ∨ output.metadata = some outputMetadata) ∧
            Fits (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling).2
              output.caller.checked ∧
            Heap (fun guard => guard ∈
              (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling).1)
              output.caller.checked.native.machine.heap ∧
            ∃ (level : Nat → Nat) (frontier : Nat),
              EnumerationOrder.Stratified output.cache.core level frontier ∧
              ∃ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                (after : EnumerationState.State Symbol Constraint),
                (∀ extra,
                  Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra))
                    output.cache.core actualPartial after ∧
                  ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra) output.cache.core) =
                    [.ok (actualPartial, after)]) ∧
                EnumerationDriver.RenderStable output.cache.core after ∧
                EnumerationCompressionFrame.Frame output.cache.core after ∧
                EnumerationOrder.Stratified after level frontier ∧
                (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
                  (assignment : Nat → Language.Term Symbol),
                  Satisfies language meaning assignment output.cache.core →
                    Satisfies language meaning assignment after ∧
                    SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
                ∃ program, SourceSynthesisProgramTermSize.Projection literal Prod.fst
                    (SourcePruningPositions.openProgram true actualPartial) program ∧
                  ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
                    SourcePruningPartialMatch.Completes assignment actualPartial full →
                      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program
```

## Scope

Actual emitted membership gives two control facts at all work and recursive
fuels, including stopped prefixes. Metadata None implies default selection
is done. Stop None implies metadata None. This observer needs no Packet,
model or reservation. It promises no output or adequate recursive depth.

The single no-stop readback producer retains EVERY old current input and the
ENTIRE stable OutcomeResources/mark/role/partial-root receipt. It transports
membership through the SAME stable actual run at extra=0. The checked control
facts derive finishedness. The output's own full Memos and Packet supply one
actual root producer. Every actual emitted output gets all-larger-read-fuel
singleton equality, RenderStable, full Frame, stratification, all conditional
model observers and one Program projection shared by every completion.
No satisfying Type assignment or completion is supplied. The starting Packet,
Fits, Heap, selection, suspended-mass, Reserved, ProgramSlots and mark0 facts
remain current input hypotheses. Recursive depth remains explicit.

Captured bounds use current Linked, HeapFits and physical guard membership.
They bound old Available payload height, rows, arity and projected tries.
Immutable descendants retain those bounds under later Keeps. The proof does
not assert that all records in a later heap keep the original alphabet.

The pure eager plan derives only from original depth, Seed and mass ceiling.
Its first law gives profile/alphabet growth. Its second locates the first
row's callback in that SAME row's tuple plan, including unused-child padding.
No cross-seed forecast monotonicity is assumed. Parent finalization and
recordTypes keep the native caller and memos; their reads still need fuel.
Generic eager execution domination, admission and resource preservation are
NOT proved. The next computed arithmetic reservation is being developed in
a copied forecast version. All operational child/consumer resource hypotheses
must remain private and be discharged by the concrete worker induction.

The current-source cold initializer is a separate next composition. The old
completed-nodeCall results cannot be relabeled raw startup. A pure width
selector for final depth(seed heap)0 is still unverified. It supplies no
future Room/model/provider premise. The marked draft is preserved below.

No Haskell source changed. Root FINDINGS retains the external Liquid LAST
repeated-name/refinement defect and its owner. No merged repair is known at
the integrated main pin. Older source-pinned counters and current fixes remain.
Default Mu semantics, satisfying models, source adequacy, original-input total
work/host-word capacity, stream order, both inverses and verified Haskell
compiler/extraction/FFI correspondence remain separate.

## Component notes and reviews

### shared-output-control-final-note.md

# R257 actual shared output control: checked result

2026-11-12 23:28 CET. The sole compiler reported strict and public axiom PASS.
Source: SourceSynthesisSharedPreparedOutputControl.lean, 317 lines.
SHA256: e6cb60f9fdec07a8dce2d3ce3e88558e5602d21983388c3d63a234e3c641967c.
Public law: SharedPreparedRecursive.run_output_control.
The original public declaration remains unchanged.

For every actual emitted output of SharedPreparedRecursive.run:
metadata=none implies next default at THAT output cache is done;
stop=none implies THAT output metadata is none.
The statement covers arbitrary stop/order, every work fuel and recursive
depth, and outputs in BOTH complete and stopped result prefixes.
It assumes only actual worker inputs and emitted membership. It requires
no Packet, adequate-depth, native model, future callback, after-state,
source acceptance, resource forecast, or finished-selection supplier.
Zero-depth expansion emits nothing. No output or model existence follows.

The proof follows actual parked restart decisions, callback recursion,
preparation and ordered receipt scans. Named observations retain the SAME
actual receipt, hook and advance result. The private adapter compares only
emitted lists; the worker retains every original endpoint and stop reason.

Final proof trap: local notation advance elaborates as a function term in
a simp list. It is not an unfoldable declaration name. Use the fully
qualified NativeContinuations.advance declaration in that simp list.
Root applied this final proof-only change. All earlier snapshots remain.
This is the actual SHALLOW shared worker. It does not establish the eager
worker, adequate recursive depth, source-model existence or Haskell pipeline.

### shared-prepared-program-outputs-note.md

# Shared prepared Program outputs without a stop rule

Frozen 2026-11-12 22:52 CET. Runtime source only. No compilation here.
Source: SourceSynthesisSharedPreparedProgramOutputs.lean, 121 lines.
SHA256: 509cf19617920893163688e76434d0f83d917928dc2f8432e0510d8b00add9e0
One public law: run_finite_complete_resources_program_outputs.
Namespace: MicroCFTA.SourceSynthesisSharedPreparedProgramOutputs.
Exact 65-line header: shared-prepared-program-outputs-header.txt.
Header SHA256: 44db4e05464520ab12dd42d80d6abed704e98f28d2bbeca5c3e60a6763c9023e.

The old Readback123 input is specialized to stop=none. Every old input remains.
The conclusion retains the SAME stable bound/outcome, all larger-fuel run equations,
full OutcomeResources, and SAME each-output marks/extension/root-zero/ProgramSlots.
It adds output.metadata=none and next(noStop)=done. It strengthens the prior root
implication to its complete unconditional conclusion. All root receipt fields are
unchanged: next, full final Memos, Post, query, Packet, metadata shape, Fits, Heap,
initial/final order, actual all-fuel rootPartial Success and singleton, RenderStable,
compression Frame, conditional Satisfies/completion, and SAME Program Projection
for openProgram and every actual completion. The old conditional observer is
recovered by ignoring its antecedent. No field or explicit requirement is removed.

One Readback producer call supplies everything. Its extra=0 actual run equation
transports emitted membership to run_output_control. That pure observer supplies
metadata=None and finishedness for THAT SAME emitted output and actual run.
The already returned root observer is applied once to the derived finished fact.
There is no second driver, native producer, callback, or root/readback producer.
Complete and stopped-prefix outputs retain their original witnesses.

No future output/Packet/finishedness/roles/model provider is a public input.
No output existence, satisfying assignment, completion existence, adequate recursive
depth, whole-search completeness/termination, or Haskell correspondence follows.
This remains the shallow shared prepared worker, not a default eager traversal.

Readback123 df9d8fdc is ROOT strict/axiom checked. The imported Control285 source
87ee1d9533b39b7a0a64eaef138bd54b92a73d7bdf34e52e74d885d15db7be01
is UNVERIFIED at this freeze. ROOT alone checks dependencies and this wrapper.
No repository, old source, compiler, Git, Haskell, root docs or evidence edits.

### r257-noStop-header-review.md

# R257 noStop ProgramOutputs header review

2026-11-12 23:28 CET. Read-only review. No source or compiler changes.
New: SourceSynthesisSharedPreparedProgramOutputs.lean, 121 lines.
SHA256: 509cf19617920893163688e76434d0f83d917928dc2f8432e0510d8b00add9e0.
Old: SourceSynthesisProgramRolesSharedReadback.lean.
Declarations: run_finite_complete_resources_program_outputs and
run_finite_complete_resources_program_roots, respectively.
New header:33-97 (65 lines). Old header:33-96 (64 lines).
No substantive issue found.

Mechanical comparison PASSED after exactly these semantic changes:
rename the declaration; specialize old stop to none; remove the old
per-output done implication; remove the newly derived metadata=none and
done conjuncts from the new statement. All remaining normalized header
tokens match. No existing premise or receipt field was discarded.

The entire old current input contract remains: Packet, Fits, physical
Heap alphabet, selection membership/length, suspended mass, Reserved,
valid/marked and actual ProgramSlots plus marked root zero. These are
existing current-state/resource hypotheses. No new future provider appears.

The entire stable driver receipt remains: SAME bound/outcome, ALL larger
work fuels and complete OutcomeResources at the SAME final forecast.
Every complete or stopped emitted output retains its extending marks,
root mark and actual heap/core ProgramSlots. Each output now has metadata
none and done derived from its actual run, rather than supplied by a gate.

The whole old readback tuple remains: inventory/full memos/Post/query
identity, Packet/output metadata compatibility, final Fits/Heap, level and
frontier, initial/after Stratified, ONE actualPartial/after, ALL larger
read fuels with exact singleton Success, RenderStable and Frame. Universal
Satisfies preservation/Completes and the SAME Program projection for the
open partial and ALL its completions remain outside independent witnesses.

Proof:99-103 calls the old producer ONCE. retained is reused unchanged.
Proof:105-114 gets SAME outcome from retained.1 at extra=0 and transports
SAME output membership to that literal run. Checked run_output_control
then derives noMetadata and finished. Proof:118-119 uses the SAME output's
old readback finished receipt; it chooses no independent partial or model.

No satisfying assignment or completion is asserted. Universal observers
remain conditional on Satisfies/Completes. No emitted output or adequate
recursive depth is asserted. Resource forecasts remain phase-local input
requirements. The worker is the checked SHALLOW prepared specialization;
actual eager traversal and the full Haskell/default pipeline stay outside
this theorem. Consumer strict status is left to the sole compiler.

### shared-eager-captured-bounds-note.md

# Captured eager bounds source
Status: UNCOMPILED SOURCE. Root is the sole compiler.
Source: SourcePruningEnumerationSharedEagerCapturedBounds.lean, 51 lines.
SHA256: dac2c60271548c55e44ea425a65f00f1e34d5eddafae5dd06449704cf46e7f82.
Public law: MicroCFTA.SourcePruningEnumerationSharedEagerCapturedBounds.captured_payload_bounds.
The exact public header is unchanged from frozen next-captured-eager-bounds.md.
Its separate header SHA is 6d77c148e105e93d816b95e606a9621020b6da1e670f397f5b69c9def63283b0.

Inputs are the CURRENT heap, Linked, HeapFits and physical guard membership.
The first conjunct bounds every Available value's ordinary height by scalar.
The second bounds each Available ordinary node's literal row count, each row's
arity and every successfully projected own-trie count. No projection is assumed.
The proof composes existing height_le_mass, available mass, scalar_mass,
node_width, resident_edges, edge_width and project_le exactly once as needed.

This is a current snapshot theorem. Available.children supplies descendants
inside that same heap. Keeps transports the immutable payloads later. The
whole later heap is not asserted to use the captured guard alphabet. No future
bound, after-heap alphabet, Packet, rank or child-resource supplier is added.
Execution domination, planned-entry admission and eager completion remain open.
No compiler, Git, Haskell or existing repository source was changed.

### shared-eager-first-row-note.md

# The first callback inside the ordered eager plan
Status: UNCOMPILED SOURCE. Root is the sole checker.
Source: SourcePruningEnumerationSharedEagerReservation.lean, 224 lines.
SHA256: 738aff817191e48776ca46982e6e09547a5e5e626ee34eb7389788464a0bd867.
The original checked121 source7343de11 is preserved byte-for-byte as the prefix.
Its immutable snapshot is shared-eager-reservation-121-7343de11.lean.
All original definitions and the existing eagerFinal_ge statement/proof are unchanged.
New frozen public header: shared-eager-first-row-header.txt, SHA
a5d8b9d9ee52c75225d891985d6ad1cb633d70d72b09a1ae423595bd625d2fa0.

New public law: MicroCFTA.SourcePruningEnumerationSharedEagerReservation.first_row_callback_le_final.
Existing public law retained: eagerFinal_ge.
The new law accepts original depth/Seed/ceiling and current computed limit positivity.
It locates the callback after the FIRST ordinary row's OWN planned child slots.
Its profile and guard alphabet fit the full original forecast.

Private fallbackPlan_le_nodePlan locates a node's fallback result before its
remaining ordinary phases. first_callback_le_tuple inducts the tuple count.
Its exact callback entry is advance seed (count*(bound+1)); its mass ceiling is
ceiling+count*bound. advance_add proves the same ordered entry across head/tail.
The tail callback is inside the head forecast, so the inclusion is not a second
execution or an assumption about callbacks. Growth is discharged by eagerFinal_ge.
Private first_row_callback_le_node places that tuple callback before later rows.

For a nullary/short actual tuple, unused planned child slots may later provide
padding to THIS callback occurrence. At maximal arity with terminal children,
those same fallback charges may all be consumed, and the empty-tail callback
needs no additional native stage. Parent finalization/recordTypes are native-neutral.
Actual resource preservation at those boundaries is NOT proved here.
The private tuple lemma holds at any planned Seed for later row-stage proofs;
the public specialization currently names the first ordinary row only.
No cross-seed monotonicity, execution trace, capacity, Packet/model provider or
executable worker change is introduced. No compiler, Git or Haskell was run.

### next-captured-eager-bounds.md

# Current captured bounds for the eager forecast
Status: READ-ONLY UNPROVED BRIDGE PLAN. No source or compiler changes.
The forecast121 itself passed Root strict compilation/axiom audit at7343de11.
All file names below are relative to lean/MicroCFTA/.

## Result
The limit and fixed own width can be derived from the captured current heap.
No new height/mass induction, future rank supplier or global after-heap alphabet
invariant is needed. Exact existing dependencies:
- SourceCurrentMemoMergeUniformNumeric.height_le_mass:22 uses precisely
  MergedOrdinaryHeight.height, including its Mu/union cutoff.
- InternedValueMassHeap.available:74 bounds every CURRENT Available value by
  HeapFits.stored. SourceCurrentConstrainedCapRequiredResources.of_checked:105
  constructs that HeapFits from current Caller Fits.
- SourceCurrentConstrainedCapTargetForecast.scalar_mass:54 bounds profile.mass.
- SourceCurrentConstrainedCapRequiredResources.node_width:50 and edge_width:59
  bound literal rows/arity from Available parent and exact EdgeResident.
- InternedEdgeResidency.resident_edges:40 gives that residency from current
  Linked and Available.resident. Facts.linked supplies Linked when needed.
- SourceEqualityAnnotationHeap.Heap:15 at edge.entry.key gives membership of
  THAT exact physical guard in the original captured alphabet.
- SourcePruningEnumerationGuardWidth.project_le:39 then bounds every successful
  projection's tries. Unsupported projection is not silently assumed supported.

## Minimal public bridge header (new, unproved)
Aliases: Symbol=SourcePruningTemplates.Symbol;
Constraint=SourceSymbolicIndex.Constraint FullSyntax.Formula;
Node=Value Symbol Constraint; Edge=EdgeValue Symbol Constraint;
Seed=SourcePruningEnumerationSharedIncomingReservation.Seed;
scalar=SourceCurrentConstrainedCapTargetForecast.scalar.
```lean
theorem captured_payload_bounds
    (seed : Seed) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (linked : InternedEdgeResidency.Linked heap)
    (bounded : SourceCurrentConstrainedCapRequiredResources.HeapFits seed.2 heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) heap) :
    (∀ value, InternedProbeProvenance.Available heap value →
      MergedOrdinaryHeight.height value ≤ scalar seed.2) ∧
    (∀ entry rows depth free,
      InternedProbeProvenance.Available heap (.node entry rows depth free) →
      rows.length ≤ scalar seed.2 ∧
      ∀ edge ∈ rows, edge.children.length ≤ scalar seed.2 ∧
        ∀ tries residual,
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ SourcePruningEnumerationGuardWidth.width seed.1)
```
The proof uses only the listed existing laws. No Packet or higher-level Ready
is needed beyond their CURRENT linked/HeapFits projections. This universal
current-snapshot form avoids a new descendant predicate or reachability type.

## Why fixed own covers actual eager descendants
InternedProbeProvenance.Available.children:48 recursively retains EVERY literal
child of the captured payload in the SAME old heap. Its children:14 includes
ordinary edge children, union members and all three Mu payloads. For each actual
ordinary descendant, apply captured_payload_bounds at that same heap. Global
selector membership restricts edgesOf to that descendant's literal rows; the
separate length hypothesis bounds duplicate occurrences. It cannot be omitted.
SharedEagerChildren.eagerChild:134 recursively passes literal staged children.
ChildVisitors.visitSelected:48 obtains these through the SAME CachedOwn.prepare;
OwnInputShape.prepare_inputs:32 identifies the exact EdgeInputs child payloads.
A terminal/opaque fallback returns a fragment; its newly queried native value is
NOT fed back into that same ordinary eager descent. Thus newly generated guards
in the later global heap do not enlarge this captured descendant's own width.
SourceEqualityRequiredCache.Keeps.available:31 and actual Post.effects.keeps
retain those old values at later global endpoints. Literal payloads and guards
are unchanged; the entire later heap need NOT fit the old alphabet.
A new outer callback starts a NEW captured phase and recomputes its own bounds.

## Actual preparation and remaining boundary
SelectedPreparationPointResources.run_resources_known:26 retains SAME observed
preparation endpoint, normalization Fits/mass and the SAME arbitrary original
Heap predicate. Thus guard membership survives actual native preparation,
including canonical hits, before choosing captured=preparedSeed. Facts and
Available prepared result come from the same preparation packet/receipt.
PreparedSeed is SharedPreparedReservation.preparedSeed:26; its alphabet is
unchanged. Apply this bridge to THAT actual heap, not an independent producer.
The pure forecast has no execution/admission domination law yet. This bridge
closes numeric payload/guard ceilings only; the coupled CPS resource induction,
planned entry admissions, common workFuel and outer source depth remain open.

### next-eager-charge-domination.md

# Parent charges and the first callback inside an eager tuple
Status: READ-ONLY UNPROVED DOMINATION PLAN. Checked sources are unchanged.
Forecast121 strict PASS7343de11. CapturedBounds51 strict PASS8c116a2a (Root repair).
Source file references below are relative to lean/MicroCFTA/.

## Charge table
| Actual step | Native forecast charge | Exact planned location |
| --- | --- | --- |
| Selected narrowing and native preparation | existing preparedSeed | before nodePlan |
| CachedOwn.prepare / own-class suspension | zero native mutation | row entry; bucket bound becomes B+W |
| Nonordinary/terminal child dispatch | advance(seed,Bchild+1) | THAT child's fallbackPlan, once |
| Remaining tuple | its complete forecast | inside each head success continuation |
| SelectedEdge.finish residual | zero native mutation | after children, before receipt consumer |
| Captured parent Finalize.run | zero native mutation | at the selected receipt's same caller/memos |
| recordTypes before recursive resume | zero native mutation | same caller/memos, before K's lower-depth worker |
| Concrete lower-depth resume | eagerFinal depth at reached planned Seed | K at that tuple completion |
| Later sibling | its whole row transform | after prior visitor/tail/K endpoint, same captured Core |

No parent charge is taken from an already consumed child fallback quota.
SourcePruningEnumerationSharedSelectedContinuations.finish:427 only adds a Core
obligation. SourcePruningEnumerationFinalize.run:24 returns Option Cached at a
FIXED heap; NativeIndex.write:41 reads flags and representative paths but cannot
return a changed native heap. ChildVisitors.visitCapturedWith:79 passes the SAME
reached caller/queries through finalization into the hook. Finalize.complete:49
already supplies finite index fuel and its exact Core/index result.
SourcePruningRecordTypes.recordTypes:50 returns an EnumerateM Core action.
SharedPreparedCallbackResources.callback_complete_resources:37 retains SAME
caller, full memos and Seed; its Frame/RenderStable and singleton raw result
identify the exact continuation entry. Only recur can then change native state.
SourcePruningEnumerationEdgeScalarBounds.Finalize.run_scalars:138 preserves
the counter and cannot increase suspended mass; callback Frame preserves values.
Zero native charge does NOT mean zero representative/rendering/oracle workFuel.
These finite pure reads still need their existing completion and fuel lemmas.

## Nullary and maximal-arity checks
A nullary row calls its parent consumer immediately. The planned row has N
phantom child slots. Do NOT borrow the node's earlier fallback K payment for
EVERY nullary row. Each row needs its OWN callback occurrence in its own tuple
forecast. The earliest all-fallback path through that tuple provides one.
For row bucket bound b=B+W, mass ceiling M and entry Seed s, define
  a=advance s (N*(b+1)); m=M+N*b.
The row's first all-fallback continuation is EXACTLY K m a. Nullary actual code
can pad its unchanged native Fits/Heap from s to a, then call its actual K using
that larger current mass ceiling. The K result fits a later stage of THIS row.
At maximal arity N with terminal children, every one of those N fallback charges
may be used by actual children. Parent finish/finalize/recordTypes need no extra
native stage; the last child's empty-tail continuation is that same K m a.
For fewer than N actual children, only the remaining phantom stages are padding.
A stopped child/hook preserves its full stopped prefix and has no actual suffix.
No extra hypothetical operation is executed to obtain a later Seed.

## Exact next mathematical bridge (unproved)
The missing lemma is CONTINUATION-INCLUSION, stronger than start-to-finish growth.
Prove internally against the already checked private tuplePlan/nodePlan:
```lean
private theorem first_callback_le_tuple
    (depth limit own height count bound ceiling : Nat) (seed : Seed) :
    let done := fun retained current => eagerFinal depth current retained
    let entry := advance seed (count * (bound + 1))
    let first := eagerFinal depth entry (ceiling + count * bound)
    let whole := tuplePlan (nodePlan limit own height) count bound ceiling done seed
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```
Induct count. Every nodePlan starts with fallbackPlan at EVERY height. Apply IH
inside its tuple-tail continuation, then the remaining node ordinary-row growth.
Use advance_add for the exact entry equality. K growth is eagerFinal_ge, proved
internally; no cross-seed monotonicity, child-resource or future capacity supplier.
This lemma is pure and does not claim an actual invocation happened.

One public concrete specialization avoids exposing abstract continuation or rank:
```lean
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```
The node's first planned fallback finishes at rowStart; first ordinary row then
contains the indicated tuple. Positive N is current numeric data, derivable from
captured HeapFits.stored.positive and scalar_mass, not a future rank promise.
The analogous generic private tuple lemma applies at EVERY later row stage.

## Boundary
No missing parent native charge or concrete undercount was found in these cases.
Growth alone does NOT prove the inclusion lemma or eager execution domination.
Actual resource IH must still transport SAME Packet/fragment/protection/full Post
at those entries and preserve complete/stopped outcomes. Callback observations
must be attached before SharedPreparedRecursive.finish discards processed rows.
The native-stage forecast stays unchanged; no eagerReserved gate is introduced.

### current-source-program-outputs-next.md

# Current source to the same no-stop Program outputs

Read-only audit, 2026-11-12 23:30 CET. No implementation or compilation.
The smallest honest composition starts at the COLD raw source value. It does
not require the completed nodeCall from CheckedHereditary208/ComputedWidth112.

ONE producer: CurrentProgramSlotsInitialization.accepted:34 (71-line module).
Keep its ENTIRE fields/cache/value/heap/built/preparation/conjunctionFields/
Context/Facts/Available/ProgramValue/growth/issued/Derived-guard-Heap/identity/
emptyValue/Ready/closed/Original/ValueFields/handle/encode/decode/ProgramSlots
receipt. Fix initial cache to Cache.emptyState, initial validity to empty_valid,
valid role predicate to Origin(encodedLibrary lib), and marked uv to uv=0.
The actual caller is Initial.caller (bits+2) cache heap; inventory and full
Initial.globals are those of this SAME built value and prepared cache.
There is no need to call CallerInitialization80 separately.

Packet: InitialPacket.initial_packet:30, or InitialCarriers.initial_packet_carriers:27,
takes THAT Context/Available/closed and CURRENT metadata.pending=[]. It supplies
literal startup, Packet, Canonical, stored root, suspendedBound=0, exact waiting
and every candidate flag; the carrier variant also keeps root/reference carriers.
Its returned handle equals the retained initializer handle by their two
encodeNode value=some handle equalities. No native operation is repeated.
startup.core is exactly EnumerationState.initial handle, so existing mark-zero
ProgramSlots applies definitionally. initialMass uses ceiling=0 and suspended=0.

Seed: OriginalSharedRankCompletion.seed:41 is
  (ConjunctionGuardUniverse.guards heap,
   <heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap>).
SAME initial Fits is <le_refl, le_refl, le_refl, InternedValueMassHeap.initial heap facts>.
SAME physical Heap follows from ConjunctionGuardUniverse.initial:26 heap facts.
CheckedHereditary208:126-129 already uses these exact proofs; these are observers
of current heap data, not a completed-worker endpoint or future resource supplier.
Keep the initializer's Derived guard Heap too; it is a different predicate.

Selection: choose InternedEdgeResidency.nodeEdges:16. On .node it is EXACTLY rows.
selectionMembers is fun _ _ _ _ _ member => member; selectionLength is le_refl.
Do not substitute MergedFreshOrdinaryExposure.nodeEdges:37: that is a heap-changing
fuelled exposure, not this Node->List selector. A different actual ordering may
retain the generic old selection inputs, but is a separate configuration cut.

Capacity is the only small NEW source-input bridge. CurrentInitialComputedRoom.bits
covers a NodeCall forecast; no existing law says it reserves the enumeration
final depth (seed heap) 0. Reusing it without a comparison would be unjustified.
The exact proposed pure selector (same implicit equality instances throughout):
  enumProfile lib query signed depth :=
    match CurrentConstruction.firstOrderRaw lib query signed with
    | .error _ => <0,0,0,0>
    | .ok expression =>
      match build (ordinarySymbols expression) [] empty with
      | .pending _ _ => <0,0,0,0>
      | .done _ heap => (SharedPreparedReservation.final depth (seed heap) 0).2
  enumBits lib query signed depth := ParentInitialRoom.roomBits
    (enumProfile lib query signed depth)
Small NEXT public headers, using current existing Profile/Reserved only:
  enumProfile_of_build (lib query signed expression returned depth value heap built) :
    enumProfile lib query signed depth =
      (SharedPreparedReservation.final depth (seed heap) 0).2
  enum_reserved_of_build (lib query signed expression returned depth value heap built) :
    SharedPreparedReservation.Reserved
      (enumBits lib query signed depth) depth (seed heap) 0
The shared explicit binders for these two headers are:
  (lib : Library) (query : Query) (signed : Int) (expression : Expression)
  (returned : CurrentConstruction.firstOrderRaw lib query signed = .ok expression)
  (depth : Nat) (value : Node) (heap : State Symbol Constraint)
  (built : FreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap)
Here returned and built are the SAME literal source/build equations used by71.
The first proof is simp [enumProfile,returned,built]. The second rewrites it and
uses SharedPreparedReservation.reserved_computed:312 (or reserved_of_final_room:272).
The pure match is a deterministic input expression, not a second build producer.
This computes a mathematical sufficient width, not a fixed host-word guarantee.

Exact future wrapper shape: original lib/query/signed/expression/returned, depth,
formulas/solver, current metadata/emptyPending, and existing current driver
holeKey/fits/admits/graph/templates/checkEmpty/order. Choose bits=enumBits from these
ORIGINAL inputs before the ONE71 call. Preserve its entire literal result above.
Append exact same-handle startup/carrier packet plus its SAME Fits/Heap, then
invoke SharedPreparedProgramOutputs.run_finite_complete_resources_program_outputs
ONCE with inventory/build caller/globals/startup/metadata, seed=(seed heap), ceiling=0,
valid=Origin(encodedLibrary lib), marked=(.=0), root=rfl, selector=nodeEdges.
Append its ENTIRE bound/outcome/stable all-fuel/OutcomeResources and unconditional
each-output metadata-none/finished/extended-marks/ProgramSlots/full Program-root
receipt. This uses no second native build, initializer, pruning worker or readback.
There is no supplied after-Packet/roles/model/Room/finishedness/provider premise.

The new wrapper retains the source initializer71, not a fictional nodeCall endpoint.
208/112/Typed158 remain separate completed-pruning results; their outputs are not
renamed as the raw startup. Program-output shape alone does not establish ordinary
Typed for every emitted Program or existence of a satisfying ground completion.
No avoid=[] premise is needed for this source-structure/startup cut; existing
positive Eligible/root language completeness still has its explicit avoid=[] domain.
Depth remains an explicit INPUT, with no adequate-depth or output-existence claim.
The worker remains shallow shared prepared enumeration, with default/eager/Haskell
correspondence and whole-search completeness/termination separate.

Historical candidate notes retain their original validation time. The exact
source pins above all have successful current own-source reports. Root
replaced two unsupported Nat .trans fields with Nat.le_trans in CapturedBounds.
Root qualified the local notation advance in the control simp list; an
unqualified notation there is a function expression, not a simp declaration.
The forecast extension's final conversion explicitly unfolds the same fixed
definitions. These proof-only edits change no public header.

## Reproducible preserved source snapshots

Apply each standard zero-context patch to the preceding source with
`patch --output NEXT PREVIOUS PATCH`. Each patch was replayed and checked
against the exact stated SHA256. These snapshots add ZERO public laws.

### Chain from SourceSynthesisSharedPreparedOutputControl

Start at the exact current repository source pin above.

Snapshot `SourceSynthesisSharedPreparedOutputControl-80b5aa00.lean`, SHA256 `80b5aa007ac17c4dc77129578129e82f0fd75a060cf84b18a4eac3ddc3a23229`.

```diff
--- SourceSynthesisSharedPreparedOutputControl.lean
+++ SourceSynthesisSharedPreparedOutputControl-80b5aa00.lean
@@ -217,2 +217 @@
-                  SourcePruningEnumerationSharedReceiptContinuation.run, captured,
-                  SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance, controlFoldEmitted]
+                  SourcePruningEnumerationSharedReceiptContinuation.run, captured, advance, controlFoldEmitted]
```

Snapshot `SourceSynthesisSharedPreparedOutputControl-2b4bac82.lean`, SHA256 `2b4bac82158c99fe4aa4da60f84736d1f31ae3829ec31bac17c066a001c45255`.

```diff
--- SourceSynthesisSharedPreparedOutputControl-80b5aa00.lean
+++ SourceSynthesisSharedPreparedOutputControl-2b4bac82.lean
@@ -201,4 +201,4 @@
-          have same : controlFoldEmitted (SourcePruningEnumerationSharedBranching.visitCaptured hook checkEmpty r n p h k
-              target scs edge actual current cache) = controlFoldEmitted (SourcePruningEnumerationSharedReceiptContinuation.run
-                hook actual current (SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
-                  target scs edge actual cache current)) := by
+          have same : SourcePruningEnumerationSharedBranching.visitCaptured hook checkEmpty r n p h k target scs
+              edge actual current cache = SourcePruningEnumerationSharedReceiptContinuation.run hook actual current
+                (SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
+                  target scs edge actual cache current) := by
@@ -208 +208 @@
-                SourcePruningEnumerationSharedReceiptContinuation.run, captured, controlFoldEmitted]
+                SourcePruningEnumerationSharedReceiptContinuation.run, captured]
@@ -214,2 +214,2 @@
-                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, called, controlFoldEmitted]
-              | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ =>
+                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, called]
+              | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ =>
@@ -217,9 +217 @@
-                  SourcePruningEnumerationSharedReceiptContinuation.run, captured, advance, controlFoldEmitted]
-              | stopped fragments observation candidate =>
-                cases advanced : advance (.stopped fragments observation candidate) with
-                | none => simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
-                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, advanced, controlFoldEmitted]
-                | some endpoint =>
-                  obtain ⟨reached, saved⟩ := endpoint
-                  simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
-                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, advanced, controlFoldEmitted]
+                  SourcePruningEnumerationSharedReceiptContinuation.run, captured]
```

Snapshot `SourceSynthesisSharedPreparedOutputControl-1cc5f400.lean`, SHA256 `1cc5f400c70c5098dd4c60efff6f0b24d0b7e59e97a56af4b07a635e03dea483`.

```diff
--- SourceSynthesisSharedPreparedOutputControl-2b4bac82.lean
+++ SourceSynthesisSharedPreparedOutputControl-1cc5f400.lean
@@ -205 +205,2 @@
-            cases captured : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
+            unfold SourcePruningEnumerationSharedBranching.visitCaptured SourcePruningEnumerationSharedReceiptContinuation.run
+            cases SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
@@ -207,11 +208,2 @@
-            | none => simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
-                SourcePruningEnumerationSharedReceiptContinuation.run, captured]
-            | some receipt =>
-              cases receipt with
-              | complete fragment reached saved after =>
-                cases called : hook fragment reached saved after <;>
-                  simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
-                    SourcePruningEnumerationSharedReceiptContinuation.run, captured, called]
-              | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ =>
-                simp only [SourcePruningEnumerationSharedBranching.visitCaptured,
-                  SourcePruningEnumerationSharedReceiptContinuation.run, captured]
+            | none => rfl
+            | some receipt => cases receipt <;> first | rfl | (split <;> rfl)
```

Snapshot `SourceSynthesisSharedPreparedOutputControl-3ded257c.lean`, SHA256 `3ded257cf52c15b1cdf75c4fe516fe7c6ffee0f36b47958d6daed307dfe1086c`.

```diff
--- SourceSynthesisSharedPreparedOutputControl-1cc5f400.lean
+++ SourceSynthesisSharedPreparedOutputControl-3ded257c.lean
@@ -31,0 +32 @@
+
@@ -33,0 +35 @@
+
@@ -35,0 +38 @@
+
@@ -47,0 +51 @@
+
@@ -61,0 +66 @@
+
@@ -87,0 +93 @@
+
@@ -158,0 +165 @@
+        dsimp only
@@ -165 +172 @@
-    · repeat' first | trivial | split
+    · repeat' first | trivial | (split <;> dsimp only)
@@ -201,10 +208,3 @@
-          have same : SourcePruningEnumerationSharedBranching.visitCaptured hook checkEmpty r n p h k target scs
-              edge actual current cache = SourcePruningEnumerationSharedReceiptContinuation.run hook actual current
-                (SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
-                  target scs edge actual cache current) := by
-            unfold SourcePruningEnumerationSharedBranching.visitCaptured SourcePruningEnumerationSharedReceiptContinuation.run
-            cases SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
-                target scs edge actual cache current with
-            | none => rfl
-            | some receipt => cases receipt <;> first | rfl | (split <;> rfl)
-          rw [same] at member
+          change output ∈ controlFoldEmitted (SourcePruningEnumerationSharedReceiptContinuation.run hook actual current
+            (SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k
+              target scs edge actual cache current)) at member
```

Snapshot `SourceSynthesisSharedPreparedOutputControl-87ee1d95.lean`, SHA256 `87ee1d9533b39b7a0a64eaef138bd54b92a73d7bdf34e52e74d885d15db7be01`.

```diff
--- SourceSynthesisSharedPreparedOutputControl-3ded257c.lean
+++ SourceSynthesisSharedPreparedOutputControl-87ee1d95.lean
@@ -139,6 +138,0 @@
-private def ControlPrefixDecision (stop : Option (Metadata Typing → Nat → Bool))
-    (order : Metadata Typing → List Nat → Option Nat) : SourcePruningEnumerationSelectedStep.Result width Typing → Prop
-  | .parked _ (some parked) (some [.ok ((updated, next), core)]) =>
-    next = SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core parked)
-  | _ => True
-
@@ -151,2 +145,5 @@
-    ControlPrefixDecision stop order (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
-      stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries) := by
+    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
+      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries with
+    | .parked _ (some parked) (some [.ok ((updated, next), core)]) =>
+      next = SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core parked)
+    | _ => True := by
@@ -161 +158 @@
-      | none => simp only [Option.map_none]; trivial
+      | none => simp only [adapted, Option.map_none]; trivial
@@ -163 +160 @@
-        simp only [Option.map_some]
+        simp only [adapted, Option.map_some]
@@ -201,4 +197,0 @@
-          change ∀ output ∈ controlFoldEmitted (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
-            hook checkEmpty r n p h k target scs (EnumerationExpandableIndex.frame entered before)
-            (edgesOf (.node entry rows depth free)) (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries),
-            Controlled stop output
@@ -232,5 +225 @@
-      constructor
-      · intro impossible; cases impossible
-      · intro noStop
-        rw [noStop] at consistent
-        cases consistent
+      exact ⟨fun impossible => by cases impossible, fun noStop => by subst stop; cases consistent⟩
@@ -247,5 +236 @@
-      constructor
-      · intro impossible; cases impossible
-      · intro noStop
-        rw [noStop] at consistent
-        cases consistent
+      exact ⟨fun impossible => by cases impossible, fun noStop => by subst stop; cases consistent⟩
```

### Chain from SourcePruningEnumerationSharedEagerReservation

Start at the exact current repository source pin above.

Snapshot `SourcePruningEnumerationSharedEagerReservation-738aff81.lean`, SHA256 `738aff817191e48776ca46982e6e09547a5e5e626ee34eb7389788464a0bd867`.

```diff
--- SourcePruningEnumerationSharedEagerReservation.lean
+++ SourcePruningEnumerationSharedEagerReservation-738aff81.lean
@@ -222 +222 @@
-  simpa only [heightSame, fallbackPlan, captured, limit, own, eagerFinal] using included
+  simpa only [heightSame] using included
```

Snapshot `SourcePruningEnumerationSharedEagerReservation-7343de11.lean`, SHA256 `7343de112347e9887be32e1f7e105d30477942fab39b72709f7b21a948150ab0`.

```diff
--- SourcePruningEnumerationSharedEagerReservation-738aff81.lean
+++ SourcePruningEnumerationSharedEagerReservation-7343de11.lean
@@ -122,103 +121,0 @@
-
-namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
-open SourceCurrentAllocatedNativeResourceForecast (Le)
-open SourcePruningEnumerationSharedIncomingReservation (Seed advance advance_add)
-open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
-open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
-local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
-
-private theorem fallbackPlan_le_nodePlan (limit own height bound ceiling : Nat)
-    (continuation : Nat → Seed → Seed)
-    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
-    Le (fallbackPlan bound ceiling continuation seed).2
-      (nodePlan limit own height bound ceiling continuation seed).2 ∧
-    (fallbackPlan bound ceiling continuation seed).1 ⊆
-      (nodePlan limit own height bound ceiling continuation seed).1 := by
-  cases height with
-  | zero => exact ⟨Le.refl _, fun _ member => member⟩
-  | succ height =>
-      exact iterate_ge (fun current => tuplePlan (nodePlan limit own height)
-          limit (bound + own) ceiling continuation current)
-        (fun current => tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
-          limit (bound + own) ceiling continuation growth current)
-        (fallbackPlan bound ceiling continuation seed) limit
-
-private theorem first_callback_le_tuple
-    (depth limit own height count bound ceiling : Nat) (seed : Seed) :
-    let done := fun retained current => eagerFinal depth current retained
-    let entry := advance seed (count * (bound + 1))
-    let first := eagerFinal depth entry (ceiling + count * bound)
-    let whole := tuplePlan (nodePlan limit own height) count bound ceiling done seed
-    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
-  dsimp only
-  induction count generalizing ceiling seed with
-  | zero =>
-      simp only [Nat.zero_mul, Nat.add_zero, advance, tuplePlan]
-      exact ⟨Le.refl _, fun _ member => member⟩
-  | succ count ih =>
-      let child := nodePlan limit own height
-      let done := fun retained current => eagerFinal depth current retained
-      let tail := fun retained current => tuplePlan child count bound retained done current
-      have doneGrowth := fun retained current => eagerFinal_ge depth current retained
-      have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
-          current.1 ⊆ (tail retained current).1 := by
-        intro retained current
-        exact tuplePlan_ge child (nodePlan_ge limit own height)
-          count bound retained done doneGrowth current
-      have first := ih (ceiling + bound) (advance seed (bound + 1))
-      have later := fallbackPlan_le_nodePlan limit own height bound ceiling tail tailGrowth seed
-      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by
-        rw [Nat.succ_mul]
-        omega
-      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by
-        rw [Nat.succ_mul]
-        omega
-      rw [counts, advance_add, masses]
-      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩
-
-private theorem first_row_callback_le_node (depth limit own height bound ceiling : Nat)
-    (seed : Seed) (positive : 0 < limit) :
-    let done := fun retained current => eagerFinal depth current retained
-    let start := fallbackPlan bound ceiling done seed
-    let first := eagerFinal depth (advance start (limit * (bound + own + 1)))
-      (ceiling + limit * (bound + own))
-    let whole := nodePlan limit own (height + 1) bound ceiling done seed
-    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
-  dsimp only
-  let done := fun retained current => eagerFinal depth current retained
-  let start := fallbackPlan bound ceiling done seed
-  let row := fun current => tuplePlan (nodePlan limit own height)
-    limit (bound + own) ceiling done current
-  have first := first_callback_le_tuple depth limit own height limit (bound + own) ceiling start
-  have growth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
-    intro current
-    exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
-      limit (bound + own) ceiling done (fun retained reached => eagerFinal_ge depth reached retained) current
-  have later : Le (row start).2 (iterate row start limit).2 ∧
-      (row start).1 ⊆ (iterate row start limit).1 := by
-    obtain ⟨count, same⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
-    rw [same]
-    exact iterate_ge row growth (row start) count
-  exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩
-
-/-- The first row contains its own padded callback after its planned child slots. -/
-theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
-    (positive : 0 < scalar (preparedSeed seed).2) :
-    let captured := preparedSeed seed
-    let N := scalar captured.2
-    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
-    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
-    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
-    let whole := eagerFinal (depth + 1) seed ceiling
-    Le first.2 whole.2 ∧ first.1 ⊆ whole.1 := by
-  let captured := preparedSeed seed
-  let limit := scalar captured.2
-  let own := SourcePruningEnumerationGuardWidth.width captured.1
-  have currentPositive : 0 < limit := positive
-  obtain ⟨height, same⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt currentPositive)
-  have included := first_row_callback_le_node depth limit own height ceiling ceiling captured currentPositive
-  have heightSame : height + 1 = limit := same.symm
-  simpa only [heightSame] using included
-
-end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
```

### Chain from SourcePruningEnumerationSharedEagerCapturedBounds

Start at the exact current repository source pin above.

Snapshot `SourcePruningEnumerationSharedEagerCapturedBounds-dac2c602.lean`, SHA256 `dac2c60271548c55e44ea425a65f00f1e34d5eddafae5dd06449704cf46e7f82`.

```diff
--- SourcePruningEnumerationSharedEagerCapturedBounds.lean
+++ SourcePruningEnumerationSharedEagerCapturedBounds-dac2c602.lean
@@ -39,2 +39,2 @@
-    exact Nat.le_trans (SourceCurrentMemoMergeUniformNumeric.height_le_mass value)
-      (Nat.le_trans mass (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2))
+    exact (SourceCurrentMemoMergeUniformNumeric.height_le_mass value).trans
+      (mass.trans (SourceCurrentConstrainedCapTargetForecast.scalar_mass seed.2))
```

## Unverified current-source enumeration width draft

This is preserved next source, not a checked module. It contributes ZERO
public laws to this packet. SHA256 `737c1c72eaf371d8777b7f9f884ff6af5f5ffb81b69a5ca07d8160cabdc6131a`.

```lean
import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
import MicroCFTA.SourcePruningEnumerationSharedPreparedReservation

/-!
# Mathematical enumeration width from current source input

The original source and its deterministic native build select one profile.
The profile reserves the finite shared prepared enumeration at the requested depth.
The same source and build equations identify that exact reservation.
This result does not execute an initializer or worker.
It does not prove capacity at a fixed Haskell machine width.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramEnumerationWidth
open Cache InternedConstructorTemplates
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceSynthesisOriginalSharedRankCompletion (seed)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- The original source input selects the final finite-depth enumeration profile. -/
noncomputable def enumProfile (lib : Library) (query : Query) (signed : Int) (depth : Nat) : Profile :=
  match SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed with
  | .error _ => ⟨0, 0, 0, 0⟩
  | .ok expression =>
      match InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty with
      | .pending _ _ => ⟨0, 0, 0, 0⟩
      | .done _value heap =>
          (SourcePruningEnumerationSharedPreparedReservation.final depth (seed heap) 0).2

/-- The existing roomBits function selects a sufficient mathematical width. -/
noncomputable def enumBits (lib : Library) (query : Query) (signed : Int) (depth : Nat) : Nat :=
  SourceCurrentParentInitialRoom.roomBits (enumProfile lib query signed depth)

/-- The same actual current source and build identify the exact enumeration profile. -/
theorem enumProfile_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    enumProfile lib query signed depth =
      (SourcePruningEnumerationSharedPreparedReservation.final depth (seed heap) 0).2 := by
  simp only [enumProfile, returned, built]

/-- The chosen mathematical width reserves this same build at the requested depth. -/
theorem enum_reserved_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    SourcePruningEnumerationSharedPreparedReservation.Reserved
      (enumBits lib query signed depth) depth (seed heap) 0 := by
  unfold enumBits
  rw [enumProfile_of_build lib query signed expression returned depth value heap built]
  exact SourcePruningEnumerationSharedPreparedReservation.reserved_computed depth (seed heap) 0

end MicroCFTA.SourceSynthesisCurrentProgramEnumerationWidth
```

## Unproved eager induction contracts

# Concrete eager resource induction and its admission boundary
Status: UNPROVED CONTRACT PLAN. No executable worker changes.
Current sufficient arithmetic input: Room bits (eagerFinal d seed ceiling).2.
This is computed entirely from original/current inputs, not future execution fit.
First isolate eagerReserved_of_final_room, rather than assume admission implicitly.

## Exact public worker target
Use ALL current operands/instances/hypotheses of
SourcePruningEnumerationSharedPreparedFiniteResources.run_finite_complete_resources:74-92,
replace its reserved hypothesis by:
  (room : Room bits (eagerFinal recursiveFuel seed ceiling).2).
Its conclusion is exactly:
  ∃ bound outcome,
    (∀ extra, RecursiveChildPolicy.runEager holeKey fits admits graph templates
      checkEmpty edgesOf stop order (bound+extra) recursiveFuel metadata caller
      memos.query before = outcome) ∧
    SharedPreparedRecursive.OutcomeResources formulas solver caller
      (eagerFinal recursiveFuel seed ceiling) outcome.
Aliases above name the existing SourcePruningEnumerationSharedPrepared modules.
No generic continuation, rank, Packet, capacity after execution or child IH is public.
The ENTIRE existing OutcomeResources remains unchanged.

## Private outer IH
For EACH d, generalize ALL metadata/caller/full Memos/inventory/cache/seed/ceiling
and initial Next decision. Current Packet/Fits/guard Heap, selector membership and
length, suspendedBound≤ceiling and Room at the computed final plan derive ONE
stable actual resumeWithChild(eagerChild at same workFuel) execution at depth d.
It returns the SAME OutcomeResources at the actual complete/stopped endpoint.
An arbitrary initial decision is needed because continueWith passes its computed
decision directly. Base decisions none/done/stuck and exhausted expansion are the
actual old zero outcomes. Positive depth performs ONE actual selected prefix and
ONE common preparation; never replay a producer to obtain an unrelated endpoint.

## Private inner height/CPS IH
Fix a captured source heap/profile/alphabet. Current Available source payloads,
Linked/HeapFits/physical Heap derive height/row/arity/tries via CapturedBounds51.
Generalize current native caller/full Memos/cache and both actual CPS consumers.
Current Packet plus current bucket bounds/pending and current Fits/Heap, at a
planned Seed entry with Room, must derive one stable actual eagerChild execution.
The result predicate is OutcomeResources applied to the existing finish uv Fold,
plus the intermediate complete-receipt fields needed by the ACTUAL continuation:
Safe/validity/pending, FragmentBound/PendingFragment/FragmentAvoid, old-root
protection, references/incoming preservation, origins and full native Post/query.
Stopped candidates keep their exact observation/candidate; Safe is not invented.

A PRIVATE consumer contract quantifies current reached cache/caller/full Memos,
fragment and mass ceiling. Given these DERIVED completion fields and Room at
its planned continuation endpoint, it supplies stable execution/resources of
THAT actual consumer at common larger workFuel. Its seed transformer K and
arithmetic reservation predicate are pure. This contract is NOT a public oracle.
It is discharged internally for: tuple [] -> residual finish; parent completion
-> fixed-heap Finalize and recordTypes; then concrete lower-depth outer IH.
For child success the tuple tail is installed immediately as K, not run later.
For ordinary child alternatives, preserve captured cache and native available
payloads while threading the ENTIRE actual native caller/full Memos after K.
Only complete receipts require a completion Packet. Every emitted output,
including stopped-prefix outputs, retains its existing OutputResources predicate.
After complete K, completed_captured_packet restores the captured sibling Packet
at that SAME new native endpoint. Stopped K terminates the remaining scan.

## Tuple and row induction boundaries
Tuple IH carries completed fragments, accumulated fragment bounds/pending/avoid,
original-root protection and the updated branch-local mass ceiling. Its current
Seed is shared across native work. Every head success runs the remaining tuple
inside its actual callback; no tail is collected/replayed. Empty/short tuples
use first_callback_le_tuple for UNUSED planned child-stage padding.
Row IH fixes captured cache/mass/source shape. Completed head+tail+K precedes the
next sibling at its exact caller/full Memos. Row count includes duplicate source
occurrences, using the current global selector-length hypothesis. Unsupported,
rejected, candidateNone, finalizeStopped and callback stops retain full shapes.
consumeSelected prepends inner receipts; finish discards them only on complete,
so intermediate receipts must be observed before that conversion.

## First implemented cut
Copied forecast version retains ALL224 definitions/proofs while the original
candidate stays frozen. New eagerReserved recursively checks ONLY arithmetic
admission at its deterministic planned fallback entries and lower-depth callbacks.
Its private tuple predicate follows the SAME nested continuation placement and
its row predicate uses the SAME iterate entry. It supplies no execution witness.
The first new theorem will derive this entire predicate from original final Room,
using within-plan growth and Room.mono plus existing reserved_of_final_room.
Actual CPS execution, common workFuel and final resource preservation remain open
until the operational inner/outer inductions above are discharged.

## Independent eager scope review

# R257 eager scope review

2026-11-12 23:37 CET. Read-only review of both actual final sources.
CapturedBounds: SourcePruningEnumerationSharedEagerCapturedBounds.lean.
51 lines; SHA256: 8c116a2a1a1ba962fa9045d89498aa5551ef0a228229505bc8edd5b32617eaa9.
Forecast: SourcePruningEnumerationSharedEagerReservation.lean.
224 lines; SHA256: f8bcdd4c5f695c32321e831270ec5703105f4384214a2bf1d0f87c5793610246.
The sole compiler reported strict PASS for their three public laws.
No substantive scope concern found. The earlier noStop review remains valid.

captured_payload_bounds:22 takes ONE captured heap, Linked, HeapFits and
its literal guard-alphabet Heap predicate. It bounds height of values
Available in THAT heap, lengths of its available ordinary rows, resident
edge arities and projected-trie width. It mentions no later heap or run.
The numeric facts about those immutable old payloads remain true. The
law does not assert availability, Fits, Linked or the old guard alphabet
for every record in an arbitrary later heap. Growth can add new records.

The forecast's fallbackPlan, tuplePlan, nodePlan and eagerFinal are
mathematical seed plans. tuplePlan nests its tail inside each child
continuation; nodePlan iterates rows from its fallback seed. These
functions are not an alternative implementation of the eager worker.

eagerFinal_ge:106 proves only numeric-profile Le and alphabet inclusion
from the input seed to its forecast, at every depth and ceiling.
first_row_callback_le_final:206 requires positive prepared scalar N.
It proves inclusion of ONE explicitly padded first-row callback forecast
in the whole forecast. Its rowStart already includes its own fallback
continuation. With b=ceiling+prepared-alphabet width, the callback entry
adds N*(b+1) and its mass argument adds N*b. These are the theorem's OWN
tuple padding terms, not an identified old tupleBudget or executed cost.
The first-row law is not an all-row execution or admission theorem.

Neither module calls an eager worker, proves its result exists, derives
native/UF/cache preservation, gives adequate fuel or recursive depth,
or supplies a machine-capacity reservation. Profile/alphabet growth
alone does not establish actual Fits/Heap at future callback endpoints.
The remaining work must relate actual eager operations to these exact
plan transitions and their current captured-data bounds. The checked
shallow noStop ProgramOutputs theorem supplies no such eager link.

This review changes no source, statement, resource bound or producer.
No build, compiler, Git, Haskell, repository or evidence action was run.

## Unverified eager admission source extension

This extension is UNVERIFIED. It adds ZERO checked laws to this packet.
It defines the planned arithmetic admission predicate and proposes to derive
it from Room at the original computed final profile. It does not prove an
actual eager execution/resource result. Apply this patch to checked224.
Expected379-line SHA256 `d07876368198c985f41d63346642b8998f8f369874d1a2a91df06bc9d0b8a07a`.

```diff
--- SourcePruningEnumerationSharedEagerReservation.lean
+++ eager-admission-d0787636.lean
@@ -224,0 +225,155 @@
+
+namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
+open SourceCurrentAllocatedNativeResourceForecast (Le Room)
+open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
+open SourcePruningEnumerationFiniteReservation (iterate iterate_ge iterate_add)
+open SourcePruningEnumerationSharedPreparedReservation (preparedSeed)
+local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
+
+private def fallbackReserved (bits bound ceiling : Nat)
+    (admitted : Nat → Seed → Prop) (seed : Seed) : Prop :=
+  SourcePruningEnumerationSharedIncomingReservation.Reserved bits seed (bound + 1) ∧
+    admitted (ceiling + bound) (advance seed (bound + 1))
+
+private def tupleReserved
+    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed)
+    (childReserved : Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop) :
+    Nat → Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop
+  | 0, _bound, ceiling, _continuation, admitted, seed => admitted ceiling seed
+  | count + 1, bound, ceiling, continuation, admitted, seed =>
+      childReserved bound ceiling
+        (fun retained current => tuplePlan child count bound retained continuation current)
+        (fun retained current => tupleReserved child childReserved count bound retained continuation admitted current)
+        seed
+
+private def nodeReserved (bits limit own : Nat) :
+    Nat → Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop
+  | 0, bound, ceiling, _continuation, admitted, seed => fallbackReserved bits bound ceiling admitted seed
+  | height + 1, bound, ceiling, continuation, admitted, seed =>
+      let first := fallbackPlan bound ceiling continuation seed
+      let row := fun current => tuplePlan (nodePlan limit own height)
+        limit (bound + own) ceiling continuation current
+      fallbackReserved bits bound ceiling admitted seed ∧
+        ∀ index, index < limit →
+          tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
+            limit (bound + own) ceiling continuation admitted (iterate row first index)
+
+/-- Check native entry admission at every stage of the original ordered plan. -/
+def eagerReserved (bits : Nat) : Nat → Seed → Nat → Prop
+  | 0, _seed, _ceiling => True
+  | depth + 1, seed, ceiling =>
+      let captured := preparedSeed seed
+      let limit := scalar captured.2
+      let own := SourcePruningEnumerationGuardWidth.width captured.1
+      nodeReserved bits limit own limit ceiling ceiling
+        (fun retained current => eagerFinal depth current retained)
+        (fun retained current => eagerReserved bits depth current retained) captured
+
+private theorem iterate_index_le
+    (next : Seed → Seed)
+    (growth : ∀ current, Le current.2 (next current).2 ∧ current.1 ⊆ (next current).1)
+    (seed : Seed) (first last : Nat) (counts : first ≤ last) :
+    Le (iterate next seed first).2 (iterate next seed last).2 ∧
+      (iterate next seed first).1 ⊆ (iterate next seed last).1 := by
+  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le counts
+  rw [iterate_add]
+  exact iterate_ge next growth (iterate next seed first) extra
+
+private theorem fallbackReserved_of_room (bits bound ceiling : Nat)
+    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
+    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
+      current.1 ⊆ (continuation retained current).1)
+    (accepted : ∀ retained current, Room bits (continuation retained current).2 → admitted retained current)
+    (seed : Seed) (room : Room bits (fallbackPlan bound ceiling continuation seed).2) :
+    fallbackReserved bits bound ceiling admitted seed := by
+  have later := growth (ceiling + bound) (advance seed (bound + 1))
+  exact ⟨SourcePruningEnumerationSharedIncomingReservation.reserved_of_final_room
+      bits seed (bound + 1) (room.mono later.1),
+    accepted (ceiling + bound) (advance seed (bound + 1)) room⟩
+
+private theorem tupleReserved_of_room (bits : Nat)
+    (child : Nat → Nat → (Nat → Seed → Seed) → Seed → Seed)
+    (childReserved : Nat → Nat → (Nat → Seed → Seed) → (Nat → Seed → Prop) → Seed → Prop)
+    (childGrowth : ∀ bound ceiling continuation,
+      (∀ retained current, Le current.2 (continuation retained current).2 ∧
+        current.1 ⊆ (continuation retained current).1) →
+      ∀ seed, Le seed.2 (child bound ceiling continuation seed).2 ∧
+        seed.1 ⊆ (child bound ceiling continuation seed).1)
+    (childRoom : ∀ bound ceiling continuation admitted,
+      (∀ retained current, Le current.2 (continuation retained current).2 ∧
+        current.1 ⊆ (continuation retained current).1) →
+      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
+      ∀ seed, Room bits (child bound ceiling continuation seed).2 →
+        childReserved bound ceiling continuation admitted seed)
+    (count : Nat) :
+    ∀ bound ceiling continuation admitted,
+      (∀ retained current, Le current.2 (continuation retained current).2 ∧
+        current.1 ⊆ (continuation retained current).1) →
+      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
+      ∀ seed, Room bits (tuplePlan child count bound ceiling continuation seed).2 →
+        tupleReserved child childReserved count bound ceiling continuation admitted seed := by
+  induction count with
+  | zero =>
+      intro bound ceiling continuation admitted growth accepted seed room
+      exact accepted ceiling seed room
+  | succ count ih =>
+      intro bound ceiling continuation admitted growth accepted seed room
+      exact childRoom bound ceiling
+        (fun retained current => tuplePlan child count bound retained continuation current)
+        (fun retained current => tupleReserved child childReserved count bound retained continuation admitted current)
+        (fun retained current => tuplePlan_ge child childGrowth count bound retained continuation growth current)
+        (fun retained current covered => ih bound retained continuation admitted growth accepted current covered)
+        seed room
+
+private theorem nodeReserved_of_room (bits limit own height : Nat) :
+    ∀ bound ceiling continuation admitted,
+      (∀ retained current, Le current.2 (continuation retained current).2 ∧
+        current.1 ⊆ (continuation retained current).1) →
+      (∀ retained current, Room bits (continuation retained current).2 → admitted retained current) →
+      ∀ seed, Room bits (nodePlan limit own height bound ceiling continuation seed).2 →
+        nodeReserved bits limit own height bound ceiling continuation admitted seed := by
+  induction height with
+  | zero =>
+      intro bound ceiling continuation admitted growth accepted seed room
+      exact fallbackReserved_of_room bits bound ceiling continuation admitted growth accepted seed room
+  | succ height ih =>
+      intro bound ceiling continuation admitted growth accepted seed room
+      let first := fallbackPlan bound ceiling continuation seed
+      let row := fun current => tuplePlan (nodePlan limit own height)
+        limit (bound + own) ceiling continuation current
+      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
+        intro current
+        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
+          limit (bound + own) ceiling continuation growth current
+      have firstBelow := iterate_ge row rowGrowth first limit
+      constructor
+      · exact fallbackReserved_of_room bits bound ceiling continuation admitted growth accepted seed
+          (room.mono firstBelow.1)
+      · intro index less
+        have below := iterate_index_le row rowGrowth first (index + 1) limit (by omega)
+        have nextEntry : iterate row first (index + 1) = row (iterate row first index) := by
+          rw [iterate_add]
+          rfl
+        rw [nextEntry] at below
+        have rowRoom : Room bits (row (iterate row first index)).2 := room.mono below.1
+        exact tupleReserved_of_room bits (nodePlan limit own height) (nodeReserved bits limit own height)
+          (nodePlan_ge limit own height) ih limit (bound + own) ceiling continuation admitted growth accepted
+          (iterate row first index) rowRoom
+
+/-- Room at the computed original plan supplies every planned query entry. -/
+theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
+    (room : Room bits (eagerFinal depth seed ceiling).2) :
+    eagerReserved bits depth seed ceiling := by
+  induction depth generalizing seed ceiling with
+  | zero => trivial
+  | succ depth ih =>
+      let captured := preparedSeed seed
+      let limit := scalar captured.2
+      let own := SourcePruningEnumerationGuardWidth.width captured.1
+      exact nodeReserved_of_room bits limit own limit ceiling ceiling
+        (fun retained current => eagerFinal depth current retained)
+        (fun retained current => eagerReserved bits depth current retained)
+        (fun retained current => eagerFinal_ge depth current retained)
+        (fun retained current covered => ih current retained covered) captured room
+
+end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
```
