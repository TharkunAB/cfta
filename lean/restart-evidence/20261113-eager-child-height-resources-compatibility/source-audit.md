# Actual eager child-height resources and one private backward callback

Base: 1723ff7dcbd07f42ddd0c908fbb3298333cce3c1.
Main: e53852064d3ef5a2eafec47d754c27504b11de5f, fetched unchanged at 2026-11-13 02:16 CET.
One existing module contains 2053 lines and three public laws. All three public
laws are inherited arithmetic results. ZERO public resource or semantic laws are
added. All old statements, proofs and execution definitions remain unchanged.
The full public runEager_finite_complete_resources target remains UNPROVED and
undeclared. Actual outer-depth and concrete continuation closure remain open.

The live PRIVATE proof closes actual child height. Pointwise congruence uses only
members of the actual prepared child list. The existing prepared_child_lt law
proves that the actual guarded eager branch takes its eager arm on those children.
The actual ordered scan then composes every child alternative with its remaining
tuple and callback. Strong height induction closes the PRIVATE lower-height child
hypothesis. The non-ordinary branch uses the actual fallback receipt and its
inclusion in the same deterministic node plan. Current captured row/arity/projected
limits and actual selector members/count remain the source facts. A pure initial
fallback allowance pads the ordinary start; it performs no native operation.
The proof retains same callers, complete Memos, Fold and OutcomeResources under
PRIVATE concrete consumers. Those consumers must still be closed by outer depth.
The public target has no added future child/Packet/consumer/model supplier.

The first height check accepted the substantive node/fallback/congruence code but
left four impossible non-node classifier branches. Standard Bool simplification
closes those four contradictions. Only the four local simp tactics change. No
statement, worker, plan, global option, heartbeat or linter setting changes.
Both the failed2053 and repaired checked2053 remain reconstructible below.

An independent PRIVATE semantic callback composition also passes. It uses the
actual false recordTypes callback and the SAME concrete shared resume-tail IH.
The existing continue_recorded and recordTypes_success_semantics laws imply the
same output backward-model property at the pre-callback caller/cache. It creates
no output, producer, model or full history. The first73-line draft omitted the
existing literal emitted definition; one explicit SharedPreparedLiveRoot import
repairs it. This source is a checked branch under its PRIVATE tail IH. It does
not prove a whole shared run restores original-source meaning. Shared boundary
retention, original-source history and satisfying finite Type models remain open.

The strongest whole-path contracts remain cold SHALLOW current-input Program
outputs and exact original-source language at the completed nodeCall endpoint.
Full eager resources/roles, adequate depth/output existence, total work/host word
capacity, stream order and multiplicity, both inverses and Haskell correspondence
remain separate. No Haskell source changed. External Liquid repeated-name/refinement
repair ownership remains unchanged. No Haskell tests are repeated for this Lean change.

## Exact inherited public declarations

Source SHA256 `c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165`.

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

```lean
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling
```

## Replayed height source history

Start from registered checked2053. Apply these reverse patches in order.
Each patch was applied with GNU patch --output and matched exact target bytes.
All earlier stages remain in the preceding checkpoint.

```json
[
  {
    "stage": "checked1888",
    "lines": 1888,
    "source_sha256": "189d72cbd7d6d346d6a85355f50acf1c160e958a4ddd5e4c819c962c6c7ba6d7",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "failed2053",
    "lines": 2053,
    "source_sha256": "3aa3e899bf6d50cc38835f630ce85d9a733d9cc1c5270cef0529faef400b3036",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "checked2053",
    "lines": 2053,
    "source_sha256": "c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165",
    "compiler_exit": 0,
    "new_public_laws": 0
  }
]
```

### checked2053 to failed2053

```diff
--- checked2053.lean
+++ failed2053.lean
@@ -1985,4 +1985,4 @@
-        | empty => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | reference name => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | union entry members depth free => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | mu entry body depth payload => simp [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
+        | empty => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
+        | reference name => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
+        | union entry members depth free => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
+        | mu entry body depth payload => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
```

### failed2053 to checked1888

```diff
--- failed2053.lean
+++ checked1888.lean
@@ -1888,165 +1887,0 @@
-section ActualVisitorCongruence
-
-private theorem children_members_congr (left right : Visitor) (inputs : List (Node × List Suspended)) :
-    (∀ child bucket, (child, bucket) ∈ inputs → ∀ caller before queries done stopped,
-      left bucket child caller before queries done stopped = right bucket child caller before queries done stopped) →
-    ∀ done stopped caller before queries,
-      SourcePruningEnumerationSharedChildVisitors.visitChildren left done stopped inputs caller before queries =
-        SourcePruningEnumerationSharedChildVisitors.visitChildren right done stopped inputs caller before queries := by
-  induction inputs with
-  | nil => intro _ _ _ _ _ _; rfl
-  | cons input rest ih =>
-      rcases input with ⟨child, bucket⟩
-      intro same done stopped caller before queries
-      simp only [SourcePruningEnumerationSharedChildVisitors.visitChildren]
-      rw [same child bucket (by simp)]
-      apply congrArg (fun yes => right bucket child caller before queries yes
-        (fun observation candidate => stopped [] observation candidate))
-      funext fragment reached saved after
-      exact ih (fun value retained member => same value retained (List.mem_cons_of_mem _ member))
-        (fun fragments => done (fragment :: fragments))
-        (fun completed => stopped (fragment :: completed)) reached after saved
-
-private theorem scan_members_congr
-    (left right : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold)
-    (before : Cached) (rows : List (EdgeValue Symbol Constraint))
-    (same : ∀ edge ∈ rows, ∀ caller queries, left edge caller queries before = right edge caller queries before)
-    (caller : Caller (bits + 2)) (queries : Queries) :
-    SourcePruningEnumerationSharedBranching.scan left before rows caller queries =
-      SourcePruningEnumerationSharedBranching.scan right before rows caller queries := by
-  induction rows generalizing caller queries with
-  | nil => rfl
-  | cons edge rest ih =>
-      simp only [SourcePruningEnumerationSharedBranching.scan, same edge List.mem_cons_self caller queries]
-      cases observed : right edge caller queries before with
-      | stopped processed outputs current => rfl
-      | complete processed outputs reached saved =>
-          simp only [ih (fun chosen member => same chosen (List.mem_cons_of_mem _ member)) reached saved]
-
-end ActualVisitorCongruence
-
-section ActualPreparedGuard
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem selected_guarded_eq
-    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
-    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
-    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows) (scs : List Suspended)
-    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
-    (consume : SelectedEdge.Result (bits + 2) → Fold) :
-    SourcePruningEnumerationSharedChildVisitors.visitSelected
-      (fun bucket child current cache memos yes no =>
-        if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry rows depth free) then
-          SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
-            bucket child current cache memos yes no
-        else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k
-          bucket child current cache memos yes no)
-      consume scs edge caller before queries =
-    SourcePruningEnumerationSharedChildVisitors.visitSelected
-      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf)
-      consume scs edge caller before queries := by
-  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
-  | none => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
-  | some results =>
-      cases results with
-      | nil => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
-      | cons first rest =>
-          cases rest with
-          | cons second rest => simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
-          | nil =>
-              rcases first with ⟨⟨symbol, staged, residual⟩, middle⟩
-              simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected, prepared]
-              apply children_members_congr
-              intro child bucket member current cache memos yes no
-              obtain ⟨_tries, _projected, _inputs, lower⟩ := SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
-                caller.checked.native.machine.heap parentEntry rows depth free edge selected scs before middle
-                symbol staged residual prepared child bucket member
-              exact dite_eq_left lower
-
-end ActualPreparedGuard
-
-section ActualHeightResources
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_child_height_complete
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
-    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver := by
-  induction height with
-  | zero => exact eager_child_height_zero_complete checkEmpty edgesOf captured limit own formulas solver
-  | succ height ih =>
-      intro inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
-        packet fits known available kept closed bounded pending mass bucketBound ranked shapes selectionMembers selectionLength
-        reserved growth consumers
-      by_cases ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = true
-      · cases incoming with
-        | empty => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | reference name => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | union entry members depth free => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | mu entry body depth payload => simp only [SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal] at ordinary
-        | node entry rows depth free =>
-            let first := fallbackPlan bound ceiling continuation seed
-            have initial := fallbackPlan_ge bound ceiling continuation growth seed
-            have firstFits : Fits first.2 caller.checked := fits.mono initial.1
-            have firstKnown : Heap (fun guard => guard ∈ first.1) caller.checked.native.machine.heap := by
-              intro key edge found
-              exact initial.2 (known key edge found)
-            have alternativesLength : (edgesOf (.node entry rows depth free)).length ≤ limit :=
-              Nat.le_trans (selectionLength entry rows depth free) (shapes entry rows depth free available).1
-            have rowsComplete := eager_rows_complete_of_child (Typing := Typing) (bits := bits)
-              checkEmpty edgesOf captured limit own height formulas solver ih limit
-            obtain ⟨fuel, outcome, running, resources⟩ := rowsComplete inventory caller memos metadata before first
-              bound ceiling bucket uv continuation admitted done stopped packet firstFits firstKnown kept mass bucketBound
-              entry rows depth free available closed ranked bounded pending (edgesOf (.node entry rows depth free))
-              alternativesLength (selectionMembers entry rows depth free) shapes selectionMembers selectionLength reserved.2 growth consumers
-            refine ⟨fuel, outcome, ?_, resources⟩
-            intro extra
-            let work := fuel + extra
-            let full : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
-              fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
-                (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
-                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
-                bucket edge reached cached saved
-            let guarded : EdgeValue Symbol Constraint → Caller (bits + 2) → Queries → Cached → Fold :=
-              fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
-                (fun inherited child current cache memos yes no =>
-                  if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) then
-                    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf
-                      inherited child current cache memos yes no
-                  else SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty work work work work work
-                    inherited child current cache memos yes no)
-                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
-                bucket edge reached cached saved
-            have same : SourcePruningEnumerationSharedBranching.scan guarded before
-                (edgesOf (.node entry rows depth free)) caller memos.query =
-                SourcePruningEnumerationSharedBranching.scan full before
-                  (edgesOf (.node entry rows depth free)) caller memos.query := by
-              apply scan_members_congr
-              intro edge member reached saved
-              exact selected_guarded_eq checkEmpty work work work work work edgesOf entry rows depth free
-                edge (selectionMembers entry rows depth free edge member) bucket reached before saved
-                (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done work) reached saved)
-            have sourceRun := SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary checkEmpty
-              work work work work work edgesOf bucket (.node entry rows depth free) caller before memos.query
-              (done work) (stopped work) ordinary
-            exact sourceRun.trans (same.trans (running extra))
-      · have fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false := by
-          cases classified : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming with
-          | false => rfl
-          | true => exact (ordinary classified).elim
-        obtain ⟨fuel, outcome, running, resources⟩ := eager_fallback_resources seed bound ceiling continuation admitted
-          formulas solver inventory caller memos metadata before checkEmpty edgesOf bucket incoming uv done stopped packet
-          bounded pending (kept.available incoming available) closed fits known mass bucketBound
-          (nodeReserved_fallback bits limit own (height + 1) bound ceiling continuation admitted seed reserved) fallback
-          (fun fragment reached saved after data fitted supported afterMass accepted =>
-            consumers.1 fragment reached saved after data (advance seed (bound + 1)) (ceiling + bound)
-              fitted supported afterMass accepted)
-          (fun reached saved after outer waiting next final post query fitted supported accepted =>
-            consumers.2 reached saved after outer waiting next final post query (advance seed (bound + 1)) (ceiling + bound)
-              fitted supported accepted)
-        have included := fallbackPlan_le_nodePlan limit own (height + 1) bound ceiling continuation growth seed
-        exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
-end ActualHeightResources
-
```

## Checked private callback branch

Copy this exact74-line source to a Lean file to reproduce the isolated check.
The source is not a new public theorem or a whole-run producer.

SHA256 `b50984f92782293752e8b1dc05aa6c19ab10706c55a3c9ab9fde0e5cb68fde0a`.

```lean
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
import MicroCFTA.SourcePruningEnumerationObservedFramesLanguage

/-!
# A backward step at the actual shared callback

The same actual false callback supplies its core before the same resume.
The smaller-depth semantic hypothesis is private and refers to that resume.
This step constructs no history, assignment, output or resource producer.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}

private def OutputBackward
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller width) (before : Cached) (output : Output width Typing) : Prop :=
  ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
    Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient output.caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment output.cache.core →
    Satisfies (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
      (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
      assignment before.core

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem recorded_callback_backward
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel depth : Nat) (metadata updated : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (observed : Core) (output : Output width Typing)
    (total : UnionFind.Total before.core.representatives)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata uv (.inl fragment) before.core) = [.ok ((false, updated), observed)])
    (tail : output ∈ emitted (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller memos.query (EnumerationExpandableIndex.frame observed before)
        (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame observed before))) →
      OutputBackward formulas solver caller (EnumerationExpandableIndex.frame observed before) output)
    (member : output ∈ emitted (continueWith
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
      graph templates stop order workFuel metadata uv fragment caller memos.query before)) :
    OutputBackward formulas solver caller before output
    := by
  have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
      (.inl fragment)) before.core (false, updated) observed := by
    rw [Success, recorded]
    exact List.mem_singleton_self _
  rw [continue_recorded (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
    graph templates stop order workFuel metadata updated uv fragment caller memos.query before observed recorded] at member
  intro ambient assignment satisfied
  have afterSatisfied := tail member ambient assignment satisfied
  exact (SourcePruningRecordTypes.recordTypes_success_semantics graph templates workFuel metadata uv (.inl fragment)
    before.core observed (false, updated) total callbackSuccess
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient caller.checked.native.machine.heap)
    (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true) assignment).mp afterSatisfied

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
```

### checkedCallback74 to failedCallback73

```diff
--- checkedCallback74.lean
+++ failedCallback73.lean
@@ -1 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
```

```json
[
  {
    "from": "checked2053",
    "to": "failed2053",
    "from_sha256": "c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165",
    "to_sha256": "3aa3e899bf6d50cc38835f630ce85d9a733d9cc1c5270cef0529faef400b3036",
    "patch_sha256": "107d698f34b2373108a2cb427ecad365061f9d90a7e47c28a92a352987949062",
    "replayed_exact": true
  },
  {
    "from": "failed2053",
    "to": "checked1888",
    "from_sha256": "3aa3e899bf6d50cc38835f630ce85d9a733d9cc1c5270cef0529faef400b3036",
    "to_sha256": "189d72cbd7d6d346d6a85355f50acf1c160e958a4ddd5e4c819c962c6c7ba6d7",
    "patch_sha256": "88a1cbc0a40033b56f352800bc124bb5da0d9b69336f4638e85222ac77e3c6ae",
    "replayed_exact": true
  },
  {
    "from": "checkedCallback74",
    "to": "failedCallback73",
    "from_sha256": "b50984f92782293752e8b1dc05aa6c19ab10706c55a3c9ab9fde0e5cb68fde0a",
    "to_sha256": "7e9cc866380efe9c70fe50c0b5a76e9e3a7c9b4acae792791dad609214cb7193",
    "patch_sha256": "6042aabc9a0bb45e83130f7eb0a19bd18dd3a1c1f53e24f9b7f3a56ac1a0c9f2",
    "replayed_exact": true
  }
]
```

## Frozen artifact: eager-height-zero-stage-note.md

SHA256 `81ecaa044f3eb33596a45e9623cb03942745595b85db1769f96147f56ccf0506`. The note describes its stated stage.
The later exact strict results and local repairs appear above.

```text
# Actual eager height-zero CPS base
Status: UNCOMPILED PRIVATE SEGMENT. The public eager resource target is UNPROVED.
Source eager-cps-height-zero-stage.lean,1267 lines. SHA256 8f5b35234a38d083b898ad890c8ff6b8013e16ce32a9ab994bb805712872d319.
Exact checked1179/dc0a4f85 source retained except final namespace closing line.
87L private fragment95fd2e20 is appended. All earlier snapshots remain immutable.

ChildConsumers records a PRIVATE certified continuation family at current
fragment inputs/full native-Memos endpoints and computed native entries.
EagerChildComplete is the PRIVATE height-IH target over CURRENT captured
availability/Keeps, current shapes derived by captured_payload_bounds, current
Packet/Fits/Heap/mass/bucket/selection and nodeReserved. It changes no worker.
The height-zero base derives ordinaryNonterminal=false internally and applies
ONE checked actual fallback resource proof. It retains exact whole actual Fold,
common stable fuel and ENTIRE OutcomeResources of nodePlan height0.

IMPORTANT: this candidate proves ONLY the height-zero base. The current private
ChildInputs/TupleInputs universal ReferencesAllowed field may be too strong
for ordinary own-class allocations. The positive-height proof needs a reviewed
PRIVATE future-variable allowance condition; no positive-height law or general
resource claim is made. All checked prior fields remain valid within their
proved scopes. No Haskell/production defect or reproduced counterexample is
claimed. Public20L runEager target is unchanged and has no new provider/gate.
No compiler/Git/repository/Haskell/checkpoint source was changed.
```

## Frozen artifact: eager-cps-height-resources-stage-note.md

SHA256 `8fc034bf4c8462650e777fcab9f4e312a05b23836c83f27a4b290cee9eecc613`. The note describes its stated stage.
The later exact strict results and local repairs appear above.

```text
# Actual eager child height induction

Status at 2026-11-13 02:08 CET: UNCOMPILED candidate. ROOT is the sole compiler.
Source: `eager-cps-height-resources-stage.lean`, 2053 lines.
SHA256: `3aa3e899bf6d50cc38835f630ce85d9a733d9cc1c5270cef0529faef400b3036`.

The source appends80 lines of pure visitor congruence and83 lines of
height induction to ROOT's exact checked1888/189d72cb.
The exact5-line private height header has SHA11deacdc.
It adds no import, public provider, worker or arithmetic definition.
All prior snapshots remain unchanged.

The actual prepare receipt supplies strict rank for every reached payload child.
The full selected operation therefore uses the eager branch of its existing guard.
The congruence proof retains the full Fold and all callback endpoints.
It covers rejected arity and unsupported preparation without additional assumptions.

The child proof inducts on the current ordinary height budget.
The ordinary case uses the checked ordered row producer and the lower-height IH.
It derives row count from the captured native payload and current selector facts.
It derives the initial row seed from the same fallback-plan growth.
The nonordinary case uses the actual fallback producer and within-plan inclusion.
The result retains the entire actual Fold and OutcomeResources.

The private consumer certificate remains part of EagerChildComplete.
The outer recursive-depth proof must discharge it for the actual continuation.
The public20-line runEager resource target remains undeclared and unproved.
No new public eager resource law is claimed.
```

## Frozen artifact: shared-backward-source-next.md

SHA256 `2f09b7e3af8f50703b14b43e4f791bf02e8042dc0b6c377766be3608dbf3f30e`. The note describes its stated stage.
The later exact strict results and local repairs appear above.

```text
# Shared backward source meaning: one private callback step

2026-11-13 02:08 CET. Runtime-only source audit and private draft.
No compiler, Git, repository, Haskell, root documentation or evidence changes.
The current original-input producer remains CurrentProgramOutputs.accepted:50.
It calls the SAME initializer and worker once. Its full187 receipt stays intact.
A native endpoint equality does not identify an execution history.

Frozen draft: SourceSynthesisSharedPreparedBackwardCallback.lean73L.
SHA256: 7e9cc866380efe9c70fe50c0b5a76e9e3a7c9b4acae792791dad609214cb7193.
Private recorded_callback_backward header19L SHA256:
cdb267f3dd3c55652d73908389293cf7da3d2f4d5884e44e8570e2100635ff77.
Private OutputBackward observer12L SHA256:
e92ec60a3fdbb74295bebc6bc1b3d3556f2c6f729fc42629ab1a3d54d872934c.
Status: unverified draft. Zero public laws. No worker or producer was added.

Exact local reuse (all paths below are lean/MicroCFTA/*.lean):
- PrefixLanguage:31 PrefixMeaning and :195 prefix_semantics apply to the SAME
  SelectedStep.runPrefix used by shared resume. Narrowed inputs restore the
  original model. Parked inputs restore it ONLY together with the removed scs.
- SelectedPreparationResources:53-62 and SelectedPreparationIdentification:55-64
  retain decoded/prepared meaning and model equivalence at the SAME entry/heap.
  SharedPreparedBranchModels.complete_models_resources:47 uses that preparation.
- SharedChildStableNeutral.stable_neutral_semantics:34 and
  SharedTraversalStableResourceNeutral.stable_complete_neutral_semantics_resources:60
  give actual shared neutral-model equivalences at stable observed endpoints.
  They retain the EFFECTIVE bucket. Nonterminal non-node boundaries retain [].
- SharedSelectedEdgeNeutralResourceSoundness:35
  stable_complete_neutral_sound_current_resources restores actual edge meaning
  with inherited-validity, fresh-arity and per-child retained-bucket conditions.
- FinalizeLanguage.written_semantics:19 restores a neutralized target plus the
  SAME fragment/target equation. It does not restore the old slot by itself.
- SharedPreparedOpaqueLanguage.stable_complete_sound_retained_resources:172
  restores the original stored value from the actual completed dispatch and
  actual preparation equivalence. Its retained-bucket condition is necessary.
- ObservedFramesLanguage.recordTypes_success_semantics:66 is the callback iff.
  SharedPreparedRecursive.continue_recorded:91 identifies the ACTUAL false restart.
- Post.arity_before at PreparedHistoryBackwardArity:40 is generic Post transport.
  It can reflect reached arity without casting a nonshared ResourceHistory.

First new draft step:
recorded_callback_backward consumes the exact singleton false callback and
membership of ONE fixed output in its actual shared continueWith. Its PRIVATE
tail IH names the concrete SAME shared resume, work fuel/depth, returned metadata,
caller, full input Memos.query and callback frame. It is not an arbitrary recur.
continue_recorded transports that membership. recordTypes_success_semantics
restores the SAME assignment at the unchanged callback native heap.
Total representatives come from the current packet's safe.1.total.
No recursive result, model or history is asserted by this helper. The tail IH
must be discharged inside the actual smaller-depth proof; it is never public.
The head/tail resource Post and full Memos remain in the EXISTING producer tuple.

Exact next private history/semantic fields are frozen separately in
shared-backward-private-ih-fields.txt (SHA256 bc4e56d44fc6eea7071f38c3651b40f3254f764565e470267a694dc4ab3ba08c).
They append per-output isolated-boundary retention AND conditional OutputBackward
at the same outcome. Keep all original stable work/resource/role/readback fields
and their complete native Posts/Memos. Do not select a second bound or endpoint.
Canonical and actual-next conditions belong to the current derived input context.
The semantic field alone is insufficient: dropped boundary restrictions need the
isolated-boundary field to exclude the corresponding discharged-output branches.

The NONSHARED construction is a guide, not a cast:
PreparedFiniteHistoryContract.ResourceHistory:123 records exact prefix, entry,
head receipt, callback and smaller-depth tail; CompleteWithHistory:211 retains
ALL old resources and adds histories at the SAME common work bound/outcome.
PreparedFiniteHistoryResources.finite_complete_with_history:30 discharges its IH.
Its run_finite_complete_resources_with_history:51 is the concrete old producer.
PreparedResourceHistoryLanguage.ResourceHistory.sound:49 consumes that history,
actualNext, Canonical before, SAME final arity heap and SAME final Discharged.
Its operational missing premises come from PreparedDischargedRetention:33,
PreparedOpaqueHistoryAttachment:29 and PreparedParkedMarkerAttachment:51.
Those last three require NONSHARED recorded tails. No shared replacement was found.
Their selected/captured/opaque constants and reservation histories cannot be
identified by output Program, native endpoint equality or Result field shape.

The first remaining whole-run task is to derive those shared retained/isolated
facts from actual captured child receipts, callback frames, and ordered siblings.
Use SAME stable actual observations and current full Memos; preserve stopped
prefix outputs. Original output resources and ProgramSlots contain no such
history. Do not add a public retained/history/model/source acceptance provider.
This is independent of satisfiability: backward meaning preserves an already
supplied SAME assignment. It does not produce one. done/metadata=None/Program
roles imply neither WHOLE Discharged nor checked residuals nor a ground model.
After shared history is closed, a discharged checked concrete render could feed
its assignment backwards into the SAME startup/root and SAME source build.
Ordinary source typing would then apply to that SAME projected Program.
Unconditional current default/eager output typing and model existence stay open.

Current source SHA256 pins:
SourceSynthesisCurrentProgramOutputs: b8985a4833b09135d069c361a7423d677311f504d6402fb104b3b36a5edbb197.
SourcePruningEnumerationSharedPreparedRecursive: 64b128f0d7d07d9a8a1f75fe30ab2d6166d363cdd1ac2db223305720a48d43e7.
SourcePruningEnumerationObservedFramesLanguage: 6075f53145f2445e053c777fe16734b113e71bc576ab47090610f6ba38468553.
SourcePruningEnumerationPrefixLanguage: 9bc134f0705bd4cca46146dea704a5f0af005d8aa83a7a9f2800ec4a9ac78862.
SourcePruningEnumerationSharedSelectedEdgeNeutralResourceSoundness: 8560607780db1691b4e21d18e21dfe7e5909422bf3fcf4c45a80f6e0a74bb91a.
SourcePruningEnumerationSharedPreparedOpaqueLanguage: 8799584781446f27eb0c764361686335c04d1f975b7ca14d41b86f8957b4210c.
SourcePruningEnumerationPreparedResourceHistoryLanguage: 0b40d57b4d2e3cbaaeb531324b3c7e3f0ec2fc43439f294d8680bcff287dc965.
```

## Frozen artifact: shared-backward-callback-header.txt

SHA256 `cdb267f3dd3c55652d73908389293cf7da3d2f4d5884e44e8570e2100635ff77`. The note describes its stated stage.
The later exact strict results and local repairs appear above.

```text
private theorem recorded_callback_backward
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel depth : Nat) (metadata updated : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (memos : Memos) (before : Cached) (observed : Core) (output : Output width Typing)
    (total : UnionFind.Total before.core.representatives)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata uv (.inl fragment) before.core) = [.ok ((false, updated), observed)])
    (tail : output ∈ emitted (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
        updated caller memos.query (EnumerationExpandableIndex.frame observed before)
        (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame observed before))) →
      OutputBackward formulas solver caller (EnumerationExpandableIndex.frame observed before) output)
    (member : output ∈ emitted (continueWith
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth)
      graph templates stop order workFuel metadata uv fragment caller memos.query before)) :
    OutputBackward formulas solver caller before output
```

## Reproduce

The current2053 source is regular Lean. Its own portable packet checks all three
inherited public laws and standard axioms. Reconstruct earlier stages with the
exact reverse patches. Check private callback74 under the same serial4GiB cap:

```sh
nix-shell ../shell.nix --run "lake env lean -j1 -DwarningAsError=true /tmp/callback74.lean"
```

No execution archive is required.
