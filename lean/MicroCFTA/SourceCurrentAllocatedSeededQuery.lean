import MicroCFTA.SourceCurrentAllocatedGateFields
import MicroCFTA.SourceCurrentAllocatedConjunctionMemo
import MicroCFTA.SourceCurrentAllocatedNativeTraceEffects
import MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion
import MicroCFTA.SourceEqualityProjectionAPI

/-!
# Actual checked first-seeded refused-class queries

Projection retains the current equality operations and native tables.
The fold projects its head, completes its tail, then executes the checked
native request. The first source operand is the final fold seed.

Reached word checks derive finite physical completion and closed results.
The scope proof has no input language model. Exact intersection language
through generated operands still needs an independent contextual adapter.
This completed graph does not establish GHC evaluation order.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededQuery
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

/-- One literal projection advances the same native tables and equality operations. -/
inductive Operand [DecidableEq (EdgeKey Symbol Guard)] (path : List Int)
    (values : List (Value Symbol Guard)) (before : Checked width) :
    Value Symbol Guard → Checked width → Prop where
  | force (result : Value Symbol Guard) (heap : State Symbol Guard)
      (projected : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap) :
      Operand path values before result (advancePhysical before ⟨heap, before.operations⟩)

/-- Source order projects the head before the tail and its final checked request. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) :
    List (List Int) → Checked width → Value Symbol Guard → Checked width → Prop where
  | one (operand : Operand path values before value after) : Fold values [path] before value after
  | cons (operand : Operand path values before value middle)
      (rest : Fold values (next :: paths) middle tail later)
      (native : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain value tail)) later
        (.code (.pure result)) after) :
      Fold values (path :: next :: paths) before result after

/-- Empty input is literal empty. Nonempty input uses the first operand as seed. -/
inductive Seeded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) :
    List (List Int) → Checked width → Value Symbol Guard → Checked width → Prop where
  | nil (before : Checked width) : Seeded values [] before .empty before
  | nonempty (fold : Fold values (rest ++ [seed]) before result after) :
      Seeded values (seed :: rest) before result after

/-- Only actual completed projection and tail prefixes select a native word obligation. -/
inductive FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) : List (List Int) → Checked width → Prop where
  | one : FoldRanges values [path] before
  | cons
      (rest : ∀ value middle, Operand path values before value middle →
        FoldRanges values (next :: paths) middle)
      (native : ∀ value middle tail later,
        Operand path values before value middle → Fold values (next :: paths) middle tail later →
        WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain value tail)) later) :
      FoldRanges values (path :: next :: paths) before

/-- Range plans use the same first-seed rotation as the actual graph. -/
def SeededRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width) : Prop :=
  match paths with
  | [] => True
  | seed :: rest => FoldRanges values (rest ++ [seed]) before

/-- A completed projection has one result and one complete returned checked state. -/
theorem Operand.unique [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before firstAfter secondAfter : Checked width}
    {first second : Value Symbol Guard}
    (left : Operand path values before first firstAfter) (right : Operand path values before second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  cases left with
  | force firstHeap left =>
      cases right with
      | force secondHeap right =>
          obtain ⟨rfl, rfl⟩ := SourceEqualityProjectionAPI.forest_unique left right
          exact ⟨rfl, rfl⟩

private theorem checked_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {A : Type} {firstFuel secondFuel : Nat} {control : Control A}
    {before firstAfter secondAfter : Checked width} {first second : A}
    (left : Trace firstFuel control before (.code (.pure first)) firstAfter)
    (right : Trace secondFuel control before (.code (.pure second)) secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  have firstDone := trace_done firstFuel control before firstAfter first left.steps
  have secondDone := trace_done secondFuel control before secondAfter second right.steps
  have firstStable := done_stable (firstFuel + 1) (secondFuel + 1) control before firstAfter first firstDone
  have secondStable := done_stable (secondFuel + 1) (firstFuel + 1) control before secondAfter second secondDone
  rw [Nat.add_comm (secondFuel + 1) (firstFuel + 1)] at secondStable
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

/-- Different successful bounds retain the same complete fold result and checked state. -/
theorem Fold.unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before firstAfter secondAfter : Checked width} {first second : Value Symbol Guard}
    (left : Fold values paths before first firstAfter) (right : Fold values paths before second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  induction left generalizing second secondAfter with
  | one operand => cases right with
      | one other => exact operand.unique other
  | cons operand rest native ih =>
      cases right with
      | cons other remaining checked =>
          obtain ⟨rfl, rfl⟩ := operand.unique other
          obtain ⟨rfl, rfl⟩ := ih remaining
          exact checked_unique native checked

/-- A seeded query retains the same value and complete checked state at every successful bound. -/
theorem Seeded.unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before firstAfter secondAfter : Checked width} {first second : Value Symbol Guard}
    (left : Seeded values paths before first firstAfter) (right : Seeded values paths before second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  cases left with
  | nil => cases right; exact ⟨rfl, rfl⟩
  | nonempty fold => cases right with
      | nonempty other => exact fold.unique other

/-- Supported projection derives closed availability and retains every current native invariant. -/
theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width)
    (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : PathSupport unconstrained anchor path values) :
    ∃ result after, Operand path values before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  rcases supported with ⟨natural, rfl, supported⟩
  obtain ⟨result, heap, actual, effects, resident, closed⟩ := SourceCurrentAllocatedGateFields.forest_complete
    unconstrained anchor anchorSemantic anchorReady natural values (physical before) ready available growth supported
  refine ⟨result, advancePhysical before ⟨heap, before.operations⟩, .force result heap actual,
    SourceCurrentAllocatedConjunctionMemo.advance_good before _ good effects, ?_,
    SourceCurrentAllocatedQueryMemo.advance_extension before _ effects,
    SourceCurrentAllocatedConjunctionMemo.advance_scoped before _ scopes,
    SourceCurrentAllocatedConjunctionMemo.advance_idle before _ idle, resident, closed⟩
  change Effects (physical before) ⟨heap, before.operations⟩
  exact effects

/-- Reached word checks derive a finite fold without a completed child or final-law premise. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    ∃ result after, Fold values paths before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  induction paths generalizing before with
  | nil => cases ranges
  | cons path paths ih =>
      cases paths with
      | nil =>
          obtain ⟨result, after, actual, effects⟩ := operand_complete unconstrained anchor anchorSemantic anchorReady
            path values before good ready scopes idle available growth (supported path (by simp))
          exact ⟨result, after, .one actual, effects⟩
      | cons next paths =>
          cases ranges with
          | cons rest native =>
              obtain ⟨value, middle, first, middleGood, firstEffects, firstExtension, middleScoped,
                middleIdle, valueAvailable, valueClosed⟩ := operand_complete unconstrained anchor anchorSemantic anchorReady
                  path values before good ready scopes idle available growth (supported path (by simp))
              obtain ⟨tail, later, remaining, laterGood, remainingEffects, remainingExtension, laterScoped,
                laterIdle, tailAvailable, tailClosed⟩ := ih middle (rest value middle first)
                  middleGood firstEffects.ready middleScoped middleIdle
                  (fun value member => firstEffects.keeps.available value (available value member))
                  (grows_trans growth firstEffects.keeps.growth)
                  (fun path member => supported path (List.mem_cons_of_mem _ member))
              have valueLater := remainingEffects.keeps.available value valueAvailable
              have leftOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original value later.native.machine.heap
                laterGood.native.machine.1.coherent valueLater valueClosed
              have rightOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original tail later.native.machine.heap
                laterGood.native.machine.1.coherent tailAvailable tailClosed
              obtain ⟨fuel, result, after, receipt, afterIdle, resultClosed⟩ :=
                SourceCurrentAllocatedNativeScopeCompletion.initial_complete (fun _ _ => true) later laterGood
                  laterScoped remainingEffects.ready.semantic laterIdle value tail leftOriginal rightOriginal
                  valueLater tailAvailable valueClosed tailClosed (native value middle tail later first remaining)
              have checked := SourceCurrentAllocatedNativeTraceEffects.effects receipt.trace laterGood
                remainingEffects.ready.semantic remainingEffects.ready.costs (fun _ => trivial)
              exact ⟨result, after, .cons first remaining receipt.trace, checked.1,
                firstEffects.trans (remainingEffects.trans checked.2.1),
                firstExtension.trans (remainingExtension.trans checked.2.2), receipt.scopedCache,
                afterIdle, receipt.result, resultClosed⟩

/-- The first-seeded query completes on selected supported paths with unrelated siblings open. -/
theorem seeded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    ∃ result after, Seeded values paths before result after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil => exact ⟨.empty, before, .nil before, good, .refl _ ready, .refl _, scopes, idle, empty_available _, rfl⟩
  | cons seed rest =>
      obtain ⟨result, after, actual, effects⟩ := fold_complete unconstrained anchor anchorSemantic anchorReady
        values (rest ++ [seed]) before ranges good ready scopes idle available growth (by
          intro path member
          exact supported path (by simpa [List.mem_append, List.mem_cons, or_comm] using member))
      exact ⟨result, after, .nonempty actual, effects⟩

/-- Actual raw traces receive the same derived scope and physical invariants at their literal result. -/
theorem Seeded.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Seeded values paths before result after)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    Good after ∧ Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, completed, effects⟩ := seeded_complete unconstrained anchor anchorSemantic anchorReady
    values paths before ranges good ready scopes idle available growth supported
  obtain ⟨rfl, rfl⟩ := actual.unique completed
  exact effects

/-- A false secondary class derives finite checked seeded execution and same-cache loaded fields. -/
theorem false_class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (values : List (Value Symbol Guard))
    {before : Checked width} {anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.native.machine.heap false anchor)
    (good : Good before) (ready : Ready (physical before)) (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SeededRanges values (paths.map (List.map Int.ofNat))
      (advancePhysical before ⟨anchor, before.operations⟩)) :
    ∃ query after, Seeded values (paths.map (List.map Int.ofNat))
        (advancePhysical before ⟨anchor, before.operations⟩) query after ∧ Good after ∧
      Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap query ∧ query.free = [] := by
  obtain ⟨anchorSemantic, anchorReady, _, anchorValues, supported⟩ :=
    SourceCurrentSecondaryProjectionScoped.class_support unconstrained gate ready.semantic
      (SourceCurrentClassGateCompletion.gate_ready ready.semantic ready.costs) available proper
  have first := SourceCurrentAllocatedGateFields.secondary_class unconstrained gate ready available
  have anchorGood := SourceCurrentAllocatedConjunctionMemo.advance_good before _ good first.1
  have anchorScoped := SourceCurrentAllocatedConjunctionMemo.advance_scoped before ⟨anchor, before.operations⟩ scopes
  have anchorIdle := SourceCurrentAllocatedConjunctionMemo.advance_idle before ⟨anchor, before.operations⟩ idle
  have advanced : Effects (physical before)
      (physical (advancePhysical before ⟨anchor, before.operations⟩)) := first.1
  obtain ⟨query, after, actual, finalGood, finalEffects, finalExtension, finalScoped, finalIdle, resident, closed⟩ :=
    seeded_complete unconstrained anchor anchorSemantic anchorReady values (paths.map (List.map Int.ofNat))
      (advancePhysical before ⟨anchor, before.operations⟩) ranges anchorGood advanced.ready anchorScoped anchorIdle
      anchorValues (grows_refl anchor) (by
        intro path member
        obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
        exact supported original included)
  exact ⟨query, after, actual, finalGood, advanced.trans finalEffects,
    (SourceCurrentAllocatedQueryMemo.advance_extension before _ first.1).trans finalExtension,
    finalScoped, finalIdle, resident, closed⟩

end MicroCFTA.SourceCurrentAllocatedSeededQuery
