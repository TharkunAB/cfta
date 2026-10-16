import MicroCFTA.SourceCurrentSecondaryQueryCosts
import MicroCFTA.SourceCurrentSecondaryEffects

/-!
# Finite seeded queries after actual false secondary gates

The range plan checks native requests at their actual reached prefixes.
The false gate supplies projection support at its returned heap. Each
projection completes before its tail and native intersection. The seeded
query retains the source rotation and does not merge projected operands.
Only selected original paths need support. Unrelated siblings can stay open.
-/
namespace MicroCFTA.SourceCurrentSeededQueryCompletion
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessProjection SourceEmptinessClassFold
open SourceCurrentSecondaryProjectionScoped
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Native checks use the first actual projection and its completed tail fold. -/
inductive FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard)) :
    List (List Int) → Native width Symbol Guard → Prop where
  | one : FoldRanges emptyGuard conjoin values [path] before
  | cons
      (rest : ∀ value middle, Operand path values before value middle →
        FoldRanges emptyGuard conjoin values (next :: paths) middle)
      (native : ∀ value middle tail later,
        Operand path values before value middle →
        Fold emptyGuard conjoin values (next :: paths) middle tail later →
        SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
          (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) later) :
      FoldRanges emptyGuard conjoin values (path :: next :: paths) before

/-- The refused query rotates its first seed to the last demanded operand. -/
def SeededRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (before : Native width Symbol Guard) : Prop :=
  match paths with
  | [] => True
  | seed :: rest => FoldRanges emptyGuard conjoin values (rest ++ [seed]) before

/-- Anchored operand support and reached word checks construct the actual finite fold. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard)
    (ranges : FoldRanges emptyGuard conjoin values paths before)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    ∃ result after, Fold emptyGuard conjoin values paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  induction paths generalizing before with
  | nil => cases ranges
  | cons path paths ih =>
      cases paths with
      | nil =>
          obtain ⟨result, after, actual, finalReady, kept, resident, closed, _⟩ :=
            operand_complete unconstrained anchor anchorSemantic anchorReady emptyGuard conjoin path values before
              ready available growth (supported path (by simp))
          exact ⟨result, after, .one actual, finalReady, kept, resident, closed⟩
      | cons next paths =>
          cases ranges with
          | cons rest native =>
              obtain ⟨value, middle, first, middleReady, firstKept, valueAvailable, valueClosed, _⟩ :=
                operand_complete unconstrained anchor anchorSemantic anchorReady emptyGuard conjoin path values before
                  ready available growth (supported path (by simp))
              obtain ⟨tail, later, remaining, laterReady, remainingKept, tailAvailable, tailClosed⟩ :=
                ih middle (rest value middle first) middleReady
                  (fun value member => firstKept.available value (available value member))
                  (grows_trans growth firstKept.growth)
                  (fun path member => supported path (List.mem_cons_of_mem _ member))
              obtain ⟨result, after, step, finalReady, lastKept, resultAvailable, resultClosed, _⟩ :=
                SourceEqualityNativeScoped.complete emptyGuard conjoin later laterReady value tail
                  (remainingKept.available value valueAvailable) tailAvailable valueClosed tailClosed
                  (native value middle tail later first remaining) (fun _ _ => true) (by intros; rfl)
              exact ⟨result, after, .cons first remaining step, finalReady,
                firstKept.trans (remainingKept.trans lastKept), resultAvailable, resultClosed⟩

/-- The actual first-seeded query completes from its reached native range plan. -/
theorem seeded_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard)
    (ranges : SeededRanges emptyGuard conjoin values paths before)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    ∃ result after, Seeded emptyGuard conjoin values paths before result after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps before.machine.heap after.machine.heap ∧
      Available after.machine.heap result ∧ result.free = [] := by
  cases paths with
  | nil =>
      exact ⟨.empty, before, Seeded.nil emptyGuard conjoin values before, ready,
        pure_keeps _ ready.semantic.ready, empty_available _, rfl⟩
  | cons seed rest =>
      exact fold_complete unconstrained anchor anchorSemantic anchorReady emptyGuard conjoin values (rest ++ [seed]) before
        ranges ready available growth
        (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member))

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap

/-- A false proper class gate derives a finite seeded query and every returned physical invariant. -/
theorem false_class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (paths : Class) (values : List (Value Symbol Guard))
    {before : Native width Symbol Guard} {anchor : State Symbol Guard}
    (gate : SourceCurrentSecondaryTrace.ClassTrace unconstrained values paths before.machine.heap false anchor)
    (ready : IdleReady top conjoin before) (costs : CostHeap before.machine.heap)
    (fields : FieldHeap before.machine.heap) (available : Values before.machine.heap values)
    (proper : ∀ path ∈ paths, path ≠ [])
    (ranges : SeededRanges top conjoin values (paths.map (List.map Int.ofNat)) (advanceHeap before anchor)) :
    ∃ query after, Seeded top conjoin values (paths.map (List.map Int.ofNat))
        (advanceHeap before anchor) query after ∧
      IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
      Keeps before.machine.heap after.machine.heap ∧ Keeps anchor after.machine.heap ∧
      Available after.machine.heap query ∧ query.free = [] ∧ Values after.machine.heap values ∧
      GateReady after.machine.heap := by
  obtain ⟨anchorSemantic, anchorReady, firstKept, anchorValues, certificates⟩ :=
    class_support unconstrained gate ready.semantic
      (SourceEqualityExposureCosts.gate_ready ready.semantic costs) available proper
  have supported : ∀ path ∈ paths.map (List.map Int.ofNat), PathSupport unconstrained anchor path values := by
    intro path member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact certificates original included
  have gateEffects := SourceCurrentSecondaryEffects.class_effects
    (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
    unconstrained gate ready.semantic costs available fields
  have advancedReady := ready.advance anchor firstKept anchorSemantic
  obtain ⟨query, after, actual, finalReady, finalKept, queryAvailable, queryClosed⟩ :=
    seeded_complete unconstrained anchor anchorSemantic anchorReady top conjoin values
      (paths.map (List.map Int.ofNat)) (advanceHeap before anchor) ranges advancedReady anchorValues
      (grows_refl anchor) supported
  have finalCosts := SourceCurrentSecondaryQueryCosts.seeded_costs unconstrained anchor anchorSemantic anchorReady
    actual advancedReady anchorValues (grows_refl anchor) supported gateEffects.2.2.1
  have finalFields := SourceCurrentSecondaryClassFold.seeded_fields unconstrained anchor anchorSemantic anchorReady
    actual advancedReady anchorValues (grows_refl anchor) supported gateEffects.2.2.2
  have retained := firstKept.trans finalKept
  exact ⟨query, after, actual, finalReady, finalCosts, finalFields, retained, finalKept,
    queryAvailable, queryClosed, (fun value member => retained.available value (available value member)),
    SourceEqualityExposureCosts.gate_ready finalReady.semantic finalCosts⟩

end MicroCFTA.SourceCurrentSeededQueryCompletion
