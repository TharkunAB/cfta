import MicroCFTA.SourcePruningEnumerationCachedEdge
import MicroCFTA.SourcePruningEnumerationOrdinaryBranches

namespace MicroCFTA.SourcePruningEnumerationCachedBranches
open EnumerationState EnumerationSchedule EnumerationCorrectness
open SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Run every selected edge from the same original cache in list order. -/
noncomputable def run
    (heap : InternedConstructorTemplates.State Symbol Constraint) (fuel : Nat)
    (scs : List EnumerationState.Suspended)
    (selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint) :
    List (Option (List (Option (Fragments.Fragment Symbol) ×
      EnumerationExpandableIndex.Cached Symbol Constraint) ×
      EnumerationExpandableIndex.Cached Symbol Constraint)) :=
  selectedEdges.map (fun edge =>
    SourcePruningEnumerationCachedEdge.prepare heap fuel scs edge before)

/-- Derive stable ordered alternatives, separate cache receipts and the exact raw branch stream. -/
theorem complete
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (InternedConstructorTemplates.EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (scs : List EnumerationState.Suspended) (roots : Nat → Nat)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : InternedProbeProvenance.Available heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = []) (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (storage : StorageValid before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) :
    ∃ (fuel : Nat)
      (outcomes : List (Option (List (Option (Fragments.Fragment Symbol) ×
        EnumerationExpandableIndex.Cached Symbol Constraint) ×
        EnumerationExpandableIndex.Cached Symbol Constraint))),
      (∀ (extra : Nat), run heap (fuel + extra) scs selectedEdges before = outcomes) ∧
      Language.All₂ (fun edge outcome =>
        (SourcePruningEnumerationEdgeTraversal.prepare scs edge = none ↔ outcome = none) ∧
        (∀ (action : EnumerateM Symbol Constraint (Option (Fragments.Fragment Symbol))),
          SourcePruningEnumerationEdgeTraversal.prepare scs edge = some action →
          ∃ (rows : List (Option (Fragments.Fragment Symbol) ×
              EnumerationExpandableIndex.Cached Symbol Constraint))
            (after : EnumerationExpandableIndex.Cached Symbol Constraint),
            outcome = some (rows, after) ∧
            ExceptT.run (action before.core) = rows.map (fun row => .ok (row.1, row.2.core)) ∧
            before.core.counter ≤ after.core.counter ∧
            after.core.counter = after.core.values.length ∧
            after.core.representatives = before.core.representatives ∧ Roots after.core.representatives roots ∧
            StorageValid after.core ∧ PendingRealized heap after.core ∧
            EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
            (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate heap
              ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
            (rows = [] ∨ ∃ result : Option (Fragments.Fragment Symbol),
              rows = [(result, after)] ∧
              (∀ (fragment : Fragments.Fragment Symbol), result = some fragment →
                FragmentBound («Symbol» := Symbol) after.core.counter fragment)))) selectedEdges outcomes ∧
      ExceptT.run (SourcePruningEnumerationOrdinaryBranches.run scs selectedEdges before.core) =
        (outcomes.map (fun outcome =>
          match outcome with
          | none => [.ok (none, before.core)]
          | some (rows, _prefix) => rows.map (fun row => .ok (some row.1, row.2.core)))).flatten := by
  induction selectedEdges with
  | nil =>
    refine ⟨0, [], ?_, .nil, rfl⟩
    intro extra
    rfl
  | cons edge rest ih =>
    have selectedHead : edge ∈ storedEdges := by
      exact selected edge (List.mem_cons_self ..)
    have selectedTail : ∀ edge ∈ rest, edge ∈ storedEdges := by
      intro edge member
      exact selected edge (List.mem_cons_of_mem _ member)
    obtain ⟨headFuel, headOutcome, headRun, headAbsent, headReceipt⟩ :=
      SourcePruningEnumerationCachedEdge.complete heap parentEntry storedEdges depth free
        edge scs roots ready parentAvailable parentClosed selectedHead before
        storage realized paths counts flags bounded
    obtain ⟨tailFuel, tailOutcomes, tailRun, tailRelated, tailRaw⟩ := ih selectedTail
    refine ⟨headFuel + tailFuel, headOutcome :: tailOutcomes, ?_,
      .cons ⟨headAbsent, headReceipt⟩ tailRelated, ?_⟩
    · intro extra
      change SourcePruningEnumerationCachedEdge.prepare heap (headFuel + tailFuel + extra)
        scs edge before :: run heap (headFuel + tailFuel + extra) scs rest before =
          headOutcome :: tailOutcomes
      rw [show headFuel + tailFuel + extra = headFuel + (tailFuel + extra) by omega,
        headRun (tailFuel + extra)]
      rw [show headFuel + (tailFuel + extra) = tailFuel + (headFuel + extra) by omega,
        tailRun (headFuel + extra)]
    · rw [SourcePruningEnumerationOrdinaryBranches.run, run_bind] at tailRaw
      simp only [choose, ExceptT.run] at tailRaw
      rw [SourcePruningEnumerationOrdinaryBranches.run, run_bind]
      simp only [choose, ExceptT.run, List.map_cons, List.flatMap_cons]
      rw [tailRaw]
      simp only [List.flatten_cons]
      cases prepared : SourcePruningEnumerationEdgeTraversal.prepare scs edge with
      | none =>
        rw [headAbsent.mp prepared]
        rfl
      | some action =>
        obtain ⟨rows, after, outcomeEq, actualRaw, _invariants⟩ :=
          headReceipt action prepared
        rw [outcomeEq]
        simp only [bind, StateT.bind, ExceptT.run, ExceptT.bind, ExceptT.mk] at actualRaw ⊢
        rw [actualRaw]
        simp only [List.flatMap_map, ExceptT.bindCont, pure, StateT.pure,
          ExceptT.pure, ExceptT.mk, ← List.map_eq_flatMap]

end MicroCFTA.SourcePruningEnumerationCachedBranches
