import MicroCFTA.SourceEqualityRequiredListsComplete
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

/-!
# Complete finite physical required-path graphs

The induction decreases the finite Needed trie. Automaton nodes can remain
cyclic. Recursive heads use complete cold exposure, and ordinary requests
visit only strictly smaller child requirements. Original source construction
derives the cache and closed-input premises.
-/
namespace MicroCFTA.SourceEqualityRequiredComplete
open InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredListsComplete

/-- An ordinary head completes from the induction hypotheses for its child requirements. -/
theorem ordinary_complete [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (nonempty : entries ≠ [])
    (children : ChildComplete (Symbol := Symbol) (Guard := Guard) entries)
    (value : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) (ordinary : Ordinary value) :
    ∃ result after, RequireNode (.node entries) value before result after ∧ Keeps before after ∧
      Available after result ∧ result.free = [] := by
  cases value with
  | empty => exact ⟨.empty, before, .empty nonempty, pure_keeps before ready, available, rfl⟩
  | reference | union | mu => cases ordinary
  | node entry edges depth free =>
      have facts := ready.semantic.1.normal.facts
      have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked
        (.node entry edges depth free) available.resident
      have closedEdges : ClosedEdges edges := MergedColdReaderClosed.node_children_closed before facts entry edges depth free available closed
      obtain ⟨rebuilt, middle, rows, firstKeeps, residentRows, closedRows⟩ :=
        rows_complete entries children edges before ready resident closedEdges
      have finished := SourceEqualityRequiredCache.node rebuilt middle firstKeeps.ready residentRows closedRows
      exact ⟨_, _, .ordinary nonempty rows rfl, firstKeeps.trans finished.1, finished.2.1, finished.2.2.1⟩

/-- Every finite requirement has a complete physical graph on every closed available source value. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (needed : Needed)
    (value : Value Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (closed : value.free = []) :
    ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧
      Available after result ∧ result.free = [] := by
  cases shape : needed with
  | node entries =>
      by_cases noChildren : entries = []
      · subst entries
        exact ⟨value, before, .identity, pure_keeps before ready, available, closed⟩
      · have children : ChildComplete (Symbol := Symbol) (Guard := Guard) entries := by
          intro index child member value before ready available closed
          exact complete child value before ready available closed
        cases value with
        | empty => exact ⟨.empty, before, .empty noChildren, pure_keeps before ready, available, rfl⟩
        | reference name => simp [Value.free] at closed
        | node entry edges depth free =>
            exact ordinary_complete entries noChildren children (.node entry edges depth free)
              before ready available closed True.intro
        | union entry members depth free =>
            obtain ⟨exposed, middle, head, headKeeps, headAvailable, headClosed, ordinary⟩ :=
              SourceEqualityRequiredHead.complete (.union entry members depth free) before ready available closed
            obtain ⟨result, after, body, bodyKeeps, resultAvailable, resultClosed⟩ :=
              ordinary_complete entries noChildren children exposed middle headKeeps.ready headAvailable headClosed ordinary
            exact ⟨result, after, .recursive noChildren True.intro head body,
              headKeeps.trans bodyKeeps, resultAvailable, resultClosed⟩
        | mu entry body depth probe =>
            obtain ⟨exposed, middle, head, headKeeps, headAvailable, headClosed, ordinary⟩ :=
              SourceEqualityRequiredHead.complete (.mu entry body depth probe) before ready available closed
            obtain ⟨result, after, bodyTrace, bodyKeeps, resultAvailable, resultClosed⟩ :=
              ordinary_complete entries noChildren children exposed middle headKeeps.ready headAvailable headClosed ordinary
            exact ⟨result, after, .recursive noChildren True.intro head bodyTrace,
              headKeeps.trans bodyKeeps, resultAvailable, resultClosed⟩
termination_by sizeOf needed
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Original source construction derives a finite required-path graph with all cache effects. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (needed : Needed) :
    ∃ value state result after,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value state ∧
      RequireNode needed value state result after ∧ Keeps state after ∧ Available after result ∧ result.free = [] := by
  obtain ⟨value, state, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  have ready := SourceEqualityRequiredCache.constructed expression value state built
  have available := (InternedFreshOrdinaryFacts.closed_verified expression).result value state built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value state built
  obtain ⟨result, after, trace, keeps, resident, resultClosed⟩ := complete needed value state ready available closed
  exact ⟨value, state, result, after, built, trace, keeps, resident, resultClosed⟩

end MicroCFTA.SourceEqualityRequiredComplete
