import MicroCFTA.SourceEqualityRequiredGraph

/-!
# Finite physical required-child and row scans

The node induction supplies completion only for stored child requirements.
The finite list scans derive every intermediate cache, reconstructed edge,
and output invariant. Row rejection precedes every child request.
-/
namespace MicroCFTA.SourceEqualityRequiredListsComplete
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open InternedEdgeResidency (EdgeResident edge_grows)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph

/-- The finite Needed induction supplies completion at each strictly smaller child trie. -/
def ChildComplete [DecidableEq (EdgeKey Symbol Guard)] (entries : List (Int × Needed)) : Prop :=
  ∀ index needed, (index, needed) ∈ entries → ∀ (value : Value Symbol Guard) (before : State Symbol Guard),
    Ready before → Available before value → value.free = [] →
    ∃ result after, RequireNode needed value before result after ∧ Keeps before after ∧
      Available after result ∧ result.free = []

/-- Every finite child list completes once its stored child requirements complete. -/
theorem children_complete [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (children : ChildComplete (Symbol := Symbol) (Guard := Guard) entries)
    (index : Nat) (values : List (Value Symbol Guard)) (before : State Symbol Guard) (ready : Ready before)
    (available : Values before values) (closed : ClosedValues values) :
    ∃ results after, RequireChildren entries index values before results after ∧ Keeps before after ∧
      Values after results ∧ ClosedValues results := by
  induction values generalizing index before with
  | nil => exact ⟨[], before, .nil, pure_keeps before ready, by simp [Values], by simp [ClosedValues]⟩
  | cons value values ih =>
      have firstAvailable := available value List.mem_cons_self
      have restAvailable : Values before values := fun child member => available child (List.mem_cons_of_mem _ member)
      have firstClosed := closed value List.mem_cons_self
      have restClosed : ClosedValues values := fun child member => closed child (List.mem_cons_of_mem _ member)
      cases found : SourceEqualityNeededMap.lookup (index : Int) entries with
      | none =>
          obtain ⟨results, after, trace, keeps, resultAvailable, resultClosed⟩ := ih (index + 1) before ready restAvailable restClosed
          refine ⟨value :: results, after, .unselected index found trace, keeps, ?_, ?_⟩
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact keeps.available _ firstAvailable
            · exact resultAvailable child member
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact firstClosed
            · exact resultClosed child member
      | some needed =>
          obtain ⟨result, middle, firstTrace, firstKeeps, firstResident, firstResultClosed⟩ := children (index : Int) needed
            (SourceEqualityNeededMap.lookup_mem _ _ _ found) value before ready firstAvailable firstClosed
          have restAvailable : Values middle values := fun child member => firstKeeps.available child (restAvailable child member)
          obtain ⟨results, after, restTrace, restKeeps, resultAvailable, resultClosed⟩ :=
            ih (index + 1) middle firstKeeps.ready restAvailable restClosed
          refine ⟨result :: results, after, .selected index found firstTrace restTrace, firstKeeps.trans restKeeps, ?_, ?_⟩
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact restKeeps.available _ firstResident
            · exact resultAvailable child member
          · intro child member
            rcases List.mem_cons.mp member with rfl | member
            · exact firstResultClosed
            · exact resultClosed child member

/-- Every finite row scan completes with actual resident rebuilt edges and closed children. -/
theorem rows_complete [DecidableEq (EdgeKey Symbol Guard)]
    (entries : List (Int × Needed)) (children : ChildComplete (Symbol := Symbol) (Guard := Guard) entries)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (ready : Ready before)
    (resident : Edges before edges) (closed : ClosedEdges edges) :
    ∃ results after, RequireRows entries edges before results after ∧ Keeps before after ∧
      Edges after results ∧ ClosedEdges results := by
  induction edges generalizing before with
  | nil => exact ⟨[], before, .nil, pure_keeps before ready, by simp [Edges], by simp [ClosedEdges]⟩
  | cons edge edges ih =>
      have restResident : Edges before edges := fun original member => resident original (List.mem_cons_of_mem _ member)
      have restClosed : ClosedEdges edges := fun original member => closed original (List.mem_cons_of_mem _ member)
      cases fit : fits (.node entries) edge.children.length with
      | false =>
          obtain ⟨results, after, trace, keeps, residentResults, closedResults⟩ := ih before ready restResident restClosed
          exact ⟨results, after, .rejected fit trace, keeps, residentResults, closedResults⟩
      | true =>
          have facts := ready.semantic.1.normal.facts
          have available : Values before edge.children := facts.cached.edges edge.entry.key edge (resident edge List.mem_cons_self)
          obtain ⟨values, middle, childTrace, childKeeps, valuesAvailable, valuesClosed⟩ :=
            children_complete entries children 0 edge.children before ready available (closed edge List.mem_cons_self)
          let actual := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle
          have built := SourceEqualityRequiredCache.edge edge.entry.key.symbol edge.entry.key.constraint values
            middle childKeeps.ready valuesAvailable
          have firstKeeps : Keeps before actual.2 := childKeeps.trans built.1
          have restResident : Edges actual.2 edges := fun original member =>
            edge_grows before actual.2 firstKeeps.growth original (restResident original member)
          obtain ⟨results, after, restTrace, restKeeps, residentResults, closedResults⟩ :=
            ih actual.2 firstKeeps.ready restResident restClosed
          refine ⟨actual.1 :: results, after, .kept fit childTrace rfl restTrace, firstKeeps.trans restKeeps, ?_, ?_⟩
          · intro original member
            rcases List.mem_cons.mp member with rfl | member
            · exact edge_grows actual.2 after restKeeps.growth actual.1 built.2.1
            · exact residentResults original member
          · intro original member
            rcases List.mem_cons.mp member with rfl | member
            · rw [show actual.1.children = values from built.2.2]
              exact valuesClosed
            · exact closedResults original member

end MicroCFTA.SourceEqualityRequiredListsComplete
