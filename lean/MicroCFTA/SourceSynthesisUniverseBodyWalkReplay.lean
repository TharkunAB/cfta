import MicroCFTA.SourceSynthesisUniverseBodyProductCompletion
import MicroCFTA.SourceRecursiveIntersectionOrdinaryProductRows

/-!
# Complete body-product row readback in one actual final machine

The derived source body product supplies its complete ordered row walk.
Each original matched pair replays its returned row in the one final
machine. Actual constructor replay also rebuilds the original value there
without changing the heap. No completed body or row worker is supplied.
The ordered relation retains source multiplicity before canonical ordering.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyWalkReplay
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel
open SourceSynthesisUniverseBodyReferenceControl (second secondState)
open InternedStoredClosedMuCompletion (PreparedWithoutMu)
open SourceRecursiveIntersectionControl (pair)

variable {Symbol Guard : Type}

/-- Derived body completion supplies every actual row and allocation-free replay in its final machine. -/
theorem node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (u b m : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard))
    (markerRow : EdgeValue Symbol Guard) (depth ordinary : Value Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (top : Guard)
    (conjoinTop : conjoin top top = top) (original : Machine Symbol Guard)
    (facts : Facts original.heap) (cacheValid : Cache.Valid original.domains)
    (universeAvailable : Available original.heap
      (.mu u (.node b bodyRows 0 [.interned u.identity]) depth ordinary))
    (markerAvailable : Available original.heap (.node m [markerRow] 0 []))
    (leaf : markerRow.children = []) (markerTop : markerRow.entry.key.constraint = top)
    (bodyTop : ∀ row ∈ bodyRows, row.entry.key.constraint = top)
    (bodyChildren : ∀ row ∈ bodyRows, ∀ child ∈ row.children,
      child = .node m [markerRow] 0 [] ∨ child = .reference (.interned u.identity)) :
    ∃ value final rows,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧
      Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) ∧
      (∀ row ∈ rows, EdgeResident final.heap row) ∧
      All₂ (fun matched row => edge emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        matched.1 matched.2 final = .done row final) (pairs bodyRows bodyRows) rows ∧
      nodeEdges value = canonicalEdges (surviving rows) ∧
      run (makeNode rows) final.heap = (value, final.heap) ∧
      (∀ row, row ∈ rows ↔ ∃ matched ∈ pairs bodyRows bodyRows,
        edge emptyGuard conjoin (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
          matched.1 matched.2 final = .done row final) := by
  let base := secondState u b bodyRows depth ordinary original
  let domain := (second u b bodyRows depth ordinary original).1
  have bodyAvailable : Available original.heap (.node b bodyRows 0 [.interned u.identity]) :=
    universeAvailable.children _ (by simp [children])
  have residents : ∀ row ∈ bodyRows, EdgeResident base.heap row :=
    fun row member => facts.linked b.key _ (bodyAvailable.resident b rfl) row member
  obtain ⟨baseValid, _, known⟩ := SourceSynthesisUniverseSecondDomain.second_checked u b bodyRows depth ordinary
    original facts cacheValid universeAvailable
  obtain ⟨value, final, done, finalValid, growth, available, prepared, freeShape⟩ :=
    SourceSynthesisUniverseBodyProductCompletion.node_complete u b m bodyRows markerRow depth ordinary
      emptyGuard conjoin top conjoinTop original facts cacheValid universeAvailable markerAvailable
      leaf markerTop bodyTop bodyChildren
  let call := execute (Symbol := Symbol) emptyGuard conjoin 8
  have calls : Calls call := execute_checked emptyGuard conjoin 8
  have replay : Replays call := execute_replay emptyGuard conjoin 8
  obtain ⟨rows, after, trace, built, exactRows⟩ :=
    node_readback emptyGuard conjoin call calls domain bodyRows bodyRows base baseValid known
      residents residents value final done
  have walked := (walk_done_iff _ _ _ _ _).mpr trace
  have checked := rows_checked emptyGuard conjoin call calls domain bodyRows bodyRows base baseValid known
    residents residents
  have afterValid : SourceRecursiveIntersectionKernel.Valid after := by
    simpa only [walked, Result.state] using checked.valid
  have residentsAfter := checked.result rows after walked
  have builtChecked := work_checked after afterValid (makeNode rows) Available
    (InternedNestedFacts.node_verified rows after.heap afterValid.1 residentsAfter)
  have lastGrowth : Extension after final := by
    simpa only [built, Result.state] using builtChecked.extension
  have related := rows_pointwise_replay emptyGuard conjoin call calls replay domain bodyRows bodyRows
    base final rows after baseValid known residents residents walked lastGrowth
  have finalResidents : ∀ row ∈ rows, EdgeResident final.heap row :=
    fun row member => edge_grows _ _ lastGrowth.heap row (residentsAfter row member)
  have repeated := work_replay (makeNode rows) after final value final afterValid built (Extension.refl final)
  have fields := work_done (makeNode rows) final value final repeated
  have literal : run (makeNode rows) final.heap = (value, final.heap) := by
    apply Prod.ext
    · exact fields.1.symm
    · exact (congrArg Machine.heap fields.2).symm
  have members : ∀ row, row ∈ rows ↔ ∃ matched ∈ pairs bodyRows bodyRows,
      edge emptyGuard conjoin (call domain) matched.1 matched.2 final = .done row final :=
    fun row => pointwise_result_member
      (fun matched => edge emptyGuard conjoin (call domain) matched.1 matched.2 final)
      (pairs bodyRows bodyRows) rows final related row
  exact ⟨value, final, rows, done, finalValid, growth, available, prepared, freeShape,
    finalResidents, related, exactRows, literal, members⟩

end MicroCFTA.SourceSynthesisUniverseBodyWalkReplay
