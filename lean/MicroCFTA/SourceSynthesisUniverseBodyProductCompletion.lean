import MicroCFTA.SourceSynthesisUniverseRowCompletion
import MicroCFTA.SourceRecursiveIntersectionPreparedNode

/-!
# Completion of the actual universe-body hash join

The real ordered row walk uses each preceding returned machine.
Every child request has a derived execution in that machine. The final
node retains its actual cache effects. Its free names are empty or contain
only the outer diagonal placeholder. No completed child caller is supplied.
-/
namespace MicroCFTA.SourceSynthesisUniverseBodyProductCompletion
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol InternedEdgeResidency
open InternedStoredClosedMuCompletion
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionControl
open SourceSynthesisUniverseBodyReferenceControl (second secondState)

variable {Symbol Guard : Type}

private def GoodRow (name : Reference) (state : Machine Symbol Guard)
    (row : EdgeValue Symbol Guard) : Prop :=
  EdgeResident state.heap row ∧ ∀ child ∈ row.children,
    PreparedWithoutMu child ∧ ∀ other ∈ child.free, other = name

private theorem walk_rows_complete
    (call : EdgeValue Symbol Guard × EdgeValue Symbol Guard → Machine Symbol Guard →
      Result Symbol Guard (EdgeValue Symbol Guard))
    (base : Machine Symbol Guard) (name : Reference)
    (jobs : List (EdgeValue Symbol Guard × EdgeValue Symbol Guard))
    (steps : ∀ job ∈ jobs, ∀ before, SourceRecursiveIntersectionKernel.Valid before → Extension base before →
      ∃ row after, call job before = .done row after ∧ SourceRecursiveIntersectionKernel.Valid after ∧
        Extension before after ∧ GoodRow name after row)
    (before : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid before) (growth : Extension base before) :
    ∃ rows final, walk call jobs before = .done rows final ∧ SourceRecursiveIntersectionKernel.Valid final ∧
      Extension before final ∧ ∀ row ∈ rows, GoodRow name final row := by
  induction jobs generalizing before with
  | nil => exact ⟨[], before, rfl, valid, Extension.refl _, by intro row member; cases member⟩
  | cons first rest ih =>
      obtain ⟨row, after, firstDone, afterValid, firstGrowth, firstGood⟩ :=
        steps first List.mem_cons_self before valid growth
      obtain ⟨rows, final, restDone, finalValid, lastGrowth, restGood⟩ :=
        ih (fun job member => steps job (List.mem_cons_of_mem _ member)) after afterValid
          (growth.trans firstGrowth)
      refine ⟨row :: rows, final, ?_, finalValid, firstGrowth.trans lastGrowth, ?_⟩
      · simp only [walk, firstDone, Result.bind, restDone]
      · intro actual member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨edge_grows after.heap final.heap lastGrowth.heap actual firstGood.1, firstGood.2⟩
        · exact restGood actual later

/-- Every actual body row completes in source order before the real node normalization. -/
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
    ∃ value final,
      node emptyGuard conjoin
        (execute emptyGuard conjoin 8 (second u b bodyRows depth ordinary original).1)
        bodyRows bodyRows (secondState u b bodyRows depth ordinary original) = .done value final ∧
      SourceRecursiveIntersectionKernel.Valid final ∧ Extension (secondState u b bodyRows depth ordinary original) final ∧
      Available final.heap value ∧ PreparedWithoutMu value ∧
      (value.free = [] ∨ value.free = [.intersection (pair u.identity u.identity).1
        (pair u.identity u.identity).2]) := by
  let base := secondState u b bodyRows depth ordinary original
  let domain := (second u b bodyRows depth ordinary original).1
  let name := Reference.intersection (pair u.identity u.identity).1 (pair u.identity u.identity).2
  have baseValid : SourceRecursiveIntersectionKernel.Valid base :=
    (SourceSynthesisUniverseSecondDomain.second_checked u b bodyRows depth ordinary original
      facts cacheValid universeAvailable).1
  obtain ⟨rows, after, walked, afterValid, growth, good⟩ :=
    walk_rows_complete
      (fun job => edge emptyGuard conjoin (execute emptyGuard conjoin 8 domain) job.1 job.2)
      base name (pairs bodyRows bodyRows) (by
        intro job member before beforeValid beforeGrowth
        obtain ⟨first, firstMember, secondRow, secondMember, _, same⟩ :=
          (SymbolicHashJoin.hashJoin_member (fun row : EdgeValue Symbol Guard => row.entry.key.symbol)
            Prod.mk bodyRows bodyRows job).mp member
        rw [← same]
        exact SourceSynthesisUniverseRowCompletion.row_complete u b m bodyRows markerRow depth ordinary
          emptyGuard conjoin top conjoinTop original before facts cacheValid universeAvailable markerAvailable
          leaf markerTop bodyTop beforeValid beforeGrowth first secondRow
          (bodyChildren first firstMember) (bodyChildren secondRow secondMember))
      base baseValid (Extension.refl base)
  have residents : ∀ row ∈ rows, EdgeResident after.heap row := fun row member => (good row member).1
  have prepared : ∀ child ∈ rows.flatMap EdgeValue.children, PreparedWithoutMu child := by
    intro child member
    obtain ⟨row, present, selected⟩ := List.mem_flatMap.mp member
    exact ((good row present).2 child selected).1
  have only : ∀ child ∈ rows.flatMap EdgeValue.children, ∀ other ∈ child.free, other = name := by
    intro child member
    obtain ⟨row, present, selected⟩ := List.mem_flatMap.mp member
    exact ((good row present).2 child selected).2
  let made := run (makeNode rows) after.heap
  have checked := work_checked after afterValid (makeNode rows) Available
    (node_verified rows after.heap afterValid.1 residents)
  refine ⟨made.1, {after with heap := made.2}, ?_, checked.valid,
    growth.trans checked.extension, checked.result _ _ rfl, ?_, ?_⟩
  · dsimp only [base, domain] at walked
    simp only [node, walked, Result.bind, work]
    rfl
  · exact SourceRecursiveIntersectionPreparedNode.makeNode_prepared rows after.heap afterValid.1 residents prepared
  · exact SourceRecursiveIntersectionPreparedNode.makeNode_free_empty_or_singleton rows after.heap
      afterValid.1 residents name only

end MicroCFTA.SourceSynthesisUniverseBodyProductCompletion
