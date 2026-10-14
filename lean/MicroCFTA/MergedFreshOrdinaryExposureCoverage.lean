import MicroCFTA.MergedFreshOrdinaryExposureCertificate
import MicroCFTA.MergedFreshOrdinaryExposureOrigins

/-!
# Exact constructor origins of repaired public reads

Each completed allocation-free public read covers every constructor reached
through the actual repaired epsilon graph. Its ordered rows retain every
resident edge after canonicalization. Complete semantic heaps and coverage
replace the old preparation premise.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedFreshOrdinaryExposure
open MergedSourceExposure (Result)
open MergedFreshOrdinaryGraph
open MergedFreshOrdinaryExposureCertificate (collect_covers)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A root with no epsilon successor exposes only its own constructor edges. -/
theorem origin_terminal [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (root : Value Symbol Guard) (terminal : successors state root = [])
    (edge : EdgeValue Symbol Guard) (origin : Origin state [root] edge) :
    edge ∈ InternedEdgeResidency.nodeEdges root := by
  obtain ⟨source, reached, member⟩ := origin
  have equal : source = root := by
    clear member
    induction reached with
    | seed member => exact List.mem_singleton.mp member
    | step prior member ih => simp [ih, terminal] at member
  simpa only [equal] using member

/-- A source with one epsilon successor and no constructor edges delegates every origin to it. -/
theorem origin_single [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (root result : Value Symbol Guard) (next : successors state root = [result])
    (noEdges : InternedEdgeResidency.nodeEdges root = [])
    (edge : EdgeValue Symbol Guard) (origin : Origin state [root] edge) : Origin state [result] edge := by
  obtain ⟨source, reached, member⟩ := origin
  have separated : source = root ∨ Productivity.Reachable (successors state) [result] source := by
    clear member
    induction reached with
    | seed member => exact Or.inl (List.mem_singleton.mp member)
    | step prior member ih =>
        rcases ih with rfl | reached
        · exact Or.inr (.seed (next ▸ member))
        · exact Or.inr (.step reached member)
  rcases separated with rfl | reached
  · simp [noEdges] at member
  · exact ⟨source, reached, member⟩

/-- A successful read with no cache effect covers every actual epsilon constructor origin. -/
theorem nodeEdges_covers_fixed [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : InternedRecordCoherence.Covered [] state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = [])
    (edges : List (EdgeValue Symbol Guard))
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value state = .done edges state)
    (edge : EdgeValue Symbol Guard) (origin : Origin state [value] edge) : edge ∈ edges := by
  have facts := semantic.1.normal.facts
  have fallback (root : Value Symbol Guard) (input : Available state root) (rootClosed : root.free = [])
      (completed : (collect fuel state [] [root]).canonical = .done edges state)
      (origin : Origin state [root] edge) : edge ∈ edges := by
    have inputs : Values state [root] := by
      intro child member
      simpa only [List.mem_singleton.mp member] using input
    cases read : collect fuel state [] [root] with
    | unresolved | pending | exhausted => simp only [read, Result.canonical, reduceCtorEq] at completed
    | done values final =>
        have equal : canonicalEdges values = edges ∧ final = state := by
          simpa only [read, Result.canonical, Result.done.injEq] using completed
        have cache := equal.2
        subst final
        rw [← equal.1]
        exact InternedEdgeResidency.canonicalEdges_retains state facts.coherent values edge
          ((MergedFreshOrdinaryColdEffects.collect_verified fuel state semantic covered [] [root] inputs
            (by intro child member; simpa only [List.mem_singleton.mp member] using rootClosed)).edges values state read)
          (collect_covers fuel state semantic covered [root] inputs values read edge origin)
  cases value with
  | empty | reference =>
      have impossible := origin_terminal state _ rfl edge origin
      cases impossible
  | node entry own depth free =>
      cases done
      exact origin_terminal state _ rfl edge origin
  | union entry members depth free => exact fallback _ available closed done origin
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, middleContext, _, _, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have middleAvailable := available.grows state middle growth history
      have back : Grows middle state := by
        have later : Grows middle (collect fuel middle [] [.mu entry body depth ordinary]).canonical.state := by
          simpa only [MergedPreparedReaderEffects.canonical_state] using
            (MergedFreshOrdinaryColdReplay.collect_correct fuel middle middleContext.normal.facts.coherent.valid
              [] [.mu entry body depth ordinary]).2
        cases result with
        | node actual own level free =>
            have equal : own = edges ∧ middle = state := by
              simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, Result.done.injEq] using done
            rw [equal.2]
            exact grows_refl state
        | empty | reference | union | mu =>
            have completed : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges state := by
              simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using done
            simpa only [completed, Result.state] using later
      have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary) state state result middle facts.coherent.valid unfolded back
      have same := (Outcome.done.inj (unfolded.symm.trans replay)).2
      subst middle
      cases result with
      | node actual own level free =>
          have equal : own = edges := by
            simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded, Result.done.injEq, and_true] using done
          rw [← equal]
          exact origin_terminal state (.node actual own level free) rfl edge (origin_single state _ (.node actual own level free)
            (by simp only [successors, unfolded]) rfl edge origin)
      | empty | reference | union | mu =>
          exact fallback _ available closed (by simpa only [MergedFreshOrdinaryExposure.nodeEdges, unfolded] using done) origin


end MicroCFTA.MergedFreshOrdinaryExposureCoverage
