import MicroCFTA.MergedFreshOrdinaryExposureCoverage

/-!
# Available values along completed repaired reads

An allocation-free completed read retains every value on its epsilon paths.
The finite traversal certificate supplies this fact even when the worklist
skips an identity that it has visited. Closed roots retain closed successors.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposureInputs
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open MergedFreshOrdinaryGraph MergedFreshOrdinaryExposure
open MergedFreshOrdinaryExposureCertificate
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open Productivity (Reachable)

/-- A complete certificate retains every value on a requested epsilon path. -/
theorem Certificate.reachable_available [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (pending found : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (cert : Certificate state [] pending found edges) (value : Value Symbol Guard)
    (reached : Reachable (successors state) pending value) : Available state value := by
  have member : value ∈ found := by
    induction reached with
    | seed member =>
        rcases cert.requested _ member with ⟨entry, _, absent⟩ | present
        · cases absent
        · exact present
    | step prior member ih =>
        rcases (cert.closed _ ih _ member).2 with ⟨entry, _, absent⟩ | present
        · cases absent
        · exact present
  exact cert.available value member

/-- A completed public read with no cache effect retains all of its epsilon values. -/
theorem nodeEdges_reachable_available [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (root : Value Symbol Guard) (available : Available state root) (edges : List (EdgeValue Symbol Guard))
    (done : nodeEdges fuel root state = .done edges state) (value : Value Symbol Guard)
    (path : Reachable (successors state) [root] value) : Available state value := by
  have terminal (root : Value Symbol Guard) (available : Available state root)
      (none : successors state root = []) (reached : Reachable (successors state) [root] value) : Available state value := by
    have same : value = root := by
      clear path
      induction reached with
      | seed member => exact List.mem_singleton.mp member
      | step prior member ih => simp only [ih, none, List.not_mem_nil] at member
    exact same ▸ available
  have fallback (root : Value Symbol Guard) (available : Available state root)
      (completed : (collect fuel state [] [root]).canonical = .done edges state)
      (reached : Reachable (successors state) [root] value) : Available state value := by
    cases read : collect fuel state [] [root] with
    | unresolved | pending | exhausted => simp only [read, MergedSourceExposure.Result.canonical, reduceCtorEq] at completed
    | done values final =>
        have equal : canonicalEdges values = edges ∧ final = state := by
          simpa only [read, MergedSourceExposure.Result.canonical, MergedSourceExposure.Result.done.injEq] using completed
        have same := equal.2
        subst final
        obtain ⟨found, cert⟩ := collect_certificate fuel state semantic covered [] [root]
          (by intro child member; simpa only [List.mem_singleton.mp member] using available) values read
        exact Certificate.reachable_available state [root] found values cert value reached
  cases root with
  | empty | reference | node => exact terminal _ available rfl path
  | union => exact fallback _ available done path
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, middleContext, _, _, resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          state semantic.1 available semantic.2 covered
      have back : Grows middle state := by
        have later : Grows middle (collect fuel middle [] [.mu entry body depth ordinary]).canonical.state := by
          simpa only [MergedPreparedReaderEffects.canonical_state] using
            (MergedFreshOrdinaryColdReplay.collect_correct fuel middle middleContext.normal.facts.coherent.valid
              [] [.mu entry body depth ordinary]).2
        cases result with
        | node =>
            have equal := MergedSourceExposure.Result.done.inj (by simpa only [nodeEdges, unfolded] using done)
            rw [equal.2]
            exact grows_refl state
        | empty | reference | union | mu =>
            have completed : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges state := by
              simpa only [nodeEdges, unfolded] using done
            simpa only [completed, MergedSourceExposure.Result.state] using later
      have replay := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary)
        state state result middle semantic.1.normal.facts.coherent.valid unfolded back
      have same := (Outcome.done.inj (unfolded.symm.trans replay)).2
      subst middle
      cases result with
      | node actual own level free =>
          have separated : value = .mu entry body depth ordinary ∨ value = .node actual own level free := by
            clear terminal fallback
            induction path with
            | seed member => exact Or.inl (List.mem_singleton.mp member)
            | step prior member ih =>
                rcases ih with rfl | rfl
                · exact Or.inr (List.mem_singleton.mp (by simpa only [successors, unfolded] using member))
                · simp only [successors, List.not_mem_nil] at member
          rcases separated with rfl | rfl
          · exact available
          · exact resultAvailable
      | empty | reference | union | mu =>
          exact fallback _ available (by simpa only [nodeEdges, unfolded] using done) path

/-- A closed available epsilon source has closed successors under actual unfolding. -/
theorem successor_closed [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (value : Value Symbol Guard) (available : Available state value)
    (closed : value.free = []) (child : Value Symbol Guard) (member : child ∈ successors state value) : child.free = [] := by
  cases value with
  | empty | reference | node => simp only [successors, List.not_mem_nil] at member
  | union entry members depth free =>
      exact MergedColdReaderClosed.union_members_closed state semantic.1.normal.facts entry members depth free available closed child member
  | mu entry body depth ordinary =>
      cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending => simp only [successors, done, List.not_mem_nil] at member
      | done result after =>
          have same : child = result := List.mem_singleton.mp (by simpa only [successors, done] using member)
          subst child
          exact InternedFreshOrdinaryStoredSubstitution.unfold_closed (.mu entry body depth ordinary)
            state semantic.1 available closed result after done

/-- Every epsilon value of an allocation-free closed read is available and closed. -/
theorem nodeEdges_reachable [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (covered : Covered [] state)
    (root : Value Symbol Guard) (available : Available state root) (closed : root.free = [])
    (edges : List (EdgeValue Symbol Guard)) (done : nodeEdges fuel root state = .done edges state)
    (value : Value Symbol Guard) (reached : Reachable (successors state) [root] value) :
    Available state value ∧ value.free = [] := by
  refine ⟨nodeEdges_reachable_available fuel state semantic covered root available edges done value reached, ?_⟩
  induction reached with
  | seed member => simpa only [List.mem_singleton.mp member] using closed
  | step prior member ih =>
      exact successor_closed state semantic _
        (nodeEdges_reachable_available fuel state semantic covered root available edges done _ prior) ih _ member

end MicroCFTA.MergedFreshOrdinaryExposureInputs
