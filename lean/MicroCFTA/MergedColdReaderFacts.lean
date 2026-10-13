import MicroCFTA.MergedColdReaderClosed

/-!
# Source cache and edge invariants after cold exposure

Ordered exposure preserves complete record facts and both actual cache
histories. It adds no Mu record in the prepared fragment. Returned edges
remain resident in the exact returned cache.
-/
namespace MicroCFTA.MergedColdReaderFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedEdgeResidency InternedShallowHeap MergedPhysicalWarmup MergedSourceExposure

/-- Each physical reader outcome retains its histories and all successful edge records. -/
structure Verified (before : State Symbol Guard) (result : Result Symbol Guard) : Prop where
  facts : Facts result.state
  growth : Grows before result.state
  history : Extends before.nodes.issued result.state.nodes.issued
  unchanged : NoNewMu before result.state
  edges : ∀ values after, result = .done values after → Edges after values

/-- A finished edge list requires no further cache effect. -/
theorem done_verified (state : State Symbol Guard) (facts : Facts state) (edges : List (EdgeValue Symbol Guard))
    (resident : Edges state edges) : Verified state (.done edges state) := by
  refine ⟨facts, grows_refl _, extends_refl _, noNewMu_refl _, ?_⟩
  intro values after same
  cases same
  exact resident

/-- An exhausted proof bound changes neither cache nor record facts. -/
theorem exhausted_verified (state : State Symbol Guard) (facts : Facts state) : Verified state (.exhausted state) :=
  ⟨facts, grows_refl _, extends_refl _, noNewMu_refl _, by intro _ _ same; cases same⟩

/-- The explicit unresolved-reference error retains its exact source cache. -/
theorem unresolved_verified (state : State Symbol Guard) (facts : Facts state) (name : InternedBinderProtocol.Reference) :
    Verified state (.unresolved name state) :=
  ⟨facts, grows_refl _, extends_refl _, noNewMu_refl _, by intro _ _ same; cases same⟩

/-- Earlier source effects compose with the reader's exact returned history. -/
theorem Verified.extend {before middle : State Symbol Guard} (result : Result Symbol Guard) (verified : Verified middle result)
    (growth : Grows before middle) (history : Extends before.nodes.issued middle.nodes.issued)
    (unchanged : NoNewMu before middle) : Verified before result :=
  ⟨verified.facts, grows_trans growth verified.growth, extends_trans history verified.history,
    noNewMu_trans unchanged verified.unchanged, verified.edges⟩

/-- Earlier ordinary edges remain resident after the remaining reader effects. -/
theorem Verified.prepend (result : Result Symbol Guard) (verified : Verified state result)
    (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges) : Verified state (result.prepend edges) := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.facts, verified.growth, verified.history, verified.unchanged, ?_⟩
      intro output final same
      have equal := Result.done.inj same
      cases equal.2
      rw [← equal.1]
      intro edge member
      rcases List.mem_append.mp member with first | later
      · exact edge_grows state after verified.growth edge (resident edge first)
      · exact verified.edges values after rfl edge later

/-- Canonical edge ordering retains source residency and every cache invariant. -/
theorem Verified.canonical (result : Result Symbol Guard) (verified : Verified state result) : Verified state result.canonical := by
  cases result with
  | unresolved | pending | exhausted => exact verified
  | done values after =>
      refine ⟨verified.facts, verified.growth, verified.history, verified.unchanged, ?_⟩
      intro output final same
      have equal := Result.done.inj same
      cases equal.2
      rw [← equal.1]
      exact fun edge member => verified.edges values after rfl edge (canonicalEdges_member values edge member)

/-- Every available input retains availability after any verified reader outcome. -/
theorem Verified.available (result : Result Symbol Guard) (verified : Verified state result)
    (value : Value Symbol Guard) (available : Available state value) : Available result.state value :=
  available.grows state result.state verified.growth verified.history

/-- The exact cold source worklist preserves facts, histories, and successful edge residency. -/
theorem collect_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Verified state (collect fuel state seen pending) := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => exact done_verified state facts [] (by simp [Edges])
      | cons => exact exhausted_verified state facts
  | succ fuel ih =>
      cases pending with
      | nil => exact done_verified state facts [] (by simp [Edges])
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts prepared seen rest restInputs
          | reference name => exact unresolved_verified state facts name
          | node entry edges depth free =>
              exact (ih state facts prepared seen rest restInputs).prepend _ edges
                (resident_edges state facts.linked (.node entry edges depth free) available.resident)
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using ih state facts prepared (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
                have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
                have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
                have growth : Grows state after := by simpa only [done, Outcome.state] using verified.growth
                have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, Outcome.state] using verified.history
                have unchanged : NoNewMu state after := by
                  simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | member
                  · rw [same]; exact verified.result result after done
                  · simpa only [done, Outcome.state] using verified.available child (restInputs child member)
                have next := ih after afterFacts (prepared.preserve unchanged) (entry.identity :: seen) (result :: rest) nextInputs
                simpa only [collect, ite_eq_right visited, done] using next.extend _ growth history unchanged

/-- The top-level physical edge reader retains all source invariants in its exact returned cache. -/
theorem nodeEdges_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) : Verified state (MergedSourceExposure.nodeEdges fuel value state) := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (rootAvailable : Available current root) :
      Verified current (collect fuel current [] [root]).canonical :=
    (collect_verified fuel current currentFacts currentPrepared [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)).canonical _
  cases value with
  | empty | reference => exact done_verified state facts [] (by simp [Edges])
  | node entry edges depth free =>
      exact done_verified state facts edges
        (resident_edges state facts.linked (.node entry edges depth free) available.resident)
  | union entry members depth free => exact fallback _ state facts prepared available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      have growth : Grows state after := by simpa only [done, Outcome.state] using verified.growth
      have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, Outcome.state] using verified.history
      have unchanged : NoNewMu state after := by
        simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
      have rootAvailable : Available after (.mu entry body depth ordinary) := by
        simpa only [done, Outcome.state] using verified.available _ available
      have resultAvailable := verified.result result after done
      have fallbackVerified := (fallback _ after afterFacts (prepared.preserve unchanged) rootAvailable).extend _ growth history unchanged
      cases result with
      | node actual edges depth free =>
          simpa only [MergedSourceExposure.nodeEdges, done] using (done_verified after afterFacts edges
            (resident_edges after afterFacts.linked (.node actual edges depth free) resultAvailable.resident)).extend _ growth history unchanged
      | empty | reference | union | mu => simpa only [MergedSourceExposure.nodeEdges, done] using fallbackVerified

/-- Closed cold exposure returns resident closed children and a prepared cache, with an exact stable result. -/
theorem read_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, MergedSourceExposure.nodeEdges fuel value state = .done edges after ∧
      Facts after ∧ Prepared after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      NoNewMu state after ∧ Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, MergedSourceExposure.nodeEdges (fuel + extra) value state = .done edges after := by
  obtain ⟨fuel, edges, after, done, children⟩ := MergedColdReaderClosed.nodeEdges_closed value state facts prepared available closed
  have verified := nodeEdges_verified fuel value state facts prepared available
  have afterFacts : Facts after := by simpa only [done, Result.state] using verified.facts
  have growth : Grows state after := by simpa only [done, Result.state] using verified.growth
  have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, Result.state] using verified.history
  have unchanged : NoNewMu state after := by simpa only [done, Result.state] using verified.unchanged
  refine ⟨fuel, edges, after, done, afterFacts, prepared.preserve unchanged, growth, history, unchanged,
    verified.edges edges after done, children, ?_⟩
  intro extra
  exact (MergedColdReaderTermination.nodeEdges_stable fuel extra value state (by rw [done]; trivial)).trans done

end MicroCFTA.MergedColdReaderFacts
