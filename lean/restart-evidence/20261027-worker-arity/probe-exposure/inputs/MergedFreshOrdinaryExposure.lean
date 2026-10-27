import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.MergedSourceComparison

/-!
# Exact repaired cold exposure in the prepared fragment

The source repair changes ordinary binder probes. Prepared substitution
emits no binder request. Its exact cold worklist, returned rows, failures,
and final cache therefore agree with the existing physical reader.
-/
namespace MicroCFTA.MergedFreshOrdinaryExposure
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open InternedEdgeResidency InternedShallowHeap MergedPhysicalWarmup
open MergedSourceExposure (Result)

/-- Follow the source's left-to-right worklist and actual cold unfolding effects. -/
def collect [DecidableEq (EdgeKey Symbol Guard)] : Nat → State Symbol Guard →
    List Nat → List (Value Symbol Guard) → Result Symbol Guard
  | _, state, _, [] => .done [] state
  | 0, state, _, _ :: _ => .exhausted state
  | fuel + 1, state, seen, value :: rest =>
      match value with
      | .empty => collect fuel state seen rest
      | .reference name => .unresolved name state
      | .node _ edges _ _ => (collect fuel state seen rest).prepend edges
      | .union entry members _ _ =>
          if entry.identity ∈ seen then collect fuel state seen rest
          else collect fuel state (entry.identity :: seen) (members ++ rest)
      | value@(.mu entry ..) =>
          if entry.identity ∈ seen then collect fuel state seen rest
          else match InternedFreshOrdinaryStoredSubstitution.unfold value state with
            | .done result after => collect fuel after (entry.identity :: seen) (result :: rest)
            | .pending key after => .pending key after

/-- Expose the source's direct ordinary/Mu paths and canonicalized closure fallback. -/
def nodeEdges [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : Result Symbol Guard :=
  match value with
  | .empty | .reference _ => .done [] state
  | .node _ edges _ _ => .done edges state
  | value@(.mu ..) =>
      match InternedFreshOrdinaryStoredSubstitution.unfold value state with
      | .done (.node _ edges _ _) after => .done edges after
      | .done _ after => (collect fuel after [] [value]).canonical
      | .pending key after => .pending key after
  | value@(.union ..) => (collect fuel state [] [value]).canonical

/-- Every prepared ordered worklist keeps the exact old reader result and cache. -/
theorem collect_eq [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) :
    collect fuel state seen pending = MergedSourceExposure.collect fuel state seen pending := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> rfl
  | succ fuel ih =>
      cases pending with
      | nil => rfl
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts prepared seen rest restInputs
          | reference => rfl
          | node entry edges depth free =>
              simp only [collect, MergedSourceExposure.collect, ih state facts prepared seen rest restInputs]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, MergedSourceExposure.collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, MergedSourceExposure.collect, ite_eq_right visited] using
                  ih state facts prepared (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, MergedSourceExposure.collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
                have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
                have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
                have unchanged : NoNewMu state after := by
                  simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | member
                  · rw [same]; exact verified.result result after done
                  · simpa only [done, Outcome.state] using verified.available child (restInputs child member)
                have next := ih after afterFacts (prepared.preserve unchanged) (entry.identity :: seen) (result :: rest) nextInputs
                simpa only [collect, MergedSourceExposure.collect, ite_eq_right visited,
                  InternedFreshOrdinaryStoredSubstitution.unfold_eq _ state prepared available, done] using next

/-- The repaired source edge reader agrees in every prepared cache and at every fuel. -/
theorem nodeEdges_eq [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) :
    nodeEdges fuel value state = MergedSourceExposure.nodeEdges fuel value state := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (rootAvailable : Available current root) :
      (collect fuel current [] [root]).canonical = (MergedSourceExposure.collect fuel current [] [root]).canonical := by
    rw [collect_eq fuel current currentFacts currentPrepared [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)]
  cases value with
  | empty | reference | node => rfl
  | union entry members depth free => exact fallback _ state facts prepared available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      have unchanged : NoNewMu state after := by
        simpa only [done, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) state prepared available
      have rootAvailable : Available after (.mu entry body depth ordinary) := by
        simpa only [done, Outcome.state] using verified.available _ available
      have fallbackEqual := fallback _ after afterFacts (prepared.preserve unchanged) rootAvailable
      cases result with
      | node => simp only [nodeEdges, MergedSourceExposure.nodeEdges,
          InternedFreshOrdinaryStoredSubstitution.unfold_eq _ state prepared available, done]
      | empty | reference | union | mu =>
          simpa only [nodeEdges, MergedSourceExposure.nodeEdges,
            InternedFreshOrdinaryStoredSubstitution.unfold_eq _ state prepared available, done] using fallbackEqual

/-- Lift repaired exposure into the unchanged source comparison result type. -/
def read [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) : MergedSourceComparison.Result Symbol Guard (List (EdgeValue Symbol Guard)) :=
  match nodeEdges fuel value state with
  | .done edges after => .done edges after
  | .unresolved name after => .failed (.unresolved name) after
  | .pending key after => .failed (.pending key) after
  | .exhausted after => .failed .exhausted after

/-- Every comparison read keeps its exact value, failure, and returned cache after repair. -/
theorem read_eq [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) :
    read fuel value state = MergedSourceComparison.read fuel value state := by
  simp only [read, MergedSourceComparison.read, nodeEdges_eq fuel value state facts prepared available]
  cases MergedSourceExposure.nodeEdges fuel value state <;> rfl

/-- Existing cold reader invariants hold for the actual repaired executor. -/
theorem nodeEdges_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) : MergedColdReaderFacts.Verified state (nodeEdges fuel value state) := by
  rw [nodeEdges_eq fuel value state facts prepared available]
  exact MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared available

/-- Closed prepared reads complete in the repaired executor with the same stable cache. -/
theorem read_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) :
    ∃ fuel edges after, nodeEdges fuel value state = .done edges after ∧
      Facts after ∧ Prepared after ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      NoNewMu state after ∧ Edges after edges ∧ MergedColdReaderClosedInputs.ClosedEdges edges ∧
      ∀ extra, nodeEdges (fuel + extra) value state = .done edges after := by
  obtain ⟨fuel, edges, after, done, finalFacts, finalPrepared, growth, history, unchanged, resident, children, stable⟩ :=
    MergedColdReaderFacts.read_closed value state facts prepared available closed
  refine ⟨fuel, edges, after, ?_, finalFacts, finalPrepared, growth, history, unchanged, resident, children, ?_⟩
  · rw [nodeEdges_eq fuel value state facts prepared available]
    exact done
  · intro extra
    rw [nodeEdges_eq (fuel + extra) value state facts prepared available]
    exact stable extra

end MicroCFTA.MergedFreshOrdinaryExposure
