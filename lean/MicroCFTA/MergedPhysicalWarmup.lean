import MicroCFTA.InternedStoredClosedMuCompletion
import MicroCFTA.InternedShallowHeap

/-!
# A finite warmup of actual recursive source records

Each complete Mu body prepares no open nested Mu. Closed nested records
can have arbitrary depth. The actual stored-body executor then completes
without adding a Mu record. One traversal of the initial record inventory
makes every later Mu unfolding replay without allocation.
-/
namespace MicroCFTA.MergedPhysicalWarmup
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedStoredSubstitution InternedStoredClosedMuCompletion InternedShallowHeap
open InternedBinderProtocol (NodeKey)

/-- Every actual complete Mu body stops preparation before an open nested Mu. -/
def Prepared (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    PreparedWithoutMu body

/-- An unchanged recursive payload retains its structural preparation property. -/
theorem Prepared.preserve (prepared : Prepared before) (unchanged : NoNewMu before after) : Prepared after := by
  intro key entry body depth ordinary present
  exact prepared key entry body depth ordinary (unchanged key entry body depth ordinary present)

/-- Every cache with depth-zero Mu bodies satisfies the larger preparation fragment. -/
theorem prepared_of_shallow (state : State Symbol Guard) (facts : Facts state) (shallow : Shallow state) :
    Prepared state := by
  intro key entry body depth ordinary stored
  have available := facts.cached.nodes key _ stored
  exact zero_prepared body state facts.coherent (available.children body (by simp [children]))
    (shallow key entry body depth ordinary stored)

/-- Complete records belong to the finite inventory derived from their actual issued counter. -/
theorem inventory_complete (state : State Symbol Guard) (coherent : Coherent state)
    (key : NodeKey) (value : Value Symbol Guard) (stored : state.nodeRecords key = some value) :
    value ∈ nodeInventory state := by
  obtain ⟨entry, present, _⟩ := coherent.nodes key value stored
  have issued := (coherent.valid.2.2 key entry present).2
  have bound := coherent.valid.2.1 entry.identity key issued
  exact List.mem_filterMap.mpr ⟨entry.identity, List.mem_range.mpr bound, by simp [issued, stored]⟩

/-- Each enumerated complete record has the source's recursive availability invariant. -/
theorem inventory_available (state : State Symbol Guard) (cached : Cached state) :
    Values state (nodeInventory state) := by
  intro value member
  obtain ⟨identity, _, present⟩ := List.mem_filterMap.mp member
  cases issued : state.nodes.issued identity with
  | none => simp [issued] at present
  | some key => exact cached.nodes key value (by simpa [issued] using present)

/-- Every source unfolding in this structural fragment completes. -/
theorem unfold_complete [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (prepared : Prepared state) (available : Available state value) :
    ∃ result after, InternedStoredSubstitution.unfold value state = .done result after := by
  cases value with
  | empty | reference | node | union => exact ⟨_, _, rfl⟩
  | mu entry body depth ordinary =>
      exact execute_complete body _ state (prepared entry.key entry body depth ordinary (available.resident entry rfl))

/-- The actual source unfolding adds no recursive payload in this fragment. -/
theorem unfold_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (prepared : Prepared state) (available : Available state value) :
    NoNewMu state (InternedStoredSubstitution.unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact noNewMu_refl state
  | mu entry body depth ordinary =>
      apply build_noNewMu
      exact encode_withoutMu (leaves body) [] body
        (prepared entry.key entry body depth ordinary (available.resident entry rfl))

/-- One completed stored-body unfolding replays after arbitrary later cache growth. -/
theorem unfold_replay [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before after : State Symbol Guard) (result : Value Symbol Guard) (final : State Symbol Guard)
    (valid : Valid before) (done : InternedStoredSubstitution.unfold value before = .done result final)
    (growth : Grows final after) : InternedStoredSubstitution.unfold value after = .done result after := by
  cases value with
  | empty | reference | node | union =>
      simp only [InternedStoredSubstitution.unfold, Outcome.done.injEq] at done
      simp only [InternedStoredSubstitution.unfold, done.1]
  | mu entry body depth ordinary => exact execute_replay body _ before after result final valid done growth

/-- Execute one actual unfolding for each original complete record, in source order. -/
def warmup [DecidableEq (EdgeKey Symbol Guard)] : List (Value Symbol Guard) →
    State Symbol Guard → Outcome Symbol Guard (List (Value Symbol Guard))
  | [], state => .done [] state
  | first :: rest, state =>
      (InternedStoredSubstitution.unfold first state).bind fun result after =>
        (warmup rest after).bind fun results final => .done (result :: results) final

/-- Finite source warmup establishes completion, provenance, and exact replay for every supplied record. -/
theorem warmup_correct [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (inputs : Values before values) :
    ∃ results after, warmup values before = .done results after ∧ Facts after ∧
      Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧ NoNewMu before after ∧
      Values after results ∧ ∀ value ∈ values, ∃ result ∈ results,
        InternedStoredSubstitution.unfold value after = .done result after := by
  induction values generalizing before with
  | nil => exact ⟨[], before, rfl, facts, grows_refl _, extends_refl _, noNewMu_refl _, by simp [Values], by simp⟩
  | cons first rest ih =>
      have firstAvailable := inputs first List.mem_cons_self
      obtain ⟨result, middle, firstDone⟩ := unfold_complete first before prepared firstAvailable
      have firstVerified := unfold_verified first before facts firstAvailable
      have middleFacts : Facts middle := by simpa only [firstDone, Outcome.state] using firstVerified.facts
      have firstGrowth : Grows before middle := by simpa only [firstDone, Outcome.state] using firstVerified.growth
      have firstHistory : Extends before.nodes.issued middle.nodes.issued := by simpa only [firstDone, Outcome.state] using firstVerified.history
      have firstUnchanged : NoNewMu before middle := by simpa only [firstDone, Outcome.state] using unfold_noNewMu first before prepared firstAvailable
      have restInputs : Values middle rest := by
        intro value member
        simpa only [firstDone, Outcome.state] using firstVerified.available value (inputs value (List.mem_cons_of_mem _ member))
      obtain ⟨results, after, restDone, afterFacts, restGrowth, restHistory, restUnchanged, outputs, replays⟩ :=
        ih middle middleFacts (prepared.preserve firstUnchanged) restInputs
      refine ⟨result :: results, after, ?_, afterFacts, grows_trans firstGrowth restGrowth,
        extends_trans firstHistory restHistory, noNewMu_trans firstUnchanged restUnchanged, ?_, ?_⟩
      · simp only [warmup, firstDone, Outcome.bind, restDone]
      · intro value member
        rcases List.mem_cons.mp member with same | member
        · rw [same]
          exact (firstVerified.result result middle firstDone).grows middle after restGrowth restHistory
        · exact outputs value member
      · intro value member
        rcases List.mem_cons.mp member with same | member
        · rw [same]
          exact ⟨result, List.mem_cons_self, unfold_replay first before after result middle facts.coherent.valid firstDone restGrowth⟩
        · obtain ⟨output, present, replay⟩ := replays value member
          exact ⟨output, List.mem_cons_of_mem _ present, replay⟩

/-- Every actual complete Mu unfolds to one of the retained warmup results without changing the cache. -/
def Ready [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) : Prop :=
  ∀ entry body depth ordinary, Available state (.mu entry body depth ordinary) →
    ∃ result ∈ outputs, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done result state

/-- Later effects that add no Mu retain each prepared recursive read exactly. -/
theorem Ready.preserve [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (facts : Facts before) (outputs : List (Value Symbol Guard)) (ready : Ready before outputs)
    (growth : Grows before after) (unchanged : NoNewMu before after) : Ready after outputs := by
  intro entry body depth ordinary available
  have stored := unchanged entry.key entry body depth ordinary (available.resident entry rfl)
  obtain ⟨result, member, done⟩ := ready entry body depth ordinary (facts.cached.nodes entry.key _ stored)
  exact ⟨result, member, unfold_replay _ before after result before facts.coherent.valid done growth⟩

/-- The initial physical record inventory derives a later cache with all recursive requests prepared. -/
theorem prepare [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) :
    ∃ outputs after, warmup (nodeInventory before) before = .done outputs after ∧ Facts after ∧
      Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧ NoNewMu before after ∧
      Values after outputs ∧ Ready after outputs := by
  obtain ⟨outputs, after, done, afterFacts, growth, history, unchanged, available, replays⟩ :=
    warmup_correct (nodeInventory before) before facts prepared (inventory_available before facts.cached)
  refine ⟨outputs, after, done, afterFacts, growth, history, unchanged, available, ?_⟩
  intro entry body depth ordinary ready
  have old := unchanged entry.key entry body depth ordinary (ready.resident entry rfl)
  exact replays _ (inventory_complete before facts.coherent entry.key _ old)

end MicroCFTA.MergedPhysicalWarmup
