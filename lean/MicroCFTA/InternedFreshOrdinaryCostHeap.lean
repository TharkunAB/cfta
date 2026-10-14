import MicroCFTA.InternedGuardedBudgetProbeHeap
import MicroCFTA.InternedFreeOccurrenceRank

/-!
# Weighted free-reference readback from repaired ordinary probes

The fresh ordinary probe separates captured occurrence costs from the
supplied local. A stored invariant retains these costs and the actual local
normal form. The existing depth heap supplies the smart retention decision.
Establishing this invariant through full source execution remains separate.
-/
namespace MicroCFTA.InternedFreshOrdinaryCostHeap
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (finish)
open InternedFreshOrdinaryConstruction InternedFreeOccurrenceRank InternedDeepFreeDepth
open InternedDeepFreeNormalization
open InternedBinderProtocol (Reference NodeKey)

/-- One stored Mu retains the exact captured costs of its fresh ordinary probe. -/
structure Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop where
  localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body
  external : ∀ name count,
    ((name, count) ∈ costs body ∧ name ≠ .interned entry.identity) ↔
      ((name, count) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth))

/-- Every complete stored recursive payload retains weighted ordinary-probe readback. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct entry body depth ordinary

/-- The empty source cache has no stored cost obligation. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects without new recursive records retain the exact earlier cost observations. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before)
    (old : InternedShallowHeap.NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- First-writer completion retains an old cost observation or installs its verified candidate. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- Three common external cost observations and actual probe freshness establish the stored candidate. -/
theorem candidate (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (depthAvailable : Available state depth)
    (captured : List (Reference × Nat))
    (localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body)
    (fresh : .interned entry.identity ∉ depth.free)
    (depthSame : ∀ name count, name ≠ .depth → ((name, count) ∈ costs depth ↔ (name, count) ∈ captured))
    (ordinarySame : ∀ name count, name ≠ .uninterned (ordinaryLevel depth) →
      ((name, count) ∈ costs ordinary ↔ (name, count) ∈ captured))
    (bodySame : ∀ name count, name ≠ .interned entry.identity → ((name, count) ∈ costs body ↔ (name, count) ∈ captured)) :
    Correct entry body depth ordinary := by
  have ordinaryFresh : ∀ count, (.uninterned (ordinaryLevel depth), count) ∉ captured := by
    intro count present
    have occurrence := (depthSame _ count (by intro impossible; cases impossible)).mpr present
    exact ordinary_fresh depth ((costs_free depth state coherent depthAvailable _).mp ⟨count, occurrence⟩)
  have bodyFresh : ∀ count, (.interned entry.identity, count) ∉ captured := by
    intro count present
    have occurrence := (depthSame _ count (by intro impossible; cases impossible)).mpr present
    exact fresh ((costs_free depth state coherent depthAvailable _).mp ⟨count, occurrence⟩)
  refine ⟨localNormal, ?_⟩
  intro name count
  constructor
  · rintro ⟨present, different⟩
    have capturedCost := (bodySame name count different).mp present
    have other : name ≠ .uninterned (ordinaryLevel depth) := fun same => ordinaryFresh count (same ▸ capturedCost)
    exact ⟨(ordinarySame name count other).mpr capturedCost, other⟩
  · rintro ⟨present, different⟩
    have capturedCost := (ordinarySame name count different).mp present
    have other : name ≠ .interned entry.identity := fun same => bodyFresh count (same ▸ capturedCost)
    exact ⟨(bodySame name count other).mpr capturedCost, other⟩

/-- Actual sequencing retains the stored cost invariant at complete and pending outcomes. -/
theorem bind_heap (outcome : InternedNestedConstruction.Outcome Symbol Guard First)
    (next : First → State Symbol Guard → InternedNestedConstruction.Outcome Symbol Guard Result)
    (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- A retained wrapper adds exactly one Mu to each external occurrence cost. -/
theorem mu_cost_iff (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (name : Reference) (count : Nat) :
    (name, count) ∈ costs (.mu entry body depth ordinary) ↔
      ∃ prior, ((name, prior) ∈ costs body ∧ name ≠ .interned entry.identity) ∧ count = prior + 1 := by
  simp only [costs]
  constructor
  · intro member
    obtain ⟨⟨other, prior⟩, present, equal⟩ := List.mem_map.mp member
    have fields : other = name ∧ prior + 1 = count := Prod.mk.inj equal
    rcases fields with ⟨rfl, rfl⟩
    exact ⟨prior, by simpa only [List.mem_filter, bne_iff_ne] using present, rfl⟩
  · rintro ⟨prior, present, rfl⟩
    exact List.mem_map.mpr ⟨(name, prior), List.mem_filter.mpr ⟨present.1, by simpa using present.2⟩, rfl⟩

/-- The stored invariant decodes every raw Mu occurrence from the actual ordinary probe. -/
theorem raw_costs (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (name : Reference) (count : Nat) :
    (name, count) ∈ costs (.mu entry body depth ordinary) ↔
      ∃ prior, ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) ∧ count = prior + 1 := by
  rw [mu_cost_iff]
  simp only [correct.external]

/-- Raw retention or the existing decoded smart decision determines the exact added cost. -/
def binderCost (smart : Bool) (depth ordinary : Value Symbol Guard) : Nat :=
  if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then 1 else 0

/-- Decode the complete returned cost list from the actual ordinary probe. -/
def decodedCosts (smart : Bool) (depth ordinary : Value Symbol Guard) : List (Reference × Nat) :=
  ((costs ordinary).filter (fun item => item.1 != .uninterned (ordinaryLevel depth))).map
    (fun item => (item.1, item.2 + binderCost smart depth ordinary))

/-- The decoded list retains each captured cost and the exact added wrapper cost. -/
theorem decoded_member (smart : Bool) (depth ordinary : Value Symbol Guard) (name : Reference) (count : Nat) :
    (name, count) ∈ decodedCosts smart depth ordinary ↔
      ∃ prior, ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) ∧
        count = prior + binderCost smart depth ordinary := by
  constructor
  · intro member
    obtain ⟨⟨other, prior⟩, present, equal⟩ := List.mem_map.mp member
    have fields : other = name ∧ prior + binderCost smart depth ordinary = count := Prod.mk.inj equal
    rcases fields with ⟨rfl, rfl⟩
    exact ⟨prior, by simpa only [List.mem_filter, bne_iff_ne] using present, rfl⟩
  · rintro ⟨prior, present, rfl⟩
    exact List.mem_map.mpr ⟨(name, prior), List.mem_filter.mpr ⟨present.1, by simpa using present.2⟩, rfl⟩

/-- Actual smart cleanup reads the complete weighted profile from the stored ordinary probe. -/
theorem finish_costs (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (correct : Correct entry body depth ordinary) (decoded : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary)
    (name : Reference) (count : Nat) :
    (name, count) ∈ costs (finish smart (.mu entry body depth ordinary)) ↔
      ∃ prior, ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) ∧
        count = prior + binderCost smart depth ordinary := by
  cases smart with
  | false => simpa [finish, binderCost] using raw_costs entry body depth ordinary correct name count
  | true =>
      have chosen := InternedGuardedBudgetProbeHeap.uses_eq entry body depth ordinary state coherent available correct.localNormal decoded
      by_cases used : .interned entry.identity ∈ deepNames body
      · have free := deep_free body state coherent available _ used
        have nonbare : body.referenceOf ≠ .ref (.interned entry.identity) := by
          intro same
          have bare := (referenceOf_self_iff _ body).mp same
          simp [bare, deepNames] at used
        have choice : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by rw [← chosen]; simp [used]
        simpa [finish, cleanup, free, nonbare, binderCost, choice] using raw_costs entry body depth ordinary correct name count
      · have choice : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by rw [← chosen]; simp [used]
        by_cases free : .interned entry.identity ∈ body.free
        · rcases correct.localNormal free with impossible | bare
          · exact False.elim (used impossible)
          · subst body
            have absent : ∀ prior, ¬ ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) := by
              intro prior present
              have impossible := (correct.external name prior).mpr present
              simp only [costs, List.mem_singleton, Prod.mk.injEq] at impossible
              exact impossible.2 impossible.1.1
            simp [finish, cleanup, Value.free, Value.referenceOf, costs, binderCost, choice, absent]
        · have finished : finish true (.mu entry body depth ordinary) = body := by simp [finish, cleanup, free]
          rw [finished]
          constructor
          · intro present
            have different : name ≠ .interned entry.identity := by
              intro same
              apply free
              exact (costs_free body state coherent available _).mp ⟨count, by simpa only [same] using present⟩
            exact ⟨count, (correct.external name count).mp ⟨present, different⟩, by simp [binderCost, choice]⟩
          · rintro ⟨prior, present, same⟩
            have equal : count = prior := by simpa [binderCost, choice] using same
            rw [equal]
            exact ((correct.external name prior).mpr present).1

/-- A canonical hit uses its immutable requested probes and the established weighted heap. -/
theorem hit_costs (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) (name : Reference) (count : Nat) :
    (name, count) ∈ costs (finish smart value) ↔
      ∃ prior, ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) ∧
        count = prior + binderCost smart depth ordinary := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact finish_costs smart entry body depth ordinary state facts.coherent
    ((facts.cached.nodes _ _ present).children body (by simp [children]))
    (heap _ entry body depth ordinary present) (depthHeap _ entry body depth ordinary present) name count

end MicroCFTA.InternedFreshOrdinaryCostHeap
