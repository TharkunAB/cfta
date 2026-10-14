import MicroCFTA.InternedGuardedBudgetLocalFinish
import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedGuardedProbeHeap

/-!
# Exact budget readback from actual canonical probes

Raw Mu languages and empty-local body languages form separate invariants.
The existing depth heap decides which language smart finish returns.
Canonical hits retain their complete stored payload and requested probes.
-/
namespace MicroCFTA.InternedGuardedBudgetProbeHeap
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (finish)
open InternedFreshOrdinaryConstruction InternedGuardedBudget
open InternedBinderProtocol (Reference NodeKey)

/-- One stored Mu retains both budget readbacks of its exact ordinary probe. -/
structure Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop where
  localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body
  raw : ∀ (holds : Guard → Term Symbol → Bool) (environment : Env Symbol),
    meaning holds environment (.mu entry body depth ordinary) = BinderBudgetLanguage.mu
      (fun candidate => meaning holds (bind environment (.uninterned (ordinaryLevel depth)) candidate) ordinary)
  zero : ∀ (holds : Guard → Term Symbol → Bool) (environment : Env Symbol),
    meaning holds (bind environment (.interned entry.identity) (fun _ _ => False)) body =
      meaning holds (bind environment (.uninterned (ordinaryLevel depth)) (fun _ _ => False)) ordinary

/-- Every actual complete Mu retains both independent ordinary-probe budget readbacks. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) → Correct entry body depth ordinary

/-- The initial source cache has no budget readback obligation. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that add no Mu retain the complete budget probe heap. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before)
    (old : InternedShallowHeap.NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Completion retains an old budget invariant or installs the proved fresh candidate. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- The existing depth invariant recovers the exact stored deep-local decision. -/
theorem uses_eq (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (localNormal : InternedDeepLocalNormal.Local (.interned entry.identity) body)
    (decoded : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary) :
    decide (.interned entry.identity ∈ InternedDeepFreeDepth.deepNames body) =
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary := by
  have raw := (decoded false).1
  have bodyDepth : body.depth = depth.depth := by
    simpa only [finish, Value.depth, InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_false,
      Bool.true_or, Bool.false_eq_true, ↓reduceIte, Nat.add_right_cancel_iff] using raw
  have actual := InternedDeepLocalNormal.finish_depth true entry body depth ordinary state coherent available localNormal
  rw [(decoded true).1, bodyDepth] at actual
  by_cases used : .interned entry.identity ∈ InternedDeepFreeDepth.deepNames body <;>
    cases observed : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary <;>
    simp only [InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_true, Bool.false_or,
      observed, used, ↓reduceIte, Bool.false_eq_true, decide_true, decide_false] at actual ⊢ <;> omega

/-- Both actual finish paths read exactly the budget language selected by the existing probe decoder. -/
theorem finish_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (smart : Bool)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state body) (correct : Correct entry body depth ordinary)
    (decoded : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary) :
    meaning holds environment (finish smart (.mu entry body depth ordinary)) =
      if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then
        BinderBudgetLanguage.mu (fun candidate => meaning holds (bind environment (.uninterned (ordinaryLevel depth)) candidate) ordinary)
      else meaning holds (bind environment (.uninterned (ordinaryLevel depth)) (fun _ _ => False)) ordinary := by
  rw [finish_local_exact holds environment smart entry body depth ordinary state coherent available correct.localNormal,
    uses_eq entry body depth ordinary state coherent available correct.localNormal decoded]
  split
  · exact correct.raw holds environment
  · exact correct.zero holds environment

/-- Coherent canonical hits retain both requested probes and the exact decoded budget language. -/
theorem hit_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (smart : Bool)
    (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    meaning holds environment (finish smart value) =
      if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then
        BinderBudgetLanguage.mu (fun candidate => meaning holds (bind environment (.uninterned (ordinaryLevel depth)) candidate) ordinary)
      else meaning holds (bind environment (.uninterned (ordinaryLevel depth)) (fun _ _ => False)) ordinary := by
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact finish_language holds environment smart entry body depth ordinary state facts.coherent
    ((facts.cached.nodes _ _ present).children body (by simp [InternedProbeProvenance.children]))
    (heap _ entry body depth ordinary present) (depthHeap _ entry body depth ordinary present)

end MicroCFTA.InternedGuardedBudgetProbeHeap
