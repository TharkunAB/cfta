import MicroCFTA.InternedGuardedProfileSupport
import MicroCFTA.InternedGuardedSelfFilter
import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryReadback
import MicroCFTA.InternedShallowHeap

/-!
# Independent-language readback from actual canonical probes

The heap invariant equates each stored Mu language with the least language
of its actual ordinary probe. Canonical hits use the complete requested
probe records. Ordinary freshness follows from surviving source captures.
-/
namespace MicroCFTA.InternedGuardedProbeHeap
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax finish)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedGuardedLanguage
open InternedBinderProtocol (Reference NodeKey)
open BinderLanguage (Lang least)

/-- One stored Mu and its actual ordinary probe have the same independent least language. -/
def Correct (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  ∀ (holds : Guard → Term Symbol → Bool) (environment : Env Symbol),
    meaning holds environment (.mu entry body depth ordinary) =
      least (fun candidate => meaning holds (bind environment (.uninterned (ordinaryLevel depth)) candidate) ordinary)

/-- Every actual complete Mu record has the independent language of its stored ordinary probe. -/
def Heap (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct entry body depth ordinary

/-- The initial source cache has no semantic Mu obligation. -/
theorem empty_heap : Heap (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Effects that add no Mu preserve the independent probe-language heap. -/
theorem preserve (before after : State Symbol Guard) (heap : Heap before)
    (old : InternedShallowHeap.NoNewMu before after) : Heap after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- Completion retains an earlier semantic invariant or installs the proved candidate. -/
theorem complete_heap (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (heap : Heap state) (correct : Correct entry body depth ordinary) :
    Heap (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- A coherent canonical hit has the least language of the complete requested ordinary probe. -/
theorem hit_language (holds : Guard → Term Symbol → Bool) (environment : Env Symbol) (smart : Bool)
    (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    meaning holds environment (finish smart value) =
      least (fun candidate => meaning holds (bind environment (.uninterned (ordinaryLevel depth)) candidate) ordinary) := by
  have normalized := finish_exact holds environment smart value state facts.coherent (facts.cached.nodes _ value present)
  obtain ⟨entry, body, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary value state facts depthAvailable ordinaryAvailable present
  exact normalized.trans (heap _ entry body depth ordinary present holds environment)

/-- The actual source chooser is fresh for the exact surviving symbolic captures. -/
theorem ordinary_fresh_captures [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (context : Context state values)
    (depth : Value Symbol Guard) (after : State Symbol Guard)
    (done : callback body values .depth state = .done depth after) :
    .uninterned (ordinaryLevel depth) ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free)) := by
  intro member
  have smaller := InternedFreshOrdinarySourceFreeNames.ordinary_above_captures body values state context.normal
    (context.local .depth (InternedNestedProvenance.depth_available state)).inputs context.freeNames context.profiles depth after done
    (ordinaryLevel depth) member
  exact Nat.lt_irrefl _ smaller

/-- Reserving the next interned identity is fresh for all surviving source captures. -/
theorem next_fresh_captures (body : Syntax Symbol Guard) (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (context : Context state values) :
    .interned state.nodes.next ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic body (values.map InternedRootProfile.profile) (values.map Value.free)) := by
  intro member
  obtain ⟨names, origin, present⟩ := InternedFreeNameForm.captures_origins body _ _ _ member
  obtain ⟨value, included, rfl⟩ := List.mem_map.mp origin
  exact InternedFreshProbeKeys.next_absent state.nodes context.normal.facts.coherent.valid.2 value
    (context.inputs value included).issued present

/-- Actual callback normalization retains the source least language at a name fresh for surviving captures. -/
theorem filter_source_least [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (environment : Env Symbol) (expression : Syntax Symbol Guard) (values : List (Value Symbol Guard))
    (name : Reference) (body : Value Symbol Guard) (state : State Symbol Guard) (context : Context state values)
    (available : Available state body)
    (fresh : name ∉ InternedProfileCallbackForm.captures
      (InternedFreeNameForm.symbolic expression (values.map InternedRootProfile.profile) (values.map Value.free)))
    (observed : ∀ ambient, meaning holds ambient body = InternedGuardedSyntax.evaluate holds
      (ambient name :: values.map (meaning holds ambient)) expression) :
    least (fun candidate => meaning holds (bind environment name candidate) (run (withoutSelfReference name body) state).1) =
      least (fun candidate => InternedGuardedSyntax.evaluate holds (candidate :: values.map (meaning holds environment)) expression) := by
  apply (filter_least holds environment name body state context.normal.facts available).trans
  apply BinderLanguage.least_congr
  intro candidate term
  apply iff_of_eq
  apply congrFun
  rw [observed]
  simp only [InternedGuardedLanguage.bind, ↓reduceIte]
  exact InternedGuardedProfileSupport.body_bind_fresh holds expression values state context.normal.facts.coherent
    context.inputs environment name candidate fresh

end MicroCFTA.InternedGuardedProbeHeap
