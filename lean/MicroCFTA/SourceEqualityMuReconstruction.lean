import MicroCFTA.InternedFreshOrdinaryProbeFilter
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedGuardedConstructors
import MicroCFTA.InternedStoredSubstitutionRebind

/-!
# Actual Mu reconstruction in partial equality reduction

The matcher supplies its two exact cached probes. Other arguments use stored
substitution. The constructor filters both probes, requests their actual key,
and performs smart cleanup. Resident filtered probes derive a completed hit
with no callback-body execution or cache change.
-/
namespace MicroCFTA.SourceEqualityMuReconstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome work request finish)
open InternedFreshOrdinaryConstruction
open InternedFreshOrdinaryProbeFilter (Clean filter_fixed)
open InternedBinderProtocol (Reference NodeKey)

/-- Actual matcher fast paths precede the stored substitution fallback. -/
def matched [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (name : Reference) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) :=
  match probeReadback depth ordinary name with
  | some value => .done value state
  | none => InternedFreshOrdinaryStoredSubstitution.execute body
      (InternedStoredSubstitutionRebind.replacement (.interned entry.identity) (.reference name)) state

/-- Source createMu filters the matched body before using a probe or fresh body. -/
def callback [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (name : Reference) (state : State Symbol Guard) :
    Outcome Symbol Guard (Value Symbol Guard) :=
  (matched entry body depth ordinary name state).bind fun value after => work (withoutSelfReference name value) after

/-- Source reconstruction retains both probe calls, its canonical request, and smart cleanup. -/
def rebuild [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  (callback entry body depth ordinary .depth state).bind fun actualDepth afterDepth =>
  (callback entry body depth ordinary (.uninterned (ordinaryLevel actualDepth)) afterDepth).bind fun actualOrdinary afterOrdinary =>
    request true actualDepth actualOrdinary (callback entry body depth ordinary) afterOrdinary

/-- The actual Depth probe uses the cached record and leaves the cache unchanged. -/
theorem depth_call [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (clean : Clean depth ordinary) :
    callback entry body depth ordinary .depth state = .done depth state := by
  simp only [callback, matched, probeReadback_depth, Outcome.bind, work, filter_fixed _ _ _ clean.1]

/-- The actual ordinary argument is selected from that exact cached Depth probe. -/
theorem ordinary_call [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (clean : Clean depth ordinary) :
    callback entry body depth ordinary (.uninterned (ordinaryLevel depth)) state = .done ordinary state := by
  simp only [callback, matched, probeReadback_ordinary, Outcome.bind, work, filter_fixed _ _ _ clean.2]

/-- A coherent resident Mu supplies a complete canonical hit for arbitrary fresh-body code. -/
theorem resident_hit [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary))
    (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard)) :
    request true depth ordinary call state = .done (cleanup (.mu entry body depth ordinary)) state := by
  have stored := available.resident entry rfl
  obtain ⟨actual, installed, fields⟩ := coherent.nodes entry.key _ stored
  change entry = actual ∧ entry.key = muKey depth ordinary at fields
  cases fields.1
  rw [fields.2] at stored installed
  simp only [request, installed, stored, finish, ↓reduceIte]

/-- Both cached probes and residency derive the complete source result and the unchanged cache. -/
theorem completed [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary)) (clean : Clean depth ordinary) :
    rebuild entry body depth ordinary state = .done (cleanup (.mu entry body depth ordinary)) state := by
  simp only [rebuild, depth_call entry body depth ordinary state clean, Outcome.bind,
    ordinary_call entry body depth ordinary state clean]
  exact resident_hit entry body depth ordinary state coherent available _

/-- Source origins discharge both probe-filter premises without a supplied binder meaning law. -/
theorem from_origins [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary)) (origins : InternedFreshOrdinarySemanticOrigins.Heap state) :
    rebuild entry body depth ordinary state = .done (cleanup (.mu entry body depth ordinary)) state :=
  completed entry body depth ordinary state coherent available
    (InternedFreshOrdinaryProbeFilter.resident_clean state origins entry body depth ordinary available)

/-- The concrete completed reconstruction preserves availability, closure, and exact guarded meaning. -/
theorem verified [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state (.mu entry body depth ordinary)) (clean : Clean depth ordinary)
    (holds : Guard → Language.Term Symbol → Bool) (environment : InternedGuardedLanguage.Env Symbol) :
    rebuild entry body depth ordinary state = .done (cleanup (.mu entry body depth ordinary)) state ∧
      Available state (cleanup (.mu entry body depth ordinary)) ∧
      (cleanup (.mu entry body depth ordinary)).free = (Value.mu entry body depth ordinary).free ∧
      InternedGuardedLanguage.meaning holds environment (cleanup (.mu entry body depth ordinary)) =
        InternedGuardedLanguage.meaning holds environment (.mu entry body depth ordinary) :=
  ⟨completed entry body depth ordinary state coherent available clean,
    InternedConstructionProvenance.cleanup_available _ available,
    InternedNormalizationFree.cleanup_free _,
    InternedGuardedLanguage.cleanup_exact holds environment _ state coherent available⟩

end MicroCFTA.SourceEqualityMuReconstruction
