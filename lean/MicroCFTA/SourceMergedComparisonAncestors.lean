import MicroCFTA.SourceMergedComparisonEffects
import MicroCFTA.MergedComparisonPreparedSoundness

/-!
# Scoped independent-language comparison ancestors

Each visited numeric pair retains actual closed available record witnesses.
Cache growth keeps these witnesses. Coherent identity readback determines
which physical records a later visited comparison denotes.
-/
namespace MicroCFTA.SourceMergedComparisonAncestors
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (identity)
open InternedGuardedLanguage (meaning)

/-- A pair transfers every accepted term through a fixed constructor height. -/
def Bounded (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (rank : Nat) (wide narrow : Value Symbol Guard) : Prop :=
  ∀ term, term.height ≤ rank → meaning holds ambient narrow term → meaning holds ambient wide term

/-- Visited identities retain their real closed available witnesses and independent finite-term law. -/
def Ancestors (state : State Symbol Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (rank : Nat) (above : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ above, ∃ wide narrow, Available state wide ∧ Available state narrow ∧ wide.free = [] ∧ narrow.free = [] ∧
    identity wide = some pair.1 ∧ identity narrow = some pair.2 ∧ Bounded holds ambient rank wide narrow

/-- Actual cache histories retain every recorded ancestor witness. -/
theorem Ancestors.grows {before after : State Symbol Guard} (keeps : Keeps before after)
    {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol} {rank : Nat} {above : List (Nat × Nat)}
    (ancestors : Ancestors before holds ambient rank above) : Ancestors after holds ambient rank above := by
  intro pair member
  obtain ⟨wide, narrow, wideKnown, narrowKnown, wideClosed, narrowClosed, wideId, narrowId, bounded⟩ := ancestors pair member
  exact ⟨wide, narrow, keeps.available wide wideKnown, keeps.available narrow narrowKnown, wideClosed, narrowClosed, wideId, narrowId, bounded⟩

/-- Ancestor inclusion at a larger height includes every smaller height. -/
theorem Ancestors.mono {state : State Symbol Guard} {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol}
    {rank smaller : Nat} {above : List (Nat × Nat)} (ancestors : Ancestors state holds ambient rank above) (bound : smaller ≤ rank) :
    Ancestors state holds ambient smaller above := by
  intro pair member
  obtain ⟨wide, narrow, wideKnown, narrowKnown, wideClosed, narrowClosed, wideId, narrowId, bounded⟩ := ancestors pair member
  exact ⟨wide, narrow, wideKnown, narrowKnown, wideClosed, narrowClosed, wideId, narrowId,
    fun term height accepted => bounded term (Nat.le_trans height bound) accepted⟩

/-- A newly visited pair records the actual operands in their real current cache. -/
theorem Ancestors.cons {state : State Symbol Guard} {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol}
    {rank : Nat} {above : List (Nat × Nat)} (ancestors : Ancestors state holds ambient rank above)
    (wide narrow : Value Symbol Guard) (wideKnown : Available state wide) (narrowKnown : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) (wideId narrowId : Nat)
    (wideFound : identity wide = some wideId) (narrowFound : identity narrow = some narrowId)
    (bounded : Bounded holds ambient rank wide narrow) : Ancestors state holds ambient rank ((wideId, narrowId) :: above) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨wide, narrow, wideKnown, narrowKnown, wideClosed, narrowClosed, wideFound, narrowFound, bounded⟩
  · exact ancestors pair tail

/-- A visited numeric pair denotes the same coherent closed operands as its recorded witnesses. -/
theorem Ancestors.apply (state : State Symbol Guard) (semantic : SemanticReady state)
    {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol} {rank : Nat} {above : List (Nat × Nat)}
    (ancestors : Ancestors state holds ambient rank above) (wide narrow : Value Symbol Guard)
    (wideKnown : Available state wide) (narrowKnown : Available state narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (wideId narrowId : Nat) (wideFound : identity wide = some wideId) (narrowFound : identity narrow = some narrowId)
    (member : (wideId, narrowId) ∈ above) : Bounded holds ambient rank wide narrow := by
  obtain ⟨actualWide, actualNarrow, actualWideKnown, actualNarrowKnown, actualWideClosed, actualNarrowClosed, actualWideId, actualNarrowId, bounded⟩ :=
    ancestors (wideId, narrowId) member
  have wideSame := MergedComparisonPreparedSoundness.identity_injective state semantic.ready.semantic.1.normal.facts
    wide actualWide wideKnown actualWideKnown wideClosed actualWideClosed wideId wideFound actualWideId
  have narrowSame := MergedComparisonPreparedSoundness.identity_injective state semantic.ready.semantic.1.normal.facts
    narrow actualNarrow narrowKnown actualNarrowKnown narrowClosed actualNarrowClosed narrowId narrowFound actualNarrowId
  simpa only [wideSame, narrowSame] using bounded

end MicroCFTA.SourceMergedComparisonAncestors
