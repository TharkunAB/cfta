import MicroCFTA.SourceCurrentMemoMergeEffects

/-!
# Language contracts for recursive memo-aware merging

Coverage refers to the independent guarded language. The initial empty
cache satisfies it. Source body certificates must derive coverage for each
new result. A warm entry is checked at its stored original record.
-/
namespace MicroCFTA.SourceCurrentMemoMergeLanguage
open Cache Language InternedConstructorTemplates InternedGuardedLanguage
open SourceCurrentMemoMergeGraph SourceCurrentMemoMergeEffects

/-- One result retains every independently accepted term of its input. -/
def Covers (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (input output : Value Symbol Guard) : Prop :=
  ∀ term, meaning holds ambient input term → meaning holds ambient output term

/-- Every completed entry retains the accepted terms of its stored original record. -/
def CacheCovers (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → Covers holds ambient entry.original entry.result

/-- Empty tables contain no unsupported semantic answer. -/
theorem cache_covers_empty (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol) :
    CacheCovers holds ambient empty := by
  intro key entry impossible
  cases impossible

/-- First-writer completion preserves old coverage and checks the new candidate. -/
theorem cache_covers_remember {holds : Guard → Term Symbol → Bool} {ambient : Env Symbol}
    {memo : Memo Symbol Guard} (covered : CacheCovers holds ambient memo)
    (input output : Value Symbol Guard) (covers : Covers holds ambient input output) :
    CacheCovers holds ambient (remember memo input output) := by
  intro key entry found
  rcases InternedRecordCoherence.record_cases memo input.referenceOf key ⟨input, output⟩ entry found with old | ⟨_, same⟩
  · exact covered key entry old
  · subst entry
    exact covers

/-- The semantic request contract includes the physical output and conditional closedness. -/
def Contract (holds : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (input : Value Symbol Guard) (before : State Symbol Guard)
    (output : Value Symbol Guard) (after : State Symbol Guard) : Prop :=
  SourceCurrentMemoMergeEffects.Contract input before output after ∧ Covers holds ambient input output

end MicroCFTA.SourceCurrentMemoMergeLanguage
