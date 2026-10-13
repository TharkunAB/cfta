import MicroCFTA.MergedColdGraphTransport
import MicroCFTA.MergedColdMergeSoundness

/-!
# Original cold-cache language included by actual merge results

The complete worker includes each term accepted before any merge effect.
The result accepts that term in its actual returned cache and later caches.
-/
namespace MicroCFTA.MergedColdMergeOriginalLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedPhysicalLanguage MergedColdMerge Language

/-- Cold extension retains the original available record's exact finite language. -/
theorem extension_exact [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (extension : Extension before after) (meaning : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (available : Available before value) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph before meaning) value term ↔ EpsilonUnion.Accepts (graph after meaning) value term :=
  MergedColdGraphTransport.accepts_stable before after facts extension.facts prepared extension.growth extension.history
    meaning value available term

/-- The completed source-grouped worker covers the original cold-cache language at its returned cache. -/
theorem source_execute_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) :
    ∃ bound result after, (∀ comparisonFuel, bound ≤ comparisonFuel →
      execute MergedSourceGrouping.groups clear top comparisonFuel value state = .done result after) ∧
      Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph state meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph state meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term := by
  obtain ⟨bound, result, after, done, extension, resident, covered, later⟩ :=
    MergedColdMergeSoundness.source_execute_complete clear meaning clearTrue top topTrue value state facts prepared available
  refine ⟨bound, result, after, done, extension, resident, ?_, ?_⟩
  · intro term accepted
    exact covered term ((extension_exact state after facts prepared extension meaning value available term).mp accepted)
  · intro view next term accepted
    exact later view next term
      ((extension_exact state view facts prepared (extension.trans next) meaning value available term).mp accepted)

/-- Every successful source worker fuel pair covers the original cold-cache finite language. -/
theorem source_successful_sound [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (meaning : Guard → Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (top : Guard) (topTrue : ∀ term, meaning top term = true)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (ordinary comparison : Nat) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : worker MergedSourceGrouping.groups clear top ordinary comparison value state = .done result after) :
    Extension state after ∧ Available after result ∧
      (∀ term, EpsilonUnion.Accepts (graph state meaning) value term → EpsilonUnion.Accepts (graph after meaning) result term) ∧
      ∀ view, Extension after view → ∀ term,
        EpsilonUnion.Accepts (graph state meaning) value term → EpsilonUnion.Accepts (graph view meaning) result term := by
  obtain ⟨extension, resident, covered, later⟩ := MergedColdMergeSoundness.source_successful_sound
    clear meaning clearTrue top topTrue value state facts prepared available ordinary comparison result after done
  refine ⟨extension, resident, ?_, ?_⟩
  · intro term accepted
    exact covered term ((extension_exact state after facts prepared extension meaning value available term).mp accepted)
  · intro view next term accepted
    exact later view next term
      ((extension_exact state view facts prepared (extension.trans next) meaning value available term).mp accepted)

end MicroCFTA.MergedColdMergeOriginalLanguage
