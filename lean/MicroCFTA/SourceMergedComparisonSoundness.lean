import MicroCFTA.SourceMergedComparisonCertificates

/-!
# Independent-language soundness of general repaired source comparison

Induction on accepted term height justifies visited-pair reuse. Each numeric
pair retains coherent available witnesses through actual cache growth.
Actual read and comparison receipts supply every intermediate cache premise.
-/
namespace MicroCFTA.SourceMergedComparisonSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects SourceMergedComparisonAncestors SourceMergedComparisonCertificates
open MergedSourceComparison (identity)
open MergedFreshOrdinaryComparison (check)
open InternedGuardedLanguage (meaning)

/-- Actual completed repaired comparisons transfer all finite terms justified by their scoped ancestor witnesses. -/
theorem check_bounded [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (rank fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done true after)
    (ancestors : Ancestors before holds ambient rank above) : Bounded holds ambient rank wide narrow := by
  cases rank with
  | zero =>
      intro term height accepted
      have positive := term.height_pos
      omega
  | succ rank =>
      have originalDone := done
      intro term height accepted
      rw [check] at done
      by_cases narrowEmpty : narrow.referenceOf = .empty
      · have same : narrow = .empty := by cases narrow <;> simp_all [Value.referenceOf]
        exact False.elim ((InternedGuardedLanguage.laws holds ambient).empty term (same ▸ accepted))
      simp only [narrowEmpty, ite_false] at done
      by_cases wideEmpty : wide.referenceOf = .empty
      · simp only [wideEmpty, ite_true] at done
        cases done
      simp only [wideEmpty, ite_false] at done
      by_cases same : wide.referenceOf = narrow.referenceOf
      · have equal := (MergedPhysicalComparison.same_record before semantic.ready.semantic.1.normal.facts wide narrow wideInput narrowInput).mp same
        simpa only [equal] using accepted
      simp only [same, ite_false] at done
      cases wideFound : identity wide with
      | none => simp only [wideFound] at done; cases done
      | some wideId =>
          cases narrowFound : identity narrow with
          | none => simp only [wideFound, narrowFound] at done; cases done
          | some narrowId =>
              simp only [wideFound, narrowFound] at done
              by_cases visited : (wideId, narrowId) ∈ above
              · exact ancestors.apply before semantic wide narrow wideInput narrowInput wideClosed narrowClosed wideId narrowId wideFound narrowFound visited term height accepted
              simp only [visited, ite_false] at done
              have oldAncestors := ancestors.mono (Nat.le_succ rank)
              have current := check_bounded clear holds ambient clearTrue rank fuel above wide narrow before semantic
                wideInput narrowInput wideClosed narrowClosed after originalDone oldAncestors
              have nextAncestors := oldAncestors.cons wide narrow wideInput narrowInput wideClosed narrowClosed wideId narrowId wideFound narrowFound current
              cases fuel with
              | zero => cases done
              | succ fuel =>
                  obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ true after).mp done
                  have readTrace := read_graph (fuel + 1) narrow before narrows middle read
                  have readFacts := readTrace.verified semantic narrowInput narrowClosed
                  have certifies : Certifies (check clear fuel ((wideId, narrowId) :: above)) holds ambient rank ((wideId, narrowId) :: above) := by
                    intro state stateSemantic localAncestors left right leftInput rightInput leftClosed rightClosed final actual
                    exact check_bounded clear holds ambient clearTrue rank fuel ((wideId, narrowId) :: above) left right state stateSemantic
                      leftInput rightInput leftClosed rightClosed final actual localAncestors
                  have rows := allRows_certificate (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                    (check_effect clear fuel ((wideId, narrowId) :: above)) holds ambient rank ((wideId, narrowId) :: above) clearTrue certifies
                    wide narrows middle readFacts.2.1 (nextAncestors.grows readFacts.1) (readFacts.1.available wide wideInput)
                    readFacts.2.2.1 wideClosed readFacts.2.2.2 after later
                  obtain ⟨edge, member, run⟩ := (readTrace.exact semantic narrowInput narrowClosed holds ambient term).mpr accepted
                  exact rows edge member term height run
termination_by rank

/-- Every true general closed source comparison implies independent guarded-language inclusion. -/
theorem check_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (fuel : Nat) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (after : State Symbol Guard) (done : check clear fuel [] wide narrow before = .done true after) :
    ∀ term, meaning holds ambient narrow term → meaning holds ambient wide term := by
  intro term accepted
  exact check_bounded clear holds ambient clearTrue term.height fuel [] wide narrow before semantic wideInput narrowInput wideClosed narrowClosed
    after done (by intro pair impossible; cases impossible) term (Nat.le_refl _) accepted

end MicroCFTA.SourceMergedComparisonSoundness
