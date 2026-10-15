import MicroCFTA.SourceMergedContracts

/-!
# Successful retained-column coverage

The actual repaired filter preserves the independent union language.
Each retained-column branch preserves complete caches and covers its
original operands. Recursive correctness is local to actual calls.
-/
namespace MicroCFTA.SourceMergedColumns
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map retainedColumn small)
open InternedGuardedLanguage (meaning)
open SourceMergedContracts

/-- Positional value coverage transfers an accepted request row to its actual results. -/
theorem covers_runs (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (operands : Request → List (Value Symbol Guard)) (requests : List Request) (results : List (Value Symbol Guard))
    (after : State Symbol Guard) (covered : All₂ (fun request result => ValuePost holds ambient (operands request) after result) requests results)
    (terms : List (Term Symbol)) (accepted : All₂ (fun request term => ∃ value ∈ operands request, meaning holds ambient value term) requests terms) :
    All₂ (meaning holds ambient) results terms := by
  induction covered generalizing terms with
  | nil => cases accepted; exact .nil
  | cons head tail ih =>
      cases accepted with
      | cons accepted rest =>
          obtain ⟨value, member, run⟩ := accepted
          exact .cons (head.covers value member _ run) (ih _ rest)

/-- Every successful retained source branch preserves semantic caches and covers the original retained list. -/
theorem retained_done [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (law : RecurseLaw call holds ambient)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : retainedColumn call inputs before = .done result after) :
    Effect before after ∧ ValuePost holds ambient inputs after result := by
  have branches (values : List (Value Symbol Guard)) (available : Values before values) (closed : ClosedValues values)
      (done : (if values.any MergedOrdinaryHeight.recursiveBoundary then work (makeUnion values)
        else bind (work (MergedOrdinaryHeight.ordinaryUnion values)) call) before = .done result after) :
      Effect before after ∧ ValuePost holds ambient values after result := by
    by_cases boundary : values.any MergedOrdinaryHeight.recursiveBoundary = true
    · simp only [boundary, ite_true, work] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.union values before semantic available closed
      refine ⟨checked.1, checked.2.1, checked.2.2, ?_⟩
      intro value member term accepted
      exact (MergedColdInterpretation.makeUnion_common before semantic.ready.semantic.1.normal.facts
        (meaning holds ambient) values available holds (InternedGuardedLanguage.laws holds ambient) term).mpr ⟨value, member, accepted⟩
    · simp only [boundary, Bool.false_eq_true, ite_false] at done
      obtain ⟨united, middle, constructed, called⟩ := (bind_done _ _ result after).mp done
      have parts := Result.done.inj constructed
      cases parts.1; cases parts.2
      have checked := SourceMergedCache.ordinary_exact holds ambient values before semantic available closed (Bool.eq_false_iff.mpr boundary)
      have next := law _ _ checked.1.2 checked.2.1 checked.2.2.1 result after called
      refine ⟨checked.1.trans next.1, next.2.available, next.2.closed, ?_⟩
      intro value member term accepted
      exact next.2.covers _ List.mem_cons_self term ((checked.2.2.2 term).mpr ⟨value, member, accepted⟩)
  cases inputs with
  | nil => exact branches [] available closed done
  | cons first rest =>
      cases rest with
      | nil =>
          have parts := Result.done.inj done
          cases parts.1; cases parts.2
          refine ⟨⟨pure_keeps _ semantic.ready, semantic⟩, available _ List.mem_cons_self, closed _ List.mem_cons_self, ?_⟩
          intro value member term accepted
          simpa only [List.mem_singleton.mp member] using accepted
      | cons second rest => exact branches (first :: second :: rest) available closed done

/-- A successful repaired column merge covers every original operand after the actual ordered filter. -/
theorem column_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (fuel : Nat) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (law : RecurseLaw call holds ambient)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.column call clear fuel inputs before = .done result after) :
    Effect before after ∧ ValuePost holds ambient inputs after result := by
  obtain ⟨selected, middle, filtered, called⟩ := (bind_done _ _ result after).mp done
  have checked := SourceMergedSelectionLanguage.select_exact clear fuel holds ambient clearTrue inputs before semantic available closed selected middle filtered
  have next := retained_done call holds ambient law selected middle checked.1.2 checked.2.1 checked.2.2.1 result after called
  refine ⟨checked.1.trans next.1, next.2.available, next.2.closed, ?_⟩
  intro value member term accepted
  obtain ⟨kept, present, run⟩ := (checked.2.2.2.2 term).mpr ⟨value, member, accepted⟩
  exact next.2.covers kept present term run

end MicroCFTA.SourceMergedColumns
