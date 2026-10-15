import MicroCFTA.SourceMergedGroups

/-!
# Independent language coverage of general repaired merging

Every successful bounded execution on a closed available value preserves
the full semantic cache and covers its independent guarded least language.
This theorem does not require prepared Mu bodies or completed callbacks.
Finite completion of the general comparator remains a separate obligation.
-/
namespace MicroCFTA.SourceMergedSoundness
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open InternedGuardedLanguage (meaning)
open SourceMergedContracts SourceMergedGroups

/-- A returned original value has no effects and covers its exact original language. -/
theorem boundary_done (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : Result.done value before = .done result after) : Effect before after ∧ ValuePost holds ambient [value] after result := by
  have parts := Result.done.inj done
  cases parts.1; cases parts.2
  refine ⟨⟨pure_keeps _ semantic.ready, semantic⟩, available, closed, ?_⟩
  intro original member term accepted
  simpa only [List.mem_singleton.mp member] using accepted

/-- Every successful actual ordinary recursion covers its input, with general repaired comparisons. -/
theorem worker_done [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (groupingCorrect : ∀ edges, MergedPhysicalGroupRoot.Grouping edges (grouping edges))
    (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (ordinaryFuel comparisonFuel : Nat) : RecurseLaw (SourceMergedWorker.worker grouping clear top ordinaryFuel comparisonFuel) holds ambient := by
  induction ordinaryFuel with
  | zero =>
      intro value before semantic available closed result after done
      cases value with
      | node entry edges depth free =>
          simp only [Value.free] at closed
          simp only [SourceMergedWorker.worker, closed, ite_true] at done
          cases done
      | empty | reference | mu | union => exact boundary_done holds ambient _ before semantic available closed result after done
  | succ remaining ih =>
      intro value before semantic available closed result after done
      cases value with
      | node entry edges depth free =>
          have facts := semantic.ready.semantic.1.normal.facts
          have resident : Edges before edges := InternedEdgeResidency.resident_edges before facts.linked _ available.resident
          have rowsClosed : ClosedEdges edges := fun edge member child included =>
            MergedOrdinaryHeight.closed_child before facts.coherent entry edges depth free available.resident closed edge member child included
          have checked := root_done (SourceMergedWorker.worker grouping clear top remaining comparisonFuel) clear comparisonFuel holds ambient clearTrue ih top topTrue
            edges (grouping edges) (groupingCorrect edges) before semantic resident rowsClosed result after (by
              simpa only [SourceMergedWorker.worker, show free = [] from closed, ite_true] using done)
          refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_⟩
          intro original member term accepted
          rw [List.mem_singleton.mp member] at accepted
          obtain ⟨edge, included, run⟩ := ((InternedGuardedLanguage.laws holds ambient).node entry edges depth free term).mp accepted
          exact checked.2.2.2 edge included term run
      | empty | reference | mu | union => exact boundary_done holds ambient _ before semantic available closed result after done

/-- The executable source grouping and derived ordinary height have the same successful-run coverage law. -/
theorem execute_covers [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (comparisonFuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : SourceMergedWorker.execute clear top comparisonFuel value before = .done result after) :
    Effect before after ∧ Available after result ∧ result.free = [] ∧
      ∀ term, meaning holds ambient value term → meaning holds ambient result term := by
  have checked := worker_done MergedSourceGrouping.groups MergedSourceGrouping.groups_correct clear top holds ambient clearTrue topTrue
    (MergedOrdinaryHeight.height value) comparisonFuel value before semantic available closed result after done
  exact ⟨checked.1, checked.2.available, checked.2.closed, checked.2.covers value List.mem_cons_self⟩

end MicroCFTA.SourceMergedSoundness
