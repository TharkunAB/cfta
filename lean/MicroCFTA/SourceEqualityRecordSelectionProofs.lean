import MicroCFTA.SourceEqualityRecordSelectionWorker

/-!
# Physical record selection function and graph agreement

Every completed receipt list has the actual source class query graph.
Conversely, every complete graph supplies a finite stable query bound.
Selected record paths equal the existing source selection path result.
-/
namespace MicroCFTA.SourceEqualityRecordSelectionProofs
open InternedConstructorTemplates InternedNestedConstruction SourceEqualityClassOrder
open InternedSourceClassSelection (Query Trace selected)
open SourceEqualityRecordSelectionWorker

variable [DecidableEq (EdgeKey Symbol Guard)]
variable (unconstrained : Value Symbol Guard → Bool)

/-- Successful physical record query execution derives the exact existing ordered source trace. -/
theorem queries_graph (fuel : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : State Symbol Guard) (actual : List (Query Symbol Guard)) (after : State Symbol Guard)
    (done : queries unconstrained fuel values records before = .done (some actual) after) :
    Trace unconstrained values (records.map Record.paths) before actual after := by
  induction records generalizing before actual after with
  | nil =>
      have parts := Outcome.done.inj done
      have same := Option.some.inj parts.1
      cases same; cases parts.2; exact .nil
  | cons record records ih =>
      cases first : InternedFreshOrdinaryStatefulGate.classMeets unconstrained fuel values record.paths before with
      | pending => simp only [queries, first, Outcome.bind] at done; cases done
      | done answer middle =>
          cases answer with
          | none => simp only [queries, first, Outcome.bind] at done; cases done
          | some blocked =>
              cases rest : queries unconstrained fuel values records middle with
              | pending => simp only [queries, first, rest, Outcome.bind] at done; cases done
              | done output final =>
                  cases output with
                  | none => simp only [queries, first, rest, Outcome.bind, Option.map_none] at done; cases done
                  | some tail =>
                      simp only [queries, first, rest, Outcome.bind, Option.map_some, Outcome.done.injEq, Option.some.injEq] at done
                      rcases done with ⟨rfl, rfl⟩
                      exact .cons (InternedFreshOrdinaryStatefulGateTrace.class_trace_of_done unconstrained fuel values record.paths before blocked middle first)
                        (ih middle tail final rest)

/-- Every complete physical record query graph has finite execution at all larger query bounds. -/
theorem queries_stable (values : List (Value Symbol Guard)) (records : List Record) (before : State Symbol Guard)
    (actual : List (Query Symbol Guard)) (after : State Symbol Guard)
    (trace : Trace unconstrained values (records.map Record.paths) before actual after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → queries unconstrained fuel values records before = .done (some actual) after := by
  induction records generalizing before actual after with
  | nil =>
      cases trace
      exact ⟨0, by intros; rfl⟩
  | cons record records ih =>
      cases trace with
      | cons first rest =>
          obtain ⟨firstBound, firstDone⟩ := InternedFreshOrdinaryStatefulGateTrace.class_trace_complete unconstrained values record.paths _ _ _ first
          obtain ⟨restBound, restStable⟩ := ih _ _ _ rest
          refine ⟨max firstBound restBound, ?_⟩
          intro fuel enough
          have firstMore := InternedFreshOrdinaryStatefulGate.class_fuel_stable unconstrained firstBound (fuel - firstBound) values record.paths _ _ _ firstDone
          have firstStable := firstMore
          rw [Nat.add_sub_of_le (Nat.le_trans (Nat.le_max_left _ _) enough)] at firstStable
          simp only [queries, firstStable, Outcome.bind, restStable fuel (Nat.le_trans (Nat.le_max_right _ _) enough), Option.map_some]

/-- Physical query traces and successful bounded record query execution agree in both directions. -/
theorem queries_iff (values : List (Value Symbol Guard)) (records : List Record) (before : State Symbol Guard)
    (actual : List (Query Symbol Guard)) (after : State Symbol Guard) :
    Trace unconstrained values (records.map Record.paths) before actual after ↔
      ∃ fuel, queries unconstrained fuel values records before = .done (some actual) after := by
  constructor
  · intro trace
    obtain ⟨bound, stable⟩ := queries_stable unconstrained values records before actual after trace
    exact ⟨bound, stable bound (Nat.le_refl _)⟩
  · rintro ⟨fuel, done⟩
    exact queries_graph unconstrained fuel values records before actual after done

/-- Completed physical record selection has the same selected path list as the existing source selector. -/
theorem select_paths (fuel : Nat) (values : List (Value Symbol Guard)) (records : List Record)
    (before : State Symbol Guard) (actual : List (Query Symbol Guard)) (after : State Symbol Guard)
    (done : queries unconstrained fuel values records before = .done (some actual) after) :
    (SourceEqualitySelectedRecords.keep records actual).map Record.paths = selected actual ∧
      select unconstrained fuel values records before = .done (some (SourceEqualitySelectedRecords.keep records actual)) after := by
  exact ⟨SourceEqualitySelectedRecords.trace_paths (queries_graph unconstrained fuel values records before actual after done),
    by simp only [select, done, Outcome.bind, Option.map_some]⟩

end MicroCFTA.SourceEqualityRecordSelectionProofs
