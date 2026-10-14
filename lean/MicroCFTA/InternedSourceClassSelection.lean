import MicroCFTA.InternedFreshOrdinaryStatefulGateClasses

/-!
# Ordered source equality-class selection with returned constructor caches

Every class queries the original child list. A blocked class is discarded,
then the remaining classes run in their original order. Missing gate fuel
and pending constructor requests remain separate from completed decisions.
-/
namespace MicroCFTA.InternedSourceClassSelection
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize
open InternedFreshOrdinaryStatefulGate

/-- One class occurrence retains its exact input cache, Boolean, and output cache. -/
structure Query (Symbol Guard : Type) where
  paths : Class
  before : State Symbol Guard
  blocked : Bool
  after : State Symbol Guard

/-- Keep the clear class occurrences in their original order. -/
def selected (queries : List (Query Symbol Guard)) : Constraints :=
  (queries.filter (fun query => !query.blocked)).map Query.paths

/-- One completed query either retains its class or removes only that occurrence. -/
theorem selected_cons (query : Query Symbol Guard) (queries : List (Query Symbol Guard)) :
    selected (query :: queries) = if query.blocked then selected queries else query.paths :: selected queries := by
  cases blocked : query.blocked <;> simp [selected, blocked]

/-- Select all local classes with source order and the actual cache returned by each class query. -/
def select [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) : Constraints → State Symbol Guard → Outcome Symbol Guard (Option Constraints)
  | [], state => .done (some []) state
  | paths :: rest, state => (classMeets unconstrained fuel values paths state).bind fun answer after =>
      match answer with
      | none => .done none after
      | some blocked => (select unconstrained fuel values rest after).bind fun kept final =>
          .done (kept.map (fun output => if blocked then output else paths :: output)) final

/-- Each class occurrence has a complete source gate graph in its actual intermediate cache. -/
inductive Trace [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) : Constraints → State Symbol Guard → List (Query Symbol Guard) → State Symbol Guard → Prop where
  | nil : Trace unconstrained values [] state [] state
  | cons (head : InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths state blocked middle)
      (tail : Trace unconstrained values rest middle queries final) :
      Trace unconstrained values (paths :: rest) state (⟨paths, state, blocked, middle⟩ :: queries) final

/-- A completed selection keeps exactly the same classes and constructor cache at all larger fuel amounts. -/
theorem fuel_stable [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel extra : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (state : State Symbol Guard) (kept : Constraints) (final : State Symbol Guard)
    (done : select unconstrained fuel values classes state = .done (some kept) final) :
    select unconstrained (fuel + extra) values classes state = .done (some kept) final := by
  induction classes generalizing state kept final with
  | nil => simpa only [select] using done
  | cons paths rest ih =>
      cases head : classMeets unconstrained fuel values paths state with
      | pending key after => simp [select, head, Outcome.bind] at done
      | done answer after =>
          cases answer with
          | none => simp [select, head, Outcome.bind] at done
          | some blocked =>
              have headMore := class_fuel_stable unconstrained fuel extra values paths state blocked after head
              cases tail : select unconstrained fuel values rest after with
              | pending key next => simp [select, head, tail, Outcome.bind] at done
              | done output next =>
                  cases output with
                  | none => simp [select, head, tail, Outcome.bind] at done
                  | some output =>
                      have tailMore := ih after output next tail
                      simpa only [select, head, tail, headMore, tailMore, Outcome.bind] using done

/-- Every completed worker produces one ordered complete receipt per original class occurrence. -/
theorem trace_of_done [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (fuel : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (state : State Symbol Guard) (kept : Constraints) (final : State Symbol Guard)
    (done : select unconstrained fuel values classes state = .done (some kept) final) :
    ∃ queries, Trace unconstrained values classes state queries final ∧ kept = selected queries := by
  induction classes generalizing state kept final with
  | nil =>
      simp only [select, Outcome.done.injEq, Option.some.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact ⟨[], .nil, rfl⟩
  | cons paths rest ih =>
      cases head : classMeets unconstrained fuel values paths state with
      | pending key after => simp [select, head, Outcome.bind] at done
      | done answer after =>
          cases answer with
          | none => simp [select, head, Outcome.bind] at done
          | some blocked =>
              cases tail : select unconstrained fuel values rest after with
              | pending key next => simp [select, head, tail, Outcome.bind] at done
              | done output next =>
                  cases output with
                  | none => simp [select, head, tail, Outcome.bind] at done
                  | some output =>
                      obtain ⟨queries, trace, keptEqual⟩ := ih after output next tail
                      simp only [select, head, tail, Outcome.bind, Option.map_some, Outcome.done.injEq, Option.some.injEq] at done
                      rcases done with ⟨rfl, rfl⟩
                      refine ⟨_, .cons (InternedFreshOrdinaryStatefulGateTrace.class_trace_of_done _ _ _ _ _ _ _ head) trace, ?_⟩
                      rw [selected_cons, keptEqual]

/-- Every complete selection graph has finite execution with its exact retained class order and cache. -/
theorem trace_complete [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints) (state : State Symbol Guard)
    (queries : List (Query Symbol Guard)) (final : State Symbol Guard)
    (trace : Trace unconstrained values classes state queries final) :
    ∃ fuel, select unconstrained fuel values classes state = .done (some (selected queries)) final := by
  induction trace with
  | nil => exact ⟨0, rfl⟩
  | cons head tail ih =>
      obtain ⟨headFuel, headDone⟩ := InternedFreshOrdinaryStatefulGateTrace.class_trace_complete _ _ _ _ _ _ head
      obtain ⟨tailFuel, tailDone⟩ := ih
      have headMore := class_fuel_stable unconstrained headFuel tailFuel _ _ _ _ _ headDone
      have tailMore := fuel_stable unconstrained tailFuel headFuel _ _ _ _ _ tailDone
      refine ⟨headFuel + tailFuel, ?_⟩
      rw [select, headMore]
      simp only [Outcome.bind]
      rw [Nat.add_comm headFuel tailFuel, tailMore]
      simp only [Option.map_some, selected_cons]

/-- Selection graphs and finite completed source execution have the same complete readback. -/
theorem trace_iff [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints) (state : State Symbol Guard)
    (kept : Constraints) (final : State Symbol Guard) :
    (∃ queries, Trace unconstrained values classes state queries final ∧ kept = selected queries) ↔
      ∃ fuel, select unconstrained fuel values classes state = .done (some kept) final := by
  constructor
  · rintro ⟨queries, trace, rfl⟩
    exact trace_complete _ _ _ _ _ _ trace
  · rintro ⟨fuel, done⟩
    exact trace_of_done _ _ _ _ _ _ _ done

/-- Every original class occurrence has exactly one receipt in its original order. -/
theorem Trace.original [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final) : queries.map Query.paths = classes := by
  induction trace with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, ih]

/-- Selection retains an ordered sublist, including every repeated clear occurrence. -/
theorem Trace.sublist [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final) : (selected queries).Sublist classes := by
  rw [← trace.original]
  exact List.Sublist.map Query.paths List.filter_sublist

/-- Each retained class has a complete false gate query in its actual input and output cache. -/
theorem Trace.selected_witness [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool}
    (trace : Trace unconstrained values classes state queries final) (paths : Class) (member : paths ∈ selected queries) :
    ∃ before after, InternedFreshOrdinaryStatefulGateTrace.ClassTrace unconstrained values paths before false after := by
  induction trace with
  | nil => simp [selected] at member
  | cons head tail ih =>
      rw [selected_cons] at member
      split at member
      · exact ih member
      · rcases List.mem_cons.mp member with rfl | member
        · rename_i clear
          have equal : _ = false := Bool.eq_false_iff.mpr clear
          dsimp only at equal
          exact ⟨_, _, equal ▸ head⟩
        · exact ih member

end MicroCFTA.InternedSourceClassSelection
