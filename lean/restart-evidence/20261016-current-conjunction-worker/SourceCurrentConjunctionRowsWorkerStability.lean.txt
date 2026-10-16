import MicroCFTA.SourceCurrentConjunctionRowsWorkerCompletion

/-!
# Successful bound stability for current conjunction rows

Larger projection and read bounds preserve each successful observation.
The equality identifies the complete constructor heap and equality cache.
Incomplete observations retain the worker's separate diagnostics.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsWorkerStability
open InternedConstructorTemplates SourceCurrentConjunctionRowsWorker
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

private theorem exposure_done_stable {fuel larger : Nat} {value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    [DecidableEq (EdgeKey Symbol Guard)]
    (actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done edges after) (enough : fuel ≤ larger) :
    MergedFreshOrdinaryExposure.nodeEdges larger value before = .done edges after := by
  have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel (larger - fuel) value before
    (by simp only [actual, MergedSourceExposure.Finished])
  rw [show fuel + (larger - fuel) = larger by omega] at stable
  exact stable.trans actual

private theorem readAll_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} (values : List (Value Symbol Guard))
    {before after : InternedConstructorTemplates.State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionWorker.readAll fuel values before = .done edges after) (enough : fuel ≤ larger) :
    SourceEqualityProjectionWorker.readAll larger values before = .done edges after := by
  induction values generalizing before edges after with
  | nil => exact actual
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
      | done rows middle =>
          simp only [SourceEqualityProjectionWorker.readAll, read] at actual
          obtain ⟨more, final, rest, returned⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ edges after).mp actual
          simp only [SourceEqualityProjectionWorker.readAll, exposure_done_stable read enough,
            SourceEqualityRequiredWorker.Result.bind, ih rest]
          exact returned
      | pending | unresolved | exhausted =>
          simp only [SourceEqualityProjectionWorker.readAll, read] at actual
          cases actual

private theorem union_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} {values : List (Value Symbol Guard)}
    {before after : InternedConstructorTemplates.State Symbol Guard} {value : Value Symbol Guard}
    (actual : SourceEqualityProjectionWorker.union fuel values before = .done value after) (enough : fuel ≤ larger) :
    SourceEqualityProjectionWorker.union larger values before = .done value after := by
  obtain ⟨edges, middle, read, built⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
  simp only [SourceEqualityProjectionWorker.union, readAll_done_stable values read enough,
    SourceEqualityRequiredWorker.Result.bind]
  exact built

private theorem head_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {fuel larger : Nat} {input value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityRequiredWorker.head fuel input before = .done value after) (enough : fuel ≤ larger) :
    SourceEqualityRequiredWorker.head larger input before = .done value after := by
  cases read : MergedFreshOrdinaryExposure.nodeEdges fuel input before with
  | done edges middle =>
      simp only [SourceEqualityRequiredWorker.head, read] at actual
      simpa only [SourceEqualityRequiredWorker.head, exposure_done_stable read enough] using actual
  | pending | unresolved | exhausted =>
      simp only [SourceEqualityRequiredWorker.head, read] at actual
      cases actual

private theorem projectRows_done_stable
    (first next : Value Symbol Guard → InternedConstructorTemplates.State Symbol Guard →
      SourceEqualityRequiredWorker.Result Symbol Guard (Value Symbol Guard))
    (stable : ∀ value before result after, first value before = .done result after → next value before = .done result after)
    (index : Int) (edges : List (EdgeValue Symbol Guard))
    {before after : InternedConstructorTemplates.State Symbol Guard} {results : List (Value Symbol Guard)}
    (actual : SourceEqualityProjectionWorker.rows first index edges before = .done results after) :
    SourceEqualityProjectionWorker.rows next index edges before = .done results after := by
  induction edges generalizing before results after with
  | nil => exact actual
  | cons edge edges ih =>
      cases selected : SourceEqualityProjectionGraph.select edge.children index with
      | none =>
          simp only [SourceEqualityProjectionWorker.rows, selected] at actual ⊢
          exact ih actual
      | some child =>
          simp only [SourceEqualityProjectionWorker.rows, selected] at actual
          obtain ⟨value, middle, firstDone, later⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ results after).mp actual
          obtain ⟨more, final, rest, returned⟩ := (SourceEqualityRequiredWorkerSound.bind_done _ _ results after).mp later
          simp only [SourceEqualityProjectionWorker.rows, selected, stable _ _ _ _ firstDone,
            SourceEqualityRequiredWorker.Result.bind, ih rest]
          exact returned

private theorem project_done_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    {larger readFuel largerRead : Nat} {path : List Int} {input value : Value Symbol Guard}
    {before after : InternedConstructorTemplates.State Symbol Guard}
    (actual : SourceEqualityProjectionWorker.project fuel readFuel path input before = .done value after)
    (enough : fuel ≤ larger) (readEnough : readFuel ≤ largerRead) :
    SourceEqualityProjectionWorker.project larger largerRead path input before = .done value after := by
  induction fuel generalizing larger path input value before after with
  | zero => cases actual
  | succ fuel ih =>
      cases larger with
      | zero => omega
      | succ remaining =>
          cases path with
          | nil => exact actual
          | cons index path =>
              cases input with
              | empty => exact actual
              | reference => cases actual
              | node entry edges depth free =>
                  obtain ⟨values, middle, rowsDone, built⟩ :=
                    (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
                  have rowsStable := projectRows_done_stable
                    (SourceEqualityProjectionWorker.project fuel readFuel path)
                    (SourceEqualityProjectionWorker.project remaining largerRead path)
                    (fun child state result final done => ih done (by omega)) index edges rowsDone
                  simp only [SourceEqualityProjectionWorker.project, rowsStable,
                    SourceEqualityRequiredWorker.Result.bind]
                  exact union_done_stable built readEnough
              | mu entry body depth free | union entry members depth free =>
                  obtain ⟨exposed, middle, headDone, rest⟩ :=
                    (SourceEqualityRequiredWorkerSound.bind_done _ _ value after).mp actual
                  simp only [SourceEqualityProjectionWorker.project, head_done_stable headDone readEnough,
                    SourceEqualityRequiredWorker.Result.bind]
                  exact ih rest (by omega)

/-- Increasing projection and read fuel preserves any successful forest and its complete heap. -/
theorem forest_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {projectionFuel readFuel largerProjection largerRead : Nat} {path : List Int}
    {values : List (Value Symbol Guard)} {before after : InternedConstructorTemplates.State Symbol Guard}
    {value : Value Symbol Guard}
    (actual : SourceEqualityProjectionWorker.forest projectionFuel readFuel path values before = .done value after)
    (enough : projectionFuel ≤ largerProjection) (readEnough : readFuel ≤ largerRead) :
    SourceEqualityProjectionWorker.forest largerProjection largerRead path values before = .done value after := by
  cases path with
  | nil => exact union_done_stable actual readEnough
  | cons index path =>
      cases selected : SourceEqualityProjectionGraph.select values index with
      | none => simpa only [SourceEqualityProjectionWorker.forest, selected] using actual
      | some input =>
          simp only [SourceEqualityProjectionWorker.forest, selected] at actual ⊢
          exact project_done_stable projectionFuel actual enough readEnough


/-- Completed sequencing exposes the exact physical intermediate state. -/
theorem bind_done_iff (first : Outcome Symbol Formula Input)
    (next : Input → Physical Symbol Formula → Outcome Symbol Formula Output)
    (result : Output) (after : Physical Symbol Formula) :
    first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro actual; exact ⟨value, state, rfl, actual⟩
      · rintro ⟨_, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

/-- Larger read fuel preserves each successful ordered exposure and both physical fields. -/
theorem exposures_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {h largerH : Nat} {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {edges : List (List (EdgeValue Symbol Guard))}
    (actual : exposures h nodes before = .done edges after) (enoughH : h ≤ largerH) :
    exposures largerH nodes before = .done edges after := by
  induction nodes generalizing before edges after with
  | nil => exact actual
  | cons value values ih =>
      cases read : MergedFreshOrdinaryExposure.nodeEdges h value before.heap with
      | done rows heap =>
          simp only [exposures, read] at actual
          obtain ⟨rest, final, restDone, returned⟩ := (bind_done_iff _ _ edges after).mp actual
          simp only [exposures, exposure_done_stable read enoughH, ih restDone, Outcome.bind]
          exact returned
      | pending | unresolved | exhausted => simp only [exposures, read] at actual; cases actual

/-- Larger independent bounds preserve every successful natural projection job. -/
theorem projections_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {jobs : List (Job Symbol Formula)} {before after : Physical Symbol Formula}
    {values : List (Value Symbol Guard)}
    (actual : projections p h jobs before = .done values after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    projections largerP largerH jobs before = .done values after := by
  induction jobs generalizing before values after with
  | nil => exact actual
  | cons job jobs ih =>
      obtain ⟨forest, path⟩ := job
      cases projected : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap with
      | done value heap =>
          simp only [projections, projected] at actual
          obtain ⟨rest, final, restDone, returned⟩ := (bind_done_iff _ _ values after).mp actual
          simp only [projections, forest_done_stable projected enoughP enoughH, ih restDone, Outcome.bind]
          exact returned
      | pending | unresolved | exhausted => simp only [projections, projected] at actual; cases actual

/-- Successful class projection preserves its exact canonical rows at larger bounds. -/
theorem classes_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {forests : List (List (Value Symbol Guard))} {constraints : EqualityNormalize.Constraints}
    {before after : Physical Symbol Formula} {rows : List (List (Value Symbol Guard))}
    (actual : classes p h forests constraints before = .done rows after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    classes largerP largerH forests constraints before = .done rows after := by
  induction constraints generalizing before rows after with
  | nil => exact actual
  | cons paths constraints ih =>
      obtain ⟨projected, middle, first, later⟩ := (bind_done_iff _ _ rows after).mp actual
      obtain ⟨rest, final, second, returned⟩ := (bind_done_iff _ _ rows after).mp later
      simp only [classes, projections_done_stable first enoughP enoughH, ih second, Outcome.bind]
      exact returned

/-- Successful column and class requirements retain the literal returned physical state. -/
theorem requirements_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {edges : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : Physical Symbol Formula} {rows : List (List (Value Symbol Guard))}
    (actual : requirements p h edges constraints before = .done rows after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    requirements largerP largerH edges constraints before = .done rows after := by
  obtain ⟨rest, middle, first, returned⟩ := (bind_done_iff _ _ rows after).mp actual
  simp only [requirements, classes_done_stable first enoughP enoughH, Outcome.bind]
  exact returned

/-- Equality errors and missing fields cannot enter the successful tuple branch. -/
theorem tuple_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {edges : List (EdgeValue Symbol Guard)}
    {before after : Physical Symbol Formula} {row : Option (List (List (Value Symbol Guard)))}
    (actual : tuple p h edges before = .done row after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    tuple largerP largerH edges before = .done row after := by
  cases folded : (SourceCurrentConjunctionEquality.fold edges before.equality).1 with
  | error => simp only [tuple, folded] at actual; cases actual
  | ok value =>
      cases value with
      | none => simp only [tuple, folded] at actual; cases actual
      | some result =>
          cases constraints : SourceEqualityInheritedPayload.classes result.payload with
          | none => simpa only [tuple, folded, constraints] using actual
          | some constraints =>
              simp only [tuple, folded, constraints] at actual ⊢
              obtain ⟨rows, final, completed, returned⟩ := (bind_done_iff _ _ row after).mp actual
              simp only [requirements_done_stable completed enoughP enoughH, Outcome.bind]
              exact returned

/-- Ordered tuple filtering retains each successful row list and exact equality allocation state. -/
theorem tuples_done_stable [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {inputs : List (List (EdgeValue Symbol Guard))}
    {before after : Physical Symbol Formula} {rows : List (List (List (Value Symbol Guard)))}
    (actual : tuples p h inputs before = .done rows after) (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    tuples largerP largerH inputs before = .done rows after := by
  induction inputs generalizing before rows after with
  | nil => exact actual
  | cons edges inputs ih =>
      obtain ⟨row, middle, first, later⟩ := (bind_done_iff _ _ rows after).mp actual
      obtain ⟨rest, final, second, returned⟩ := (bind_done_iff _ _ rows after).mp later
      simp only [tuples, tuple_done_stable first enoughP enoughH, ih second, Outcome.bind]
      exact returned

/-- Larger bounds retain a successful conjunction's entire output and physical state. -/
theorem rows_done_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h largerP largerH : Nat} {nodes : List (Value Symbol Guard)}
    {before after : Physical Symbol Formula} {rows : List (List (List (Value Symbol Guard)))}
    (actual : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done rows after)
    (enoughP : p ≤ largerP) (enoughH : h ≤ largerH) :
    SourceCurrentConjunctionRowsWorker.rows largerP largerH nodes before = .done rows after := by
  obtain ⟨edges, middle, exposed, allocated⟩ := (bind_done_iff _ _ rows after).mp actual
  simp only [SourceCurrentConjunctionRowsWorker.rows, exposures_done_stable exposed enoughH, Outcome.bind]
  exact tuples_done_stable allocated enoughP enoughH

/-- Successful incomparable fuel choices identify the same row list, heap, and equality cache. -/
theorem rows_done_unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {p h otherP otherH : Nat} {nodes : List (Value Symbol Guard)} {before after later : Physical Symbol Formula}
    {first second : List (List (List (Value Symbol Guard)))}
    (one : SourceCurrentConjunctionRowsWorker.rows p h nodes before = .done first after)
    (two : SourceCurrentConjunctionRowsWorker.rows otherP otherH nodes before = .done second later) :
    first = second ∧ after = later := by
  have firstStable := rows_done_stable one (Nat.le_max_left p otherP) (Nat.le_max_left h otherH)
  have secondStable := rows_done_stable two (Nat.le_max_right p otherP) (Nat.le_max_right h otherH)
  exact Outcome.done.inj (firstStable.symm.trans secondStable)

end MicroCFTA.SourceCurrentConjunctionRowsWorkerStability
