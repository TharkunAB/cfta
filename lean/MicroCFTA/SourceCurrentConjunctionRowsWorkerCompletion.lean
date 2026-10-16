import MicroCFTA.SourceCurrentConjunctionRowsWorker
import MicroCFTA.SourceEqualityProjectionWorkerComplete

/-!
# Stable bounds for current allocated conjunction rows

Each finite graph supplies projection and read bounds at its actual
intermediate heaps. Equality folds retain their exact returned caches.
The bounds do not add an arity check to the source worker.
-/
namespace MicroCFTA.SourceCurrentConjunctionRowsWorkerCompletion
open InternedConstructorTemplates SourceCurrentConjunctionRowsWorker
namespace Read
export SourceCurrentConjunctionCompletionReads (Exposures Projections)
end Read
namespace Req
export SourceCurrentConjunctionRequirements (ClassRequirements Requirements)
end Req
namespace Alloc
export SourceCurrentConjunctionRowsAllocation (Tuple Tuples Rows)
end Alloc
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- Every larger projection and read bound returns the same output and complete physical state. -/
def StableRun (evaluation : Nat → Nat → Outcome Symbol Formula Output) (output : Output)
    (after : Physical Symbol Formula) : Prop :=
  ∃ projection read, ∀ p h, projection ≤ p → read ≤ h → evaluation p h = .done output after

/-- One shared upper bound supplies both independently derived bounds. -/
theorem stable_uniform {evaluation : Nat → Nat → Outcome Symbol Formula Output} {output : Output}
    {after : Physical Symbol Formula} (actual : StableRun evaluation output after) :
    ∃ bound, ∀ fuel, bound ≤ fuel → evaluation fuel fuel = .done output after := by
  obtain ⟨p, h, done⟩ := actual
  exact ⟨max p h, fun fuel enough => done fuel fuel (by omega) (by omega)⟩

/-- Actual ordered exposure graphs retain the same equality cache at every sufficient read bound. -/
theorem exposures_complete [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : InternedConstructorTemplates.State Symbol Guard}
    {edges : List (List (EdgeValue Symbol Guard))} (actual : Read.Exposures nodes before edges after)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    StableRun (fun _ h => exposures h nodes ⟨before, operations⟩) edges ⟨after, operations⟩ := by
  induction actual with
  | nil => exact ⟨0, 0, by intros; rfl⟩
  | cons first rest ih =>
      obtain ⟨read, headDone⟩ := SourceEqualityProjectionWorkerComplete.read_stable first
      obtain ⟨projection, remainingRead, restDone⟩ := ih
      refine ⟨projection, max read remainingRead, ?_⟩
      intro p h enoughP enoughH
      simp only [exposures, headDone h (by omega), restDone p h enoughP (by omega), Outcome.bind]

/-- Actual projection jobs supply stable lower-worker bounds in literal job order. -/
theorem projections_complete [DecidableEq (EdgeKey Symbol Guard)]
    {jobs : List (SourceCurrentConjunctionCompletionReads.Job Symbol Guard)}
    {before after : InternedConstructorTemplates.State Symbol Guard} {values : List (Value Symbol Guard)}
    (actual : Read.Projections jobs before values after) (operations : SourceEqualityConstraintMemoAllocation.State) :
    StableRun (fun p h => projections p h jobs ⟨before, operations⟩) values ⟨after, operations⟩ := by
  induction actual with
  | nil => exact ⟨0, 0, by intros; rfl⟩
  | cons first rest ih =>
      obtain ⟨p, h, firstDone⟩ := SourceEqualityProjectionWorkerComplete.forest_stable first
      obtain ⟨restP, restH, restDone⟩ := ih
      refine ⟨max p restP, max h restH, ?_⟩
      intro a b enoughP enoughH
      simp only [projections, firstDone a b (by omega) (by omega), restDone a b (by omega) (by omega), Outcome.bind]

/-- Class requirements retain every original class occurrence and its canonical projected row. -/
theorem classes_complete [DecidableEq (EdgeKey Symbol Guard)]
    {forests : List (List (Value Symbol Guard))} {constraints : EqualityNormalize.Constraints}
    {before after : InternedConstructorTemplates.State Symbol Guard} {requirements : List (List (Value Symbol Guard))}
    (actual : Req.ClassRequirements forests constraints before requirements after)
    (operations : SourceEqualityConstraintMemoAllocation.State) :
    StableRun (fun p h => classes p h forests constraints ⟨before, operations⟩) requirements ⟨after, operations⟩ := by
  induction actual with
  | nil => exact ⟨0, 0, by intros; rfl⟩
  | cons first rest ih =>
      obtain ⟨p, h, firstDone⟩ := projections_complete first operations
      obtain ⟨restP, restH, restDone⟩ := ih
      refine ⟨max p restP, max h restH, ?_⟩
      intro a b enoughP enoughH
      simp only [classes, firstDone a b (by omega) (by omega), restDone a b (by omega) (by omega), Outcome.bind]

/-- The graph's same-arity evidence adds no branch to the literal requirements worker. -/
theorem requirements_complete [DecidableEq (EdgeKey Symbol Guard)]
    {edges : List (EdgeValue Symbol Guard)} {constraints : EqualityNormalize.Constraints}
    {before after : InternedConstructorTemplates.State Symbol Guard} {rows : List (List (Value Symbol Guard))}
    (actual : Req.Requirements edges constraints before rows after) (operations : SourceEqualityConstraintMemoAllocation.State) :
    StableRun (fun p h => requirements p h edges constraints ⟨before, operations⟩) rows ⟨after, operations⟩ := by
  cases actual with
  | run same body =>
      obtain ⟨p, h, done⟩ := classes_complete body operations
      exact ⟨p, h, by intro a b ep eh; simp only [requirements, done a b ep eh, Outcome.bind]⟩

/-- A tuple stops at its actual contradiction or runs its literal live requirements. -/
theorem tuple_complete [DecidableEq (EdgeKey Symbol Guard)]
    {edges : List (EdgeValue Symbol Guard)} {before after : Physical Symbol Formula}
    {row : Option (List (List (Value Symbol Guard)))} (actual : Alloc.Tuple edges before row after) :
    StableRun (fun p h => tuple p h edges before) row after := by
  cases actual with
  | contradiction folded empty => exact ⟨0, 0, by intros; simp only [tuple, folded, empty]⟩
  | live folded classes actual =>
      obtain ⟨p, h, done⟩ := requirements_complete actual (SourceCurrentConjunctionEquality.fold edges before.equality).2
      exact ⟨p, h, by intro a b ep eh; simp only [tuple, folded, classes, done a b ep eh, Outcome.bind]⟩

/-- Actual tuple filtering combines bounds without changing tuple order or equality effects. -/
theorem tuples_complete [DecidableEq (EdgeKey Symbol Guard)]
    {tuples : List (List (EdgeValue Symbol Guard))} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Alloc.Tuples tuples before rows after) :
    StableRun (fun p h => SourceCurrentConjunctionRowsWorker.tuples p h tuples before) rows after := by
  induction actual with
  | nil => exact ⟨0, 0, by intros; rfl⟩
  | skip first rest ih | keep first rest ih =>
      obtain ⟨p, h, firstDone⟩ := tuple_complete first
      obtain ⟨restP, restH, restDone⟩ := ih
      refine ⟨max p restP, max h restH, ?_⟩
      intro a b enoughP enoughH
      simp only [SourceCurrentConjunctionRowsWorker.tuples, firstDone a b (by omega) (by omega),
        restDone a b (by omega) (by omega), Outcome.bind]

/-- Every finite current row graph derives stable execution at the same full physical state. -/
theorem rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Alloc.Rows nodes before rows after) :
    StableRun (fun p h => SourceCurrentConjunctionRowsWorker.rows p h nodes before) rows after := by
  cases actual with
  | run exposed allocated =>
      obtain ⟨p, h, exposedDone⟩ := exposures_complete exposed before.equality
      obtain ⟨restP, restH, allocatedDone⟩ := tuples_complete allocated
      refine ⟨max p restP, max h restH, ?_⟩
      intro a b enoughP enoughH
      simp only [SourceCurrentConjunctionRowsWorker.rows, exposedDone a b (by omega) (by omega),
        allocatedDone a b (by omega) (by omega), Outcome.bind]

/-- The stable row endpoint also uses the conventional stable theorem name. -/
theorem rows_stable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {nodes : List (Value Symbol Guard)} {before after : Physical Symbol Formula}
    {rows : List (List (List (Value Symbol Guard)))} (actual : Alloc.Rows nodes before rows after) :
    StableRun (fun p h => SourceCurrentConjunctionRowsWorker.rows p h nodes before) rows after := rows_complete actual

end MicroCFTA.SourceCurrentConjunctionRowsWorkerCompletion
