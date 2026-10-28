import MicroCFTA.SourcePruningEnumerationCheckedSyntaxOrigins
import MicroCFTA.SourcePruningEnumerationCheckedProjection
import MicroCFTA.SourceEqualityAnnotationConstruction

/-!
# Projection heaps from original checked source syntax

Each original edge passes its constructor check at its original child count.
The actual construction retains projectability in every physical edge record.
The closed producer retains its actual build and semantic annotation fields.
-/
namespace MicroCFTA.SourcePruningEnumerationProjectionHeap
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourcePruningEnumerationArityOrigins
open SourceEqualityAnnotationConstruction
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "projectable" =>
  (fun constraint : Constraint => SourcePruningEnumerationConstraint.project constraint ≠ none)
variable {Symbol : Type}

mutual
/-- Original constructor checks supply projectability for every source edge. -/
theorem source_allowed (expression : Syntax Symbol Constraint)
    (checked : SourceChecked expression) : Allowed projectable expression := by
  cases expression with
  | empty | var => trivial
  | node edges => exact source_edges_allowed edges checked
  | union members => exact source_many_allowed members checked
  | binder smart body => exact source_allowed body checked
termination_by sizeOf expression

/-- The ordered source children retain their original constructor checks. -/
theorem source_many_allowed (expressions : List (Syntax Symbol Constraint))
    (checked : SourceManyChecked expressions) : ManyAllowed projectable expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      exact ⟨source_allowed first checked.1, source_many_allowed rest checked.2⟩
termination_by sizeOf expressions

/-- Each literal source guard projects because its actual constructor test passed. -/
theorem source_edges_allowed (expressions : List (EdgeSyntax Symbol Constraint))
    (checked : SourceEdgesChecked expressions) : EdgesAllowed projectable expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          exact ⟨SourcePruningEnumerationCheckedProjection.accepted_projectable
              constraint children.length checked.1.2,
            source_many_allowed children checked.2.1,
            source_edges_allowed rest checked.2.2⟩
termination_by sizeOf expressions
end

/-- Actual source construction retains the original heap property at every outcome. -/
theorem build_projectable [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (checked : SourceChecked expression)
    (environment : List (Value Symbol Constraint)) (before : State Symbol Constraint)
    (heap : SourceEqualityAnnotationHeap.Heap projectable before) :
    SourceEqualityAnnotationHeap.Heap projectable
      (InternedFreshOrdinaryConstruction.build expression environment before).state :=
  SourceEqualityAnnotationConstruction.build projectable expression
    (source_allowed expression checked) environment before heap

/-- The actual closed build derives its whole heap property from original source checks. -/
theorem constructed_projectable [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (checked : SourceChecked expression)
    (value : Value Symbol Constraint) (after : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value after) :
    SourceEqualityAnnotationHeap.Heap projectable after := by
  simpa only [built, InternedNestedConstruction.Outcome.state] using
    build_projectable expression checked [] empty
      (SourceEqualityAnnotationHeap.empty_heap projectable)

/-- Closed construction supplies the full original annotation producer packet. -/
theorem closed_projectable [DecidableEq (EdgeKey Symbol Constraint)]
    (expression : Syntax Symbol Constraint) (checked : SourceChecked expression) :
    ∃ value heap,
      ∃ _done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
        SourceEqualityAnnotationHeap.Heap projectable heap ∧
          SourceEqualityAnnotationLanguage.Annotated projectable value :=
  SourceEqualityAnnotationConstruction.closed projectable expression
    (source_allowed expression checked)

end MicroCFTA.SourcePruningEnumerationProjectionHeap
