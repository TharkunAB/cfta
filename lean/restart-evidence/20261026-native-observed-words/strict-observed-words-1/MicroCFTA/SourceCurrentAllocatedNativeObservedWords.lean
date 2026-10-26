import MicroCFTA.SourceCurrentAllocatedNativePhysicalTraceCompletion

namespace MicroCFTA.SourceCurrentAllocatedNativeObservedWords
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalExecution (Inputs)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeRequestBounds (Words WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {A : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A recorded physical instruction check includes its current numeric key bounds. -/
theorem inputs_words (control : Control A) (state : Checked width) (inputs : Inputs control state) :
    Words width control := by
  cases control with
  | edgeBody _ _ => trivial
  | code code =>
      cases code with
      | node _ _ | edge _ _ => exact inputs.2
      | pure | fail | work | enter | read | optionalBinder | finishNode | finishEdge => trivial

/-- A completed checked trace contains the numeric checks of every possible actual prefix. -/
theorem trace_wordRanges {fuel : Nat} {control : Control A} {before after : Checked width} {value : A}
    (trace : Trace fuel control before (.code (.pure value)) after) : WordRanges control before := by
  intro count next reached observed
  induction fuel generalizing control before count next reached with
  | zero =>
      cases trace
      cases observed with
      | refl => trivial
      | cons _ _ _ _ _ _ _ one _ =>
          simp only [step, SourceRecursiveIntersectionNative.step, lift] at one
          cases one
  | succ fuel ih =>
      cases trace with
      | cons start initial middle current final result size inputs one rest =>
          cases observed with
          | refl => exact inputs_words start initial inputs
          | cons _ _ other after _ _ _ actual tail =>
              obtain ⟨sameControl, sameState⟩ := Outcome.yielded.inj (one.symm.trans actual)
              subst other
              subst after
              exact ih rest tail

end MicroCFTA.SourceCurrentAllocatedNativeObservedWords
