import MicroCFTA.SourceEqualityNativeDemandTraceSplit

/-!
# Raw predicates through the actual source read

The source read retains the complete checked state.
Its child keeps the original parent continuation and raw count.
The completed child supplies its predicate at the same complete endpoint.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeRawReferencePredicateReplay
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- The actual source read transfers its smaller child predicate at the same full endpoint. -/
theorem reference_trace_predicate_of_actual_read
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request child : NodeRequest Symbol Guard) (original before after : Checked width)
    (parentFuel bodySteps : Nat) (result : Value Symbol Guard) (P : Value Symbol Guard → Prop)
    (finishNext : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
    (read : SourceEqualityNativeDemand.step (.code (compileNode request)) before =
      .yielded (.code (requestNode child.domain child.left child.right)) before)
    (entered : Steps 1 (.code (.node request .pure)) original
      (.code ((compileNode request).bind finishNext)) before)
    (smaller : bodySteps < parentFuel)
    (actual : Steps bodySteps (.code (compileNode request)) before (.code (.pure result)) after)
    (children : ∀ used count, 0 < used → used + count ≤ parentFuel → count < parentFuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard))
        (value : Value Symbol Guard) (last : Checked width),
      Steps used (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind next)) before →
      Steps count (.code (requestNode child.domain child.left child.right)) before (.code (.pure value)) last →
      P value) :
    P result ∧ ∃ childCount : Nat,
      bodySteps = 1 + childCount ∧ 2 + childCount ≤ parentFuel ∧ childCount < parentFuel ∧
      Steps 1 (.code (compileNode request)) before
        (.code (requestNode child.domain child.left child.right)) before ∧
      Steps 2 (.code (.node request .pure)) original
        (.code ((requestNode child.domain child.left child.right).bind finishNext)) before ∧
      Steps childCount (.code (requestNode child.domain child.left child.right)) before
        (.code (.pure result)) after := by
  have origin : Steps 1 (.code (compileNode request)) before
      (.code (requestNode child.domain child.left child.right)) before :=
    .cons _ _ _ _ _ _ _ read (.refl _ _)
  have appended := origin.bind _ _ _ _ _ finishNext
  have composed := entered.trans _ _ _ _ _ _ _ _ appended
  have outer : Steps 2 (.code (.node request .pure)) original
      (.code ((requestNode child.domain child.left child.right).bind finishNext)) before := by
    simpa only [Control.bind] using composed
  cases bodySteps with
  | zero =>
      have same := steps_zero _ _ _ _ actual
      rw [same.1] at read
      cases read
  | succ remaining =>
      obtain ⟨control, current, chosen, tail⟩ := steps_succ remaining _ _ _ _ actual
      obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj (chosen.symm.trans read)
      have property : P result := children 2 remaining (by omega) (by omega) (by omega)
        finishNext result after outer tail
      exact ⟨property, remaining, by omega, by omega, by omega, origin, outer, tail⟩

end MicroCFTA.SourceCurrentAllocatedNativeRawReferencePredicateReplay


#check @MicroCFTA.SourceCurrentAllocatedNativeRawReferencePredicateReplay.reference_trace_predicate_of_actual_read
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawReferencePredicateReplay.reference_trace_predicate_of_actual_read
#check @MicroCFTA.SourceCurrentAllocatedNativeRawReferenceReplay.reference_trace_result_of_actual_read
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawReferenceReplay.reference_trace_result_of_actual_read
