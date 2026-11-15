import MicroCFTA.SourceEqualityNativeDemandBodyCode
import MicroCFTA.SourceEqualityNativeDemandPrefixSplit

/-!
# Preserve the actual compiled producer while removing an outer continuation

These lemmas invert a nonpure finish head and lift an actual producer prefix.
They do not infer a compiled producer from an arbitrary finish instruction.
The complete initial-query ancestry contract remains unproved.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A B : Type}

set_option autoImplicit false

/-- A nonpure appended finish head was already present in the inner control. -/
theorem finish_node_bind_inverse
    (control : Control A) (outside : A → Code Symbol Guard B)
    (handle : Nat) (value : Value Symbol Guard) (rest : Code Symbol Guard B)
    (nonpure : ∀ result, control ≠ .code (.pure result))
    (same : control.bind outside = .code (.finishNode handle value rest)) :
    ∃ (resume : Code Symbol Guard A),
      control = .code (.finishNode handle value resume) ∧ rest = resume.bind outside := by
  cases control with
  | edgeBody => cases same
  | code code =>
      cases code with
      | pure result => exact False.elim (nonpure result rfl)
      | finishNode original payload resume =>
          change (.code (.finishNode original payload (resume.bind outside)) : Control B) =
            .code (.finishNode handle value rest) at same
          obtain ⟨rfl, rfl, tail⟩ := Code.finishNode.inj (Control.code.inj same)
          exact ⟨resume, rfl, tail.symm⟩
      | fail | work | enter | read | optionalBinder | node | edge | finishEdge => cases same

/-- Lifting a real compiled prefix retains its handle, request, raw count, and full state. -/
theorem compiled_node_prefix_bind
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (used : Nat) (control : Control A) (before producer : Checked width)
    (handle : Nat) (request : NodeRequest Symbol Guard)
    (resume : Value Symbol Guard → Code Symbol Guard A)
    (outside : A → Code Symbol Guard B)
    (actual : Steps used control before
      (.code ((compileNode request).bind (fun value => .finishNode handle value (resume value)))) producer) :
    Steps used (control.bind outside) before
      (.code ((compileNode request).bind
        (fun value => .finishNode handle value ((resume value).bind outside)))) producer := by
  have lifted := actual.bind _ _ _ _ _ outside
  simpa only [Control.bind, Code.bind_assoc, Code.bind] using lifted

private theorem literal_node_query_clean (request : NodeRequest Symbol Guard) :
    SourceEqualityNativeDemandBodyCode.Clean (.code (.node request .pure)) := by
  intro value
  trivial

end MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
