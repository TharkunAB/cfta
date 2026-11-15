import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandTraceSplit
import MicroCFTA.SourceRecursiveIntersectionCompile

/-!
# Exact results for literal pure native bodies

A raw body trace retains the result selected by its original request.
A returned pure law supplies the exact selected warm cutoff law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- A literal pure compiler body fixes the complete returned value. -/
def PureResult [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∀ expected, compileNode request = .pure expected → value = expected

/-- An actual raw body return proves the pure clause without more observation fuel. -/
theorem raw_result
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before after : Checked width)
    (count : Nat) (value : Value Symbol Guard)
    (actual : Steps count (.code (compileNode request)) before (.code (.pure value)) after) :
    PureResult request value := by
  intro expected selected
  have terminal : Steps count (.code (.pure expected)) before (.code (.pure value)) after := by
    simpa only [selected] using actual
  exact (pure_trace count expected value before after terminal).2.1.symm

/-- The actual returned cell and selected pure equation supply the fixed-request law. -/
theorem returned_expected
    [DecidableEq Symbol]
    (request : NodeRequest Symbol Guard) (before : Checked width) (expected : Value Symbol Guard)
    (selected : compileNode request = .pure expected)
    (returned : Returned PureResult before.native.nodes) :
    Returned (fun old result => old = request → result = expected) before.native.nodes := by
  intro handle old result stored same
  subst old
  exact returned handle request result stored expected selected

end MicroCFTA.SourceCurrentAllocatedNativePureQueryLaw
