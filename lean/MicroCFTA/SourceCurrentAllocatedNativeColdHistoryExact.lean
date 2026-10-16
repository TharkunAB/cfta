import MicroCFTA.SourceCurrentAllocatedNativeInputInventoryModels
import MicroCFTA.SourceCurrentAllocatedNativeWarmHistory

/-!
# Exact serial histories from empty native tables

The complete finite operand list derives one fixed input interpretation.
Empty native tables derive the initial contextual and scope invariants.
The serial checked walk supplies every later query's actual cache state.
Initial heap readiness and reached machine ranges remain explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeColdHistoryExact
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeRequestBounds (WordRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Query" => Value Symbol Guard × Value Symbol Guard
variable {width : Nat}

/-- The inventory retains both operands of every query, in source order. -/
def operands (pairs : List Query) : List (Value Symbol Guard) :=
  pairs.flatMap fun pair => [pair.1, pair.2]

/-- Listed original operands derive one model and actual complete serial execution. -/
theorem cold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (valid : Good (⟨initial width machine, operations⟩ : Checked width)) (semantic : SemanticReady machine.heap)
    (pairs : List Query) (originals : ∀ value ∈ operands pairs, Original value)
    (available : Values machine.heap (operands pairs)) (closed : ∀ value ∈ operands pairs, value.free = [])
    (ranges : WordRanges (.code (SourceCurrentAllocatedNativeWarmHistory.program pairs))
      (⟨initial width machine, operations⟩ : Checked width)) :
    let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput machine.heap valid.native.machine.1
      (SourceEqualityPCSGuard.holds formulas solver) (operands pairs) originals available closed
    ∃ fuel values after, SourceCurrentAllocatedNativeWarmHistory.Receipt machine.heap formulas solver inputs
      fuel pairs (⟨initial width machine, operations⟩ : Checked width) values after := by
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let inputs := SourceCurrentAllocatedNativeInputInventoryModels.finiteInput machine.heap valid.native.machine.1
    holds (operands pairs) originals available closed
  apply SourceCurrentAllocatedNativeWarmHistory.walk_complete machine.heap valid.native.machine.1 formulas solver inputs pairs
    ⟨initial width machine, operations⟩ valid
    (SourceCurrentAllocatedNativeContextCache.initial_contextual (view machine.heap holds)
      (finiteInputMeaning (view machine.heap holds) inputs) (finiteRankedInput (view machine.heap holds) inputs) holds width machine)
    (SourceCurrentAllocatedNativeScopeCache.initial_scoped width machine) semantic
    (SourceRecursiveIntersectionNative.idle_initial machine) (grows_refl _) (extends_refl _)
  · intro pair member
    have leftMember : pair.1 ∈ operands pairs := List.mem_flatMap.mpr ⟨pair, member, List.mem_cons_self⟩
    have rightMember : pair.2 ∈ operands pairs := List.mem_flatMap.mpr
      ⟨pair, member, List.mem_cons_of_mem _ List.mem_cons_self⟩
    exact ⟨originals pair.1 leftMember, originals pair.2 rightMember,
      available pair.1 leftMember, available pair.2 rightMember, closed pair.1 leftMember, closed pair.2 rightMember,
      SourceCurrentAllocatedNativeInputInventoryModels.root_valid machine.heap valid.native.machine.1 holds
        (operands pairs) originals available closed pair.1 leftMember,
      SourceCurrentAllocatedNativeInputInventoryModels.root_valid machine.heap valid.native.machine.1 holds
        (operands pairs) originals available closed pair.2 rightMember⟩
  · exact ranges

end MicroCFTA.SourceCurrentAllocatedNativeColdHistoryExact
