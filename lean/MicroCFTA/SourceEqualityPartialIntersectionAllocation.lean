import MicroCFTA.SourceEqualityIntersectionEdgeAllocation
import MicroCFTA.SourceEqualityPartialMkEdgeAllocation

/-!
# Intersection constructor prefixes in recursive memo state

The source-selected operand order fixes raw conjunction. Arity mismatch
skips both conjunction and accessor demand. Rejection retains reached
allocations. The separate empty-edge receipt demands noConstraint and
interns the sentinel without a child callback. Both operations preserve
current recursive result cells. Complete native recursion remains separate.
-/
namespace MicroCFTA.SourceEqualityPartialIntersectionAllocation
open SourceEqualityConstraintAllocation
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Constraint" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Worker" => SourceEqualityPartialMemoWorker.State
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Use the actual source guard order at the already selected edge operands. -/
noncomputable def prepare (first second : Constraint) (firstArity secondArity : Nat) (before : OpState) :=
  SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second firstArity secondArity before

/-- Every completed source prefix preserves current request and result proofs before any child callback. -/
theorem prefix_sound (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (first second : Constraint) (firstArity secondArity : Nat) (before : OpState)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : Ready before.constraints first.stored) (secondReady : Ready before.constraints second.stored)
    (worker : Worker width) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker) :
    SourceEqualityPartialMemoSound.Sound holds ambient
      {worker with constraints := (prepare first second firstArity secondArity before).2.constraints} ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables
          {worker with constraints := (prepare first second firstArity secondArity before).2.constraints}) := by
  obtain ⟨_, _, _, _, growth, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
    GuardStructuralOrder.le first second firstArity secondArity before valid firstReady secondReady
  have steps : Cache.Steps worker.constraints (prepare first second firstArity secondArity before).2.constraints := by
    simpa only [prepare, same] using growth.constraints
  exact ⟨SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps⟩

/-- The stopping continuation demands only the empty field and the direct empty-edge constructor. -/
def emptyEdge [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (symbol : Symbol) (before : OpState) (worker : Worker width) :
    InternedConstructorTemplates.EdgeValue Symbol Guard × OpState × Worker width :=
  let after := SourceEqualityMkEdgeAllocation.emptyField before
  let built := InternedConstructorTemplates.run
    (InternedConstructorTemplates.makeEdge symbol SourceEqualityConstraintConstructors.top [.empty]) worker.native.machine.heap
  (built.1, after, {worker with constraints := after.constraints, native := SourceEqualityNativeScoped.advanceHeap worker.native built.2})

/-- Actual sentinel construction preserves all recursive cells and their meaning without child-demand premises. -/
theorem emptyEdge_sound [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (symbol : Symbol) (before : OpState) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before) (same : worker.constraints = before.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (heapReady : SourceEqualityRequiredCache.Ready worker.native.machine.heap) :
    SourceEqualityPartialMemoSound.Sound holds ambient (emptyEdge symbol before worker).2.2 ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (emptyEdge symbol before worker).2.2) ∧
      SourceEqualityConstraintMemoAllocation.Valid (emptyEdge symbol before worker).2.1 ∧
      SourceEqualityConstraintMemoAllocation.Grows before (emptyEdge symbol before worker).2.1 := by
  obtain ⟨afterValid, growth, _⟩ := SourceEqualityMkEdgeAllocation.emptyField_correct before valid
  have keeps := SourceEqualityMkEdgeAllocation.work_keeps symbol
    (SourceEqualityConstraintConstructors.top : Guard) [] false worker.native.machine.heap heapReady
    (by intro child impossible; cases impossible)
  have steps : Cache.Steps worker.constraints (SourceEqualityMkEdgeAllocation.emptyField before).constraints := by
    simpa only [same] using growth.constraints
  have allocated := SourceEqualityPartialAllocationFrame.steps_sound holds ambient worker _ sound steps
  exact ⟨SourceEqualityPartialMemoSound.Sound.keeps holds ambient allocated rfl keeps,
    SourceEqualityPartialAllocationFrame.steps_frame worker _ sound.valid steps, afterValid, growth⟩

end MicroCFTA.SourceEqualityPartialIntersectionAllocation
