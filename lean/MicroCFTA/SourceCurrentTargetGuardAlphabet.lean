import MicroCFTA.SourceCurrentConstrainedCapTargetOperand
import MicroCFTA.SourceCurrentConstrainedCapTargetReceiptComposition
import MicroCFTA.SourceCurrentGeneratedQueryGuardResources
import MicroCFTA.SourceCurrentOpenProjectionFields
import MicroCFTA.SourceCurrentMemoMergeFieldHeap

/-!
# Initial finite guard alphabets for allocated Targets

Each Operand permits Top. The literal tail runs before its native query.
The original profile predicts each query instruction bound. The producer
constructs the same full Target return and its guard carrier together.
No future entry alphabet or completed callback is supplied.
-/
namespace MicroCFTA.SourceCurrentTargetGuardAlphabet
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedTargetGraph (Fold Target)
open SourceCurrentAllocatedTargetComplete (Receipt FoldReads TargetReads)
namespace Forecast
export SourceCurrentConstrainedCapTargetForecast
  (operand foldProfile targetProfile Reserved TargetReserved operandFuel queryFuel foldFuel targetFuel)
end Forecast
namespace Worker
export SourceCurrentAllocatedTargetWorker (Outcome operand leaf fold target)
end Worker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "advance" => SourceCurrentNativeGuardAlphabet.advance
local notation "instructionBound" => SourceCurrentAllocatedNativeComputedBudget.instructionBound

/-- Count Operand Top extensions and all predicted native instructions in source order. -/
def foldCount (count : Nat) (seed : List Int) : List (List Int) → Profile → Nat
  | [], _ => 1
  | path :: paths, profile =>
      let entry := Forecast.operand path count profile
      let query := Forecast.foldProfile count seed paths entry
      1 + foldCount count seed paths entry + instructionBound query.nodes query.edges query.mass

/-- An empty Target has no guard extension. A nonempty Target uses its literal fold. -/
def targetCount (count : Nat) : List (List Int) → Profile → Nat
  | [], _ => 0
  | seed :: paths, profile => foldCount count seed paths profile

variable {bits : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem operand_heap (alphabet : List Guard)
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked (bits+2)} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (actual : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final)
    (frame : Frame formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (stored : PhysicalStored before.native.machine.heap memo)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    Heap (fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.step alphabet) after.native.machine.heap := by
  let annotation := fun guard => guard ∈ SourceCurrentNativeGuardAlphabet.step alphabet
  have fields : Heap annotation before.native.machine.heap := fun key edge found =>
    SourceCurrentNativeGuardAlphabet.mem_step_of_mem (known key edge found)
  obtain ⟨projected,middle,current,projection,merged⟩ := actual.actual
  have projectedFields := SourceCurrentOpenProjectionFields.forest annotation projection.graph
    frame.ready.semantic frame.ready.costs available fields
  cases merged.actual with
  | done call =>
    exact SourceCurrentMemoMergeFieldHeap.call_heap annotation
      (SourceCurrentNativeGuardAlphabet.top_mem_step alphabet) call.graph projection.ready.semantic
      projection.ready.costs (stored.grows projection.effects.keeps) projection.available projectedFields

/-- Initial selected domains and numeric room construct the complete source-order Fold. -/
theorem fold_complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (values : List (Value Symbol Guard))
    (seed : List Int) (paths : List (List Int)) (inventory : Inventory)
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : Forecast.Reserved bits values.length seed paths profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    ∃ next result after saved final,
      ∃ actual : Fold values seed paths before memo result after saved,
        FoldReads formulas solver actual memos final ∧
        Receipt formulas solver next values (seed :: paths) before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.foldProfile values.length seed paths profile) after ∧
        Heap (fun guard => guard ∈ advance alphabet (foldCount values.length seed paths profile)) after.native.machine.heap ∧
        Worker.fold (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          values seed paths before memo = .done result after saved := by
  induction paths generalizing alphabet inventory before memo profile memos with
  | nil =>
      obtain ⟨result, after, saved, final, actual, receipt, returned, finalFits, done⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory seed values before memo profile
          frame fits available (domains seed List.mem_cons_self) physicalStored covered memos valid
      exact ⟨inventory, result, after, saved, final, .nil actual, FoldReads.nil (operand := actual) receipt,
        SourceCurrentConstrainedCapTargetReceiptComposition.of_operand receipt, returned, finalFits,
        by simpa only [foldCount,SourceCurrentNativeGuardAlphabet.advance_succ,
          SourceCurrentNativeGuardAlphabet.advance_zero] using operand_heap alphabet receipt frame available physicalStored known, done⟩
  | cons path paths ih =>
      obtain ⟨head, middle, current, nextMemos, headActual, first, headFrame, headFits, headDone⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory path values before memo profile
          frame fits available (domains path (by simp)) physicalStored covered memos valid
      obtain ⟨tailInventory, tail, later, saved, final, tailActual, tailReads, rest, tailFrame, tailFits,
          tailKnown,tailDone⟩ :=
        ih (SourceCurrentNativeGuardAlphabet.step alphabet) inventory middle current (Forecast.operand path values.length profile)
          headFrame headFits first.originals (tail_all domains) first.stored first.covered nextMemos first.globals
          reserved.tail (operand_heap alphabet first frame available physicalStored known)
      obtain ⟨next, fuel, result, after, query,queryKnown⟩ := SourceCurrentGeneratedQueryGuardResources.complete
        (advance (SourceCurrentNativeGuardAlphabet.step alphabet)
          (foldCount values.length seed paths (Forecast.operand path values.length profile)))
        (Forecast.foldProfile values.length seed paths (Forecast.operand path values.length profile))
        formulas solver tailInventory later tailFrame tailFits reserved.query head tail
        (rest.effects.keeps.available head first.available) rest.available first.closed rest.closed
        tailKnown final rest.globals.valid
      have headEnough := SourceCurrentConstrainedCapTargetForecast.foldFuel_head values.length seed path paths profile
      have tailEnough := SourceCurrentConstrainedCapTargetForecast.foldFuel_tail values.length seed path paths profile
      have queryEnough := SourceCurrentConstrainedCapTargetForecast.foldFuel_query values.length seed path paths profile
      have firstDone := SourceCurrentAllocatedTargetWorkerCompletion.operand_done_stable headDone
        headEnough headEnough headEnough headEnough
      have restDone := SourceCurrentAllocatedTargetWorkerCompletion.fold_done_stable tailDone
        tailEnough tailEnough tailEnough tailEnough tailEnough
      have leafDone : Worker.leaf
          (Forecast.queryFuel (Forecast.foldProfile values.length seed paths (Forecast.operand path values.length profile)))
          head tail later saved = .done result after saved := by
        simp only [SourceCurrentAllocatedTargetWorker.leaf, Forecast.queryFuel, query.done]
      have lastDone := SourceCurrentAllocatedTargetWorkerCompletion.leaf_done_stable leafDone queryEnough
      refine ⟨next, result, after, saved, final, .cons headActual tailActual query.query.actual,
        FoldReads.cons (operand := headActual) (rest := tailActual) (step := query.query.actual) first tailReads query.query,
        SourceCurrentConstrainedCapTargetReceiptComposition.cons first rest query.query,
        query.frame, query.fits, ?_, ?_⟩
      · simpa only [foldCount,SourceCurrentNativeGuardAlphabet.advance_add,
          SourceCurrentNativeGuardAlphabet.advance_succ,SourceCurrentNativeGuardAlphabet.advance_zero,
          SourceCurrentGeneratedQueryGuardResources.forecast] using queryKnown
      · simp only [SourceCurrentAllocatedTargetWorker.fold, firstDone,
          SourceCurrentAllocatedTargetWorker.Outcome.bind, restDone, lastDone]

/-- Initial reservations construct the actual Target, full receipt, and exact common-fuel return. -/
theorem complete (alphabet : List Guard) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : Forecast.TargetReserved bits values.length paths profile)
    (known : Heap (fun guard => guard ∈ alphabet) before.native.machine.heap) :
    ∃ next result after saved final,
      ∃ actual : Target values paths before memo result after saved,
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values paths before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.targetProfile values.length paths profile) after ∧
        Heap (fun guard => guard ∈ advance alphabet (targetCount values.length paths profile)) after.native.machine.heap ∧
        Worker.target (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          values paths before memo = .done result after saved := by
  cases paths with
  | nil =>
      exact ⟨inventory, .empty, before, memo, memos, .nil, .nil,
        SourceCurrentConstrainedCapTargetReceiptComposition.empty frame.ready frame.admitted available physicalStored covered valid,
        frame, fits, known, rfl⟩
  | cons seed paths =>
      obtain ⟨next, result, after, saved, final, actual, reads, receipt, returned, finalFits, finalKnown,done⟩ :=
        fold_complete alphabet formulas solver values seed paths inventory before memo profile
          frame fits available domains physicalStored covered memos valid reserved known
      exact ⟨next, result, after, saved, final, .nonempty actual, .cons reads, receipt, returned, finalFits, finalKnown,done⟩

end MicroCFTA.SourceCurrentTargetGuardAlphabet
