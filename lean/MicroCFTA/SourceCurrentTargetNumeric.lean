import MicroCFTA.SourceCurrentConstrainedCapTargetOperand
import MicroCFTA.SourceCurrentConstrainedCapTargetReceiptComposition
import MicroCFTA.SourceCurrentGeneratedQueryFrameResources

/-!
# Complete interleaved Targets from initial numeric reservations

Each head Operand precedes the recursive tail and its checked query.
Initial profiles determine every reached resource bound and worker fuel.
The same execution retains full Frames, inventories, physical Merge memos,
and equality-operation states. Selected closure applies to each operand
path. Unselected roots can stay open. No finite input cap is required.
-/
namespace MicroCFTA.SourceCurrentTargetNumeric
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
variable {bits : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial selected domains and numeric room construct the complete source-order Fold. -/
theorem fold_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (values : List (Value Symbol Guard))
    (seed : List Int) (paths : List (List Int)) (inventory : Inventory)
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : Forecast.Reserved bits values.length seed paths profile) :
    ∃ next result after saved final,
      ∃ actual : Fold values seed paths before memo result after saved,
        FoldReads formulas solver actual memos final ∧
        Receipt formulas solver next values (seed :: paths) before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.foldProfile values.length seed paths profile) after ∧
        Worker.fold (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          values seed paths before memo = .done result after saved := by
  induction paths generalizing inventory before memo profile memos with
  | nil =>
      obtain ⟨result, after, saved, final, actual, receipt, returned, finalFits, done⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory seed values before memo profile
          frame fits available (domains seed List.mem_cons_self) physicalStored covered memos valid
      exact ⟨inventory, result, after, saved, final, .nil actual, FoldReads.nil (operand := actual) receipt,
        SourceCurrentConstrainedCapTargetReceiptComposition.of_operand receipt, returned, finalFits,
        done⟩
  | cons path paths ih =>
      obtain ⟨head, middle, current, nextMemos, headActual, first, headFrame, headFits, headDone⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory path values before memo profile
          frame fits available (domains path (by simp)) physicalStored covered memos valid
      obtain ⟨tailInventory, tail, later, saved, final, tailActual, tailReads, rest, tailFrame, tailFits,
          tailDone⟩ :=
        ih inventory middle current (Forecast.operand path values.length profile)
          headFrame headFits first.originals (tail_all domains) first.stored first.covered nextMemos first.globals
          reserved.tail
      obtain ⟨next, fuel, result, after, query⟩ := SourceCurrentGeneratedQueryFrameResources.complete
        (Forecast.foldProfile values.length seed paths (Forecast.operand path values.length profile))
        formulas solver tailInventory later tailFrame tailFits reserved.query head tail
        (rest.effects.keeps.available head first.available) rest.available first.closed rest.closed
        final rest.globals.valid
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
        query.frame, query.fits, ?_⟩
      simp only [SourceCurrentAllocatedTargetWorker.fold, firstDone,
        SourceCurrentAllocatedTargetWorker.Outcome.bind, restDone, lastDone]

/-- Initial reservations construct the actual Target, full receipt, and exact common-fuel return. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (reserved : Forecast.TargetReserved bits values.length paths profile) :
    ∃ next result after saved final,
      ∃ actual : Target values paths before memo result after saved,
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values paths before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.targetProfile values.length paths profile) after ∧
        Worker.target (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          values paths before memo = .done result after saved := by
  cases paths with
  | nil =>
      exact ⟨inventory, .empty, before, memo, memos, .nil, .nil,
        SourceCurrentConstrainedCapTargetReceiptComposition.empty frame.ready frame.admitted available physicalStored covered valid,
        frame, fits, rfl⟩
  | cons seed paths =>
      obtain ⟨next, result, after, saved, final, actual, reads, receipt, returned, finalFits, done⟩ :=
        fold_complete formulas solver values seed paths inventory before memo profile
          frame fits available domains physicalStored covered memos valid reserved
      exact ⟨next, result, after, saved, final, .nonempty actual, .cons reads, receipt, returned, finalFits, done⟩

end MicroCFTA.SourceCurrentTargetNumeric
