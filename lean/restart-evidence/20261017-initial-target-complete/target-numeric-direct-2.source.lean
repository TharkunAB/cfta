import MicroCFTA.SourceCurrentConstrainedCapTargetOperand
import MicroCFTA.SourceCurrentConstrainedCapTargetReceiptComposition

/-!
# Complete interleaved Targets from initial numeric reservations

Each head Operand precedes the recursive tail and its checked query.
Initial profiles determine every reached resource bound and worker fuel.
The same execution retains full Frames, inventories, memos, and cap laws.
Selected closure and the separate original-root cap assumptions stay explicit.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapTargetNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedTargetGraph (Fold Target)
open SourceCurrentAllocatedTargetComplete (Receipt FoldReads TargetReads)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
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
local notation "MergeStored" => SourceCurrentConstrainedCapMemoMerge.Stored Plain
local notation "foldDepth" => SourceCurrentConstrainedCapMixedTarget.foldDepth
local notation "targetDepth" => SourceCurrentConstrainedCapMixedTarget.targetDepth
variable {bits : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial selected domains, caps, and numeric room construct the complete source-order Fold. -/
theorem fold_complete (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (values : List (Value Symbol Guard))
    (seed : List Int) (paths : List (List Int)) (inventory : Inventory)
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (merged : MergeStored memo) (bounded : ∀ value ∈ values, Cap Plain depth value)
    (reserved : Forecast.Reserved bits values.length seed paths profile) :
    ∃ next result after saved final,
      ∃ actual : Fold values seed paths before memo result after saved,
        FoldReads formulas solver actual memos final ∧
        Receipt formulas solver next values (seed :: paths) before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.foldProfile values.length seed paths profile) after ∧
        MergeStored saved ∧ Cap Plain (foldDepth depth seed paths) result ∧
        Worker.fold (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          (Forecast.foldFuel values.length seed paths profile) (Forecast.foldFuel values.length seed paths profile)
          values seed paths before memo = .done result after saved := by
  induction paths generalizing inventory before memo profile memos with
  | nil =>
      obtain ⟨result, after, saved, final, actual, receipt, returned, finalFits, done⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory seed values before memo profile
          frame fits available (domains seed List.mem_cons_self) physicalStored covered memos valid
      have caps := SourceCurrentConstrainedCapMixedTarget.operand_receipt depth receipt frame.ready available
        (domains seed List.mem_cons_self) physicalStored merged (SourceCurrentConstrainedCapOperandFrame.current frame) bounded
      exact ⟨inventory, result, after, saved, final, .nil actual, FoldReads.nil (operand := actual) receipt,
        SourceCurrentConstrainedCapTargetReceiptComposition.of_operand receipt, returned, finalFits,
        caps.1, caps.2.2, done⟩
  | cons path paths ih =>
      obtain ⟨head, middle, current, nextMemos, headActual, first, headFrame, headFits, headDone⟩ :=
        SourceCurrentConstrainedCapTargetOperand.complete formulas solver inventory path values before memo profile
          frame fits available (domains path (by simp)) physicalStored covered memos valid
      have headCaps := SourceCurrentConstrainedCapMixedTarget.operand_receipt depth first frame.ready available
        (domains path (by simp)) physicalStored merged (SourceCurrentConstrainedCapOperandFrame.current frame) bounded
      obtain ⟨tailInventory, tail, later, saved, final, tailActual, tailReads, rest, tailFrame, tailFits,
          tailMerged, tailCap, tailDone⟩ :=
        ih inventory middle current (Forecast.operand path values.length profile)
          headFrame headFits first.originals (tail_all domains) first.stored first.covered nextMemos first.globals
          headCaps.1 reserved.tail
      obtain ⟨next, fuel, result, after, query⟩ := SourceCurrentConstrainedCapGeneratedQueryResources.complete
        (Forecast.foldProfile values.length seed paths (Forecast.operand path values.length profile))
        (max (SourceCurrentConstrainedCapMixedTarget.operandDepth depth path) (foldDepth depth seed paths))
        formulas solver tailInventory later tailFrame tailFits reserved.query head tail
        (rest.effects.keeps.available head first.available) rest.available first.closed rest.closed
        (headCaps.2.2.mono (Nat.le_max_left _ _)) (tailCap.mono (Nat.le_max_right _ _)) final rest.globals.valid
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
        query.frame, query.fits, tailMerged, query.joint.cap, ?_⟩
      simp only [SourceCurrentAllocatedTargetWorker.fold, firstDone,
        SourceCurrentAllocatedTargetWorker.Outcome.bind, restDone, lastDone]

/-- Initial reservations construct the actual Target, full receipt, and exact common-fuel return. -/
theorem complete (depth : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked (bits + 2)) (memo : Memo) (profile : Profile)
    (frame : Frame formulas solver inventory before) (fits : Fits profile before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ paths, Domain path values)
    (physicalStored : PhysicalStored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (merged : MergeStored memo) (bounded : ∀ value ∈ values, Cap Plain depth value)
    (reserved : Forecast.TargetReserved bits values.length paths profile) :
    ∃ next result after saved final,
      ∃ actual : Target values paths before memo result after saved,
        TargetReads formulas solver actual memos final ∧
        Receipt formulas solver next values paths before memo result after saved memos final ∧
        Frame formulas solver next after ∧ Fits (Forecast.targetProfile values.length paths profile) after ∧
        MergeStored saved ∧ Cap Plain (targetDepth depth paths) result ∧
        Worker.target (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          (Forecast.targetFuel values.length paths profile) (Forecast.targetFuel values.length paths profile)
          values paths before memo = .done result after saved := by
  cases paths with
  | nil =>
      exact ⟨inventory, .empty, before, memo, memos, .nil, .nil,
        SourceCurrentConstrainedCapTargetReceiptComposition.empty frame.ready frame.admitted available physicalStored covered valid,
        frame, fits, merged, .plain 0 .empty, rfl⟩
  | cons seed paths =>
      obtain ⟨next, result, after, saved, final, actual, reads, receipt, returned, finalFits, savedMerged, cap, done⟩ :=
        fold_complete depth formulas solver values seed paths inventory before memo profile
          frame fits available domains physicalStored covered memos valid merged bounded reserved
      exact ⟨next, result, after, saved, final, .nonempty actual, .cons reads, receipt, returned, finalFits, savedMerged, cap, done⟩

end MicroCFTA.SourceCurrentConstrainedCapTargetNumeric
