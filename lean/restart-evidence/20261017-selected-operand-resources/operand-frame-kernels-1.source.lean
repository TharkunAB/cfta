import MicroCFTA.SourceCurrentConstrainedCapOperandFrame
import MicroCFTA.EndpointMemoGateSource

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.OperandFrameKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame)
open SourceCurrentAllocatedTargetGraph (Operand)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Three selected Operands construct all intermediate frames and retain every initially populated native cell. -/
theorem three_operands (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (first second third : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (frame : Frame formulas solver inventory before) (available : Values before.native.machine.heap values)
    (firstDomain : Domain first values) (secondDomain : Domain second values) (thirdDomain : Domain third values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ firstValue middle firstMemo firstGlobals secondValue later secondMemo secondGlobals result after saved final,
      Operand first values before memo firstValue middle firstMemo ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory first values
        before memo firstValue middle firstMemo memos firstGlobals ∧ Frame formulas solver inventory middle ∧
      Operand second values middle firstMemo secondValue later secondMemo ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory second values
        middle firstMemo secondValue later secondMemo firstGlobals secondGlobals ∧ Frame formulas solver inventory later ∧
      Operand third values later secondMemo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory third values
        later secondMemo result after saved secondGlobals final ∧ Frame formulas solver inventory after ∧
      after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final := by
  obtain ⟨firstValue, middle, firstMemo, firstGlobals, firstRun, firstReceipt, firstFrame⟩ :=
    SourceCurrentConstrainedCapOperandFrame.complete formulas solver inventory first values before memo
      frame available firstDomain stored covered memos valid
  obtain ⟨secondValue, later, secondMemo, secondGlobals, secondRun, secondReceipt, secondFrame⟩ :=
    SourceCurrentConstrainedCapOperandFrame.complete formulas solver inventory second values middle firstMemo
      firstFrame firstReceipt.originals secondDomain firstReceipt.stored firstReceipt.covered firstGlobals firstReceipt.globals
  obtain ⟨result, after, saved, final, thirdRun, thirdReceipt, thirdFrame⟩ :=
    SourceCurrentConstrainedCapOperandFrame.complete formulas solver inventory third values later secondMemo
      secondFrame secondReceipt.originals thirdDomain secondReceipt.stored secondReceipt.covered secondGlobals secondReceipt.globals
  exact ⟨firstValue, middle, firstMemo, firstGlobals, secondValue, later, secondMemo, secondGlobals, result, after, saved, final,
    firstRun, firstReceipt, firstFrame, secondRun, secondReceipt, secondFrame, thirdRun, thirdReceipt, thirdFrame,
    thirdReceipt.nodes.trans (secondReceipt.nodes.trans firstReceipt.nodes),
    thirdReceipt.edges.trans (secondReceipt.edges.trans firstReceipt.edges),
    thirdReceipt.domains.trans (secondReceipt.domains.trans firstReceipt.domains), thirdReceipt.globals⟩

/-- A selected empty value permits arbitrary longer paths while an unrelated reference stays open. -/
theorem selected_open_sibling (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (before : Checked width) (frame : Frame formulas solver inventory before) :
    let values : List (Value Symbol Guard) := [.empty, .reference .depth]
    ¬MergedColdReaderClosedInputs.ClosedValues values ∧
      ∃ firstValue middle firstMemo firstGlobals secondValue later secondMemo secondGlobals result after saved final,
        Operand [0] values before SourceCurrentMemoMergeGraph.empty firstValue middle firstMemo ∧
        SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0] values
          before SourceCurrentMemoMergeGraph.empty firstValue middle firstMemo EndpointMemoGateSource.empty firstGlobals ∧
        Frame formulas solver inventory middle ∧
        Operand [0, 0] values middle firstMemo secondValue later secondMemo ∧
        SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0, 0] values
          middle firstMemo secondValue later secondMemo firstGlobals secondGlobals ∧ Frame formulas solver inventory later ∧
        Operand [0, 0, 0] values later secondMemo result after saved ∧
        SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory [0, 0, 0] values
          later secondMemo result after saved secondGlobals final ∧ Frame formulas solver inventory after ∧
        after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
        after.native.machine.domains = before.native.machine.domains ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final := by
  dsimp only
  have available : Values before.native.machine.heap [.empty, .reference .depth] := by
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact empty_available _
    · exact InternedNestedProvenance.depth_available _
  have selected (path : List Int) : Domain (0 :: path) ([.empty, .reference .depth] : List (Value Symbol Guard)) := by
    cases path <;> simp [SourceEqualityProjectionPathDomain.ForestClosed, SourceEqualityProjectionPathDomain.NodeClosed,
      SourceEqualityProjectionGraph.select, Value.free]
  have covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers
      (SourceEqualityPCSGuard.holds formulas solver) ambient (SourceCurrentMemoMergeGraph.empty : Memo) := by
    intro ambient key entry absent
    cases absent
  refine ⟨?_, three_operands formulas solver inventory [0] [0, 0] [0, 0, 0]
    [.empty, .reference .depth] before SourceCurrentMemoMergeGraph.empty frame available
    (selected []) (selected [0]) (selected [0, 0]) (SourceCurrentMemoMergeEffects.stored_empty _) covered
    EndpointMemoGateSource.empty (EndpointMemoGateSource.empty_valid _)⟩
  intro closed
  have impossible := closed (.reference .depth) (by simp)
  cases impossible

end MicroCFTA.OperandFrameKernels

#check @MicroCFTA.OperandFrameKernels.three_operands
#print axioms MicroCFTA.OperandFrameKernels.three_operands
#check @MicroCFTA.OperandFrameKernels.selected_open_sibling
#print axioms MicroCFTA.OperandFrameKernels.selected_open_sibling
