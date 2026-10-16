import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentProfiles

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option format.width 200

namespace MicroCFTA.ParentProfilesIndependent
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Raw rejection constructs its own strict reads without any child load or availability input. -/
theorem rejected_constructs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (original : EdgeValue Symbol Guard)
    (loaded : Allocated) (inherited : EqValue) (before : Checked width)
    (fourth : Fourth) (memo : Memo) (memos : Memos)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original.entry.key.constraint = true) (domain : DEdge original)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next, ∃ actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
        loaded inherited original.children before fourth memo (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
        (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2 fourth memo,
      SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos memos ∧
      SourceCurrentAllocatedParentEdge.Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint
        loaded inherited original.children before (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
        (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2 fourth fourth memo memo memos ∧
      NativeStored (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2.native ∧
      OutputStored (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2.native ∧
      Profiles memo ∧ SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow original
        (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1 := by
  let actual : SourceCurrentAllocatedParentEdge.Edge budget original.entry.key.symbol original.entry.key.constraint
      loaded inherited original.children before fourth memo (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
      (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2 fourth memo := .rejected test
  have reads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver actual memos memos := .rejected (test := test)
  have dead : contradictory original.entry.key.constraint = false → False := by
    intro other
    simp only [test, Bool.true_eq_false] at other
  have strong := SourceCurrentAllocatedFiniteOrdinaryParentProfiles.structure_from_reads formulas solver inventory original
    reads ready admitted (fun other => False.elim (dead other)) domain correct physical covered native profiles output valid
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory reads ready admitted
    (fun other => False.elim (dead other)) correct physical covered valid
  exact ⟨next, actual, reads, receipt, strong⟩

/-- The first actual return supplies the second parent's physical and strong cache invariants. -/
theorem serial_same_return
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (firstOriginal secondOriginal : EdgeValue Symbol Guard)
    {budget : Nat} {firstLoaded secondLoaded : Allocated} {firstInherited secondInherited : EqValue}
    {before middle after : Checked width} {firstResult secondResult : EdgeValue Symbol Guard}
    {fourth middleFourth savedFourth : Fourth} {memo middleMemo saved : Memo} {memos middleMemos final : Memos}
    {first : SourceCurrentAllocatedParentEdge.Edge budget firstOriginal.entry.key.symbol firstOriginal.entry.key.constraint
      firstLoaded firstInherited firstOriginal.children before fourth memo firstResult middle middleFourth middleMemo}
    {second : SourceCurrentAllocatedParentEdge.Edge budget secondOriginal.entry.key.symbol secondOriginal.entry.key.constraint
      secondLoaded secondInherited secondOriginal.children middle middleFourth middleMemo secondResult after savedFourth saved}
    (firstReads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver first memos middleMemos)
    (secondReads : SourceCurrentAllocatedParentEdgeActual.Reads formulas solver second middleMemos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (firstLive : contradictory firstOriginal.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached firstOriginal.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load firstOriginal.entry.key.constraint before.operations.constraints = .ok (some firstLoaded) ∧
      SourceEqualityConstraintAllocation.Ready before.operations.constraints firstInherited ∧
      Values before.native.machine.heap firstOriginal.children)
    (secondLive : contradictory secondOriginal.entry.key.constraint = false →
      SourceEqualityGuardReadback.Cached secondOriginal.entry.key.constraint.equalities ∧
      SourceEqualityConstraintFieldLookup.load secondOriginal.entry.key.constraint middle.operations.constraints = .ok (some secondLoaded) ∧
      SourceEqualityConstraintAllocation.Ready middle.operations.constraints secondInherited ∧
      Values middle.native.machine.heap secondOriginal.children)
    (firstDomain : DEdge firstOriginal) (secondDomain : DEdge secondOriginal)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (native : NativeStored before.native) (profiles : Profiles memo) (output : OutputStored before.native)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ next, SourceCurrentAllocatedParentEdge.Receipt formulas solver next firstOriginal.entry.key.symbol
        firstOriginal.entry.key.constraint firstLoaded firstInherited firstOriginal.children before firstResult middle
        fourth middleFourth memo middleMemo middleMemos ∧
      (NativeStored middle.native ∧ OutputStored middle.native ∧ Profiles middleMemo ∧
        SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow firstOriginal firstResult) ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
        SourceCurrentAllocatedFiniteOrdinaryRequired.EdgeNarrow secondOriginal secondResult := by
  have firstStrong := SourceCurrentAllocatedFiniteOrdinaryParentProfiles.structure_from_reads formulas solver inventory firstOriginal
    firstReads ready admitted firstLive firstDomain correct physical covered native profiles output valid
  have ranges : ∀ test : contradictory firstOriginal.entry.key.constraint = false,
      SourceCurrentAllocatedLocalReductionActual.Ranges budget firstLoaded firstInherited firstOriginal.children before fourth := by
    intro test records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) firstOriginal.children
      (records.map SourceEqualityClassOrder.Record.paths) (SourceCurrentAllocatedPrecheck.state before firstLoaded firstInherited)
      fourth ready.good.native.machine.1.coherent (firstLive test).2.2.2 firstDomain
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedParentEdgeActual.verified formulas solver inventory firstReads ready admitted
    (fun test => ⟨(firstLive test).1, (firstLive test).2.1, (firstLive test).2.2.1, (firstLive test).2.2.2, ranges test⟩)
    correct physical covered valid
  have secondStrong := SourceCurrentAllocatedFiniteOrdinaryParentProfiles.structure_from_reads formulas solver next secondOriginal
    secondReads receipt.ready receipt.admitted secondLive secondDomain receipt.correct receipt.stored receipt.covered
    firstStrong.1 firstStrong.2.2.1 firstStrong.2.1 receipt.globals
  exact ⟨next, receipt, firstStrong, secondStrong⟩

#print axioms rejected_constructs
#check @rejected_constructs
#print axioms serial_same_return
#check @serial_same_return
end MicroCFTA.ParentProfilesIndependent
