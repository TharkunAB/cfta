import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryShared
namespace FiniteOrdinarySharedKernels
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State)
open SourceCurrentAllocatedFiniteOrdinaryShared (Stored force force_finite leaf_finite)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Domain" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "Domains" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "ForceRanges" => SourceCurrentAllocatedSharedTargetForce.ForceRanges
local notation "ForceReceipt" => SourceCurrentAllocatedSharedTargetForce.Receipt
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "LeafRanges" => SourceCurrentAllocatedSharedTargetLeaf.Ranges
local notation "LeafReceipt" => SourceCurrentAllocatedSharedTargetLeaf.Receipt
local notation "Narrow" => SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
variable {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before : State width} {input : Value Symbol Guard}

/-- First forcing derives a stored domain; its next literal hit needs no target range checks. -/
theorem force_then_hit (ready : Ready formulas solver inventory record values base before)
    (known : Values base values) (domains : Domains values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (ranges : ForceRanges record values path before)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ value after next final,
      ForceReceipt formulas solver next record values base path before value after memos final ∧
      Force record values path after value after ∧
      ForceReceipt formulas solver next record values base path after value after final final ∧
      Stored after ∧ Domain value := by
  obtain ⟨value, after, next, final, first, structural, domain⟩ :=
    force_finite formulas solver inventory ready known domains stored coherent active member ranges memos valid
  have actual : Force record values path after value after := .hit first.present
  have hitRanges : ForceRanges record values path after := by
    intro absent
    rw [first.present] at absent
    cases absent
  obtain ⟨nextHit, finalHit, second, retained, resultDomain⟩ := force formulas solver next actual first.ready known domains
    structural coherent active member hitRanges final first.globals.valid
  have readsUnchanged : ∀ {initial returned : State width} {output : Value Symbol Guard}
      {actual : Force record values path initial output returned} {a b : Memos},
      initial.targets path = some value → SourceCurrentAllocatedSharedTargetForce.Reads formulas solver actual a b → b = a := by
    intro initial returned output actual a b present reads
    cases reads with
    | hit => rfl
    | miss absent _ => rw [present] at absent; cases absent
  have hitReads : finalHit = final := readsUnchanged first.present second.reads
  have hitInventory : Ready formulas solver next record values base after := first.ready
  have returned : ForceReceipt formulas solver next record values base path after value after final final := by
    cases hitReads
    exact {second with ready := hitInventory}
  exact ⟨value, after, next, final, first, actual, returned, retained, resultDomain⟩

/-- Two finite leaf calls use derived intermediate facts and compose the original input bound. -/
theorem two_leaves (ready : Ready formulas solver inventory record values base before)
    (known : Values base values) (domains : Domains values) (stored : Stored before)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (inputDomain : Domain input) (ranges : LeafRanges record values path input before)
    (laterRanges : ∀ result after, Leaf record values path input before result after →
      LeafRanges record values path result after)
    (memos : Memos) (valid : Valid before.checked.native.machine.heap memos) :
    ∃ result middle next current output after last final,
      LeafReceipt formulas solver next record values base path input before result middle memos current ∧
      LeafReceipt formulas solver last record values base path result middle output after current final ∧
      Stored after ∧ Narrow input output ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient output term →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term := by
  obtain ⟨result, middle, next, current, first, middleStored, firstBound⟩ :=
    leaf_finite formulas solver inventory ready known domains stored coherent active member available inputDomain ranges memos valid
  obtain ⟨output, after, last, final, second, finalStored, secondBound⟩ :=
    leaf_finite formulas solver next first.ready known domains middleStored coherent active member first.available firstBound.1
      (laterRanges result middle first.actual) current first.globals.valid
  exact ⟨result, middle, next, current, output, after, last, final, first, second, finalStored,
    ⟨secondBound.1, Nat.le_trans secondBound.2 firstBound.2⟩,
    fun ambient term accepted => first.narrows ambient term (second.narrows ambient term accepted)⟩
end FiniteOrdinarySharedKernels
#print axioms FiniteOrdinarySharedKernels.force_then_hit
#check @FiniteOrdinarySharedKernels.force_then_hit
#print axioms FiniteOrdinarySharedKernels.two_leaves
#check @FiniteOrdinarySharedKernels.two_leaves
