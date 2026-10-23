import MicroCFTA.SourceCurrentOriginalRowGroupAdmission
import MicroCFTA.SourceCurrentOriginalRowReconstruction

namespace MicroCFTA.SourceCurrentOriginalRowRebuildAdmission
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable (inventory : Inventory)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
local notation "holds" => guardHolds formulas solver
local notation "inputs" => inventory.inputs holds
local notation "inputView" => view inventory.source holds
local notation "inputModel" => finiteInputMeaning inputView inputs
local notation "inputRanked" => finiteRankedInput inputView inputs
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable inputView inputModel inputRanked holds
local notation "Current" => At formulas solver inventory
local notation "PairInputs" => (fun pair : Edge × Edge =>
  SourceCurrentAllocatedNativeContextCache.EdgeInputs inputView inputModel
    (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain (Prod.fst pair) (Prod.snd pair)))

/-- Retain admission after the same supplied ordinary reconstruction. -/
theorem rebuilt_admitted
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (parentEntry : Interned InternedBinderProtocol.NodeKey)
    (parentRows : List Edge) (parentDepth : Nat)
    (member : (.node parentEntry parentRows parentDepth [] : Value Symbol Guard) ∈ inventory.roots)
    (entries : List (Symbol × List Edge))
    (iteration : SourceCurrentMergeGrouping.Iteration
      (SourceCurrentPrependGrouping.fromRows (fun edge : Edge => edge.entry.key.symbol)
        parentRows) entries)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (before : Wrapper (bits + 2))
    (current : Current before.checked)
    (admitted : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      before.memo.cells handle = some ⟨pair, .returned value⟩ →
      PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair))
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨inventory.source.nodes.next, inventory.source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains inventory.source).length, 0⟩)
    (fuels : Fin entries.length → Nat) (kept : Fin entries.length → List Edge)
    (states : Fin (entries.length + 1) → Wrapper (bits + 2))
    (start : states 0 = before)
    (steps : ∀ index : Fin entries.length,
      SourceCurrentOriginalRowClusterScan.execute (fuels index)
        (.cluster (entries.get index).2.reverse []) (states index.castSucc) =
        .done (kept index) (states index.succ))
    (packets : ∀ index : Fin entries.length,
      Stable (states index.castSucc) ∧
      Good (states index.castSucc).checked ∧
      SemanticReady (states index.castSucc).checked.native.machine.heap ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains inventory.source)
        initialDomains (states index.castSucc).checked.native.machine.domains ∧
      NativeIdle (states index.castSucc).checked.native) :
    let middle := states (Fin.last entries.length)
    let output := (List.ofFn kept).flatten
    let built := run (makeNode output) middle.checked.native.machine.heap
    let after : Wrapper (bits + 2) :=
      { middle with checked :=
        { middle.checked with native := (SourceRecursiveIntersectionThunks.advance
          middle.checked.native { middle.checked.native.machine with heap := built.2 }) } }
    SourceCurrentAllocatedNativeContextCache.Contextual
      inputView inputModel inputRanked holds after.checked.native →
    Grows inventory.source after.checked.native.machine.heap →
    Extends inventory.source.nodes.issued after.checked.native.machine.heap.nodes.issued →
    Current after.checked ∧
    ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      after.memo.cells handle = some ⟨pair, .returned value⟩ →
      PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
  dsimp only
  intro finalContextual finalGrowth finalHistory
  obtain ⟨middleCurrent, middleAdmitted⟩ :=
    SourceCurrentOriginalRowGroupAdmission.groups_admitted inventory formulas solver
      bits (.node parentEntry parentRows parentDepth []) member entries iteration
      initialDomains initialValid before current admitted room fuels kept states start steps packets
      (Fin.last entries.length)
  exact ⟨⟨finalContextual, ⟨middleCurrent.covered.nodes, middleCurrent.covered.edges⟩,
    finalGrowth, finalHistory⟩, middleAdmitted⟩

end MicroCFTA.SourceCurrentOriginalRowRebuildAdmission
