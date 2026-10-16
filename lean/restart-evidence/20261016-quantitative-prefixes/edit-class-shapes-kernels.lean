import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPassShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts

namespace MicroCFTA.QuantitativePrefixChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape ChildrenShape)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedFiniteOrdinaryEditCallbackCounts
open MergedOrdinaryHeight (height childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentAllocatedFiniteOrdinarySharedProfiles.Stored
local notation "TargetRows" => SourceCurrentAllocatedFiniteOrdinarySharedForceResources.targetRows
local notation "OutRows" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputRows
local notation "OutArity" => SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.outputArity
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PassRows" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputRows
local notation "PassArity" => SourceCurrentAllocatedFiniteOrdinaryPassResources.outputArity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}

/-- Two actual Empty callbacks retain one captured slot envelope without any constructor headroom premise. -/
theorem repeated_empty_positions
    {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before middle after : Shared width} {firstValue secondValue : Value Symbol Guard}
    {inventory firstInventory secondInventory : Inventory} {memos current final : Memos}
    (first : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver firstInventory record originals base path
      .empty before firstValue middle memos current)
    (second : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver secondInventory record originals base path
      .empty middle secondValue after current final)
    (ready : Ready formulas solver inventory record originals base before)
    (known : Values base originals) (coherent : SourceEqualityClassOrder.Coherent record) (member : path ∈ record.paths)
    (rows arity count depth bound : Nat) (captured : ChildrenShape rows arity originals)
    (lengthBound : originals.length ≤ count) (pathsBound : ∀ path ∈ record.paths, path.length ≤ depth)
    (capturedHeight : childrenHeight originals ≤ bound)
    (stored : Stored (TargetRows record rows count depth bound) (max arity 1) bound before)
    (valid : Valid before.checked.native.machine.heap memos) :
    ∃ actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0
        ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after,
      ChildrenReads formulas solver base actual memos final ∧ ChildrenCount actual 2 ∧
      Stored (TargetRows record rows count depth bound) (max arity 1) bound after ∧
      ChildrenShape (OutRows record rows count depth bound 0) (OutArity arity 0) [firstValue, secondValue] ∧
      childrenHeight [firstValue, secondValue] ≤ 0 ∧
      ∃ next, SourceCurrentAllocatedSharedEditEffects.ChildrenReceipt formulas solver next record originals base
        ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after memos final := by
  let firstNode := EditNode.leaf first.actual
  let secondNode := EditNode.leaf second.actual
  let tail : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 1
      ([.empty] : List (Value Symbol Guard)) middle [secondValue] after := .selected 1 rfl secondNode .nil
  let actual : EditChildren record originals [(0, .editAt path), (1, .editAt path)] 0
      ([.empty, .empty] : List (Value Symbol Guard)) before [firstValue, secondValue] after := .selected 0 rfl firstNode tail
  have reads : ChildrenReads formulas solver base actual memos final :=
    .selected (found := rfl) (first := firstNode) (rest := tail) (.leaf first)
      (.selected (found := rfl) (first := secondNode) (.leaf second) .nil)
  have populated : Populated (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Populated]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by simp only [Populated], [], path, by simp [leaves]⟩
  have allowed : Allowed record (.editBelow [(0, .editAt path), (1, .editAt path)]) := by
    rw [Allowed, All]
    intro index child included
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at included
    rcases included with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simpa only [All] using member
  have available : Values before.checked.native.machine.heap ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro value selected
    have same : value = .empty := by simpa using selected
    exact same ▸ empty_available _
  have safe : ChildrenSafe [(0, .editAt path), (1, .editAt path)] 0 ([.empty, .empty] : List (Value Symbol Guard)) := by
    intro query child found value selected
    have same : value = .empty := by
      have present := List.mem_of_getElem? selected
      simpa using present
    subst value
    exact closed_safe _ _ _ ready.checked.semantic (empty_available _) rfl
  have produced := SourceCurrentAllocatedFiniteOrdinaryEditShapes.children reads populated allowed ready available safe valid
    known coherent rows arity count depth bound 0 0 0 captured lengthBound pathsBound capturedHeight stored
    (show ChildrenShape 0 0 ([.empty, .empty] : List (Value Symbol Guard)) from ⟨trivial, trivial, trivial⟩) (by decide)
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedSharedEditEffects.children_effects reads populated allowed ready available safe valid
  exact ⟨actual, reads, .selected (found := rfl) (.leaf first.actual) (.selected (found := rfl) (.leaf second.actual) .nil),
    produced.1, produced.2.1, produced.2.2.2.2, next, receipt⟩

/-- An arbitrary actual pass supplies the profile and strong native stores for the following actual query. -/
theorem pass_then_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {records : List SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after queried : SourceEqualityNativeDemand.State width} {memo saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard}
    {memos final : Memos} {actual : SourceCurrentAllocatedClassPass.Pass records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final) (inventory : Inventory)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : SourceCurrentConjunctionClassScan.Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (profiles : SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored memo)
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (chosen : Value Symbol Guard) (member : chosen ∈ results) (fuel : Nat) (result : Value Symbol Guard)
    (trace : SourceCurrentAllocatedNativePhysicalTraceCompletion.Trace fuel
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain chosen chosen)) after
      (.code (.pure result)) queried) :
    ∃ next, SourceCurrentAllocatedClassPass.Receipt formulas solver next records values before memo results after saved memos final ∧
      SourceCurrentAllocatedFiniteOrdinaryStored.Stored queried.native ∧
      SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored queried.native ∧
      SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored saved ∧
      NodeShape ((PassRows records rows count depth bound) * (PassRows records rows count depth bound))
        (max (PassArity records arity) 1) result ∧ height result ≤ bound := by
  have produced := SourceCurrentAllocatedFiniteOrdinaryClassPassShapes.pass formulas solver inventory reads coherent active
    ready admitted available physical profiles native output covered valid rows arity count depth bound profile lengthBound pathsBound heightBound
  have domains : ∀ record ∈ records, ∀ path ∈ record.paths,
      SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values :=
    fun _ _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available
      (ChildrenShape.domain values profile) _
  obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Pass.verified formulas solver inventory reads coherent active
    ready admitted available domains physical covered valid
  have chosenProfile := ChildrenShape.member results produced.2.2.2.1 chosen member
  have structural := SourceCurrentAllocatedFiniteOrdinaryExecution.node_trace
    ⟨IntersectionEmptyDomain.emptyDomain, chosen, chosen⟩ after queried fuel result trace receipt.ready.good receipt.ready.semantic
    produced.1 ⟨rfl, NodeShape.domain _ chosenProfile, NodeShape.domain _ chosenProfile⟩
  have shaped := SourceCurrentAllocatedFiniteOrdinaryOutputExecution.node_trace
    ⟨IntersectionEmptyDomain.emptyDomain, chosen, chosen⟩ after queried fuel result trace receipt.ready.good receipt.ready.semantic
    produced.2.1 rfl _ _ chosenProfile chosenProfile
  have chosenHeight := (MergedOrdinaryHeight.childrenHeight_le results bound).mp produced.2.2.2.2.2.2 chosen member
  exact ⟨next, receipt, structural.1, shaped.1, produced.2.2.1, shaped.2,
    Nat.le_trans structural.2.2.1 chosenHeight⟩

end MicroCFTA.QuantitativePrefixChecks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 10000000
#print axioms MicroCFTA.QuantitativePrefixChecks.repeated_empty_positions
#check @MicroCFTA.QuantitativePrefixChecks.repeated_empty_positions
#print axioms MicroCFTA.QuantitativePrefixChecks.pass_then_query
#check @MicroCFTA.QuantitativePrefixChecks.pass_then_query
