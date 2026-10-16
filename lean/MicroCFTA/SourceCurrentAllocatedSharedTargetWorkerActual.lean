import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedTargetWorkerSound
import MicroCFTA.SourceCurrentAllocatedProbeTargets

/-!
# Actual checked receipts for executable shared leaves

Initial class facts derive the physical graph at each supplied literal
return. The same graph supplies its own reads, computed inventory, language
law, and probe heap. Initial support also constructs stable force and leaf
execution. No successful body or future invariant is a premise. Global
receipts remain logical evidence rather than concrete host table execution.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerActual
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State advance)
open SourceCurrentAllocatedSharedTargetWorker
open SourceCurrentAllocatedSharedTargetWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Force" => SourceCurrentAllocatedSharedTargetForce.Force
local notation "Leaf" => SourceCurrentAllocatedSharedTargetLeaf.Leaf
local notation "ForceRanges" => SourceCurrentAllocatedSharedTargetForce.ForceRanges
local notation "LeafRanges" => SourceCurrentAllocatedSharedTargetLeaf.Ranges
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable {width : Nat}

/-- A successful bind retains its exact intermediate shared state. -/
theorem bind_done_iff (first : Outcome width)
    (next : Value Symbol Guard → State width → Outcome width)
    (result : Value Symbol Guard) (after : State width) :
    first.bind next = .done result after ↔
      ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro done; exact ⟨value, state, rfl, done⟩
      · rintro ⟨_, _, same, done⟩; cases same; exact done
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, impossible, _⟩; cases impossible

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

/-- Legitimate initial class facts derive the physical force at the supplied literal return. -/
theorem force_graph (inventory : Inventory) {p h m s n : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : Path} {before after : State width} {value : Value Symbol Guard}
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (ranges : ForceRanges record values path before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (done : force p h m s n record values path before = .done value after) :
    Force record values path before value after := by
  cases present : before.targets path with
  | some target =>
      simp only [force, present] at done
      cases done
      exact .hit present
  | none =>
      cases actual : SourceCurrentAllocatedTargetWorker.target p h m s n values
          (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo with
      | done result checked saved =>
          simp only [force, present, actual] at done
          cases done
          exact .miss present (SourceCurrentAllocatedTargetWorkerSound.target_sound formulas solver inventory p h m s n
            values (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo
            ready.checked ready.admitted (fun value member => ready.captured.available value (known value member))
            (SourceCurrentTargetPathComplete.operand_domains record values domains path) ready.stored ready.covered
            (ranges present) memos valid _ checked saved actual)
      | failed => simp only [force, present, actual] at done; cases done

/-- A supplied native return derives the physical step at the same full checked state. -/
theorem step_graph {n : Nat} {target input result : Value Symbol Guard} {before after : State width}
    (ready : SourceCurrentConjunctionClassScan.Ready before.checked)
    (targetAvailable : Available before.checked.native.machine.heap target)
    (inputAvailable : Available before.checked.native.machine.heap input)
    (targetClosed : target.free = []) (inputClosed : input.free = [])
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked)
    (done : step n target input before = .done result after) :
    ∃ checked, SourceCurrentAllocatedTargetQuery.Step target input before.checked result checked ∧
      after = advance before checked := by
  cases actual : SourceEqualityNativeDemand.execute n
      (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain target input)) before.checked with
  | done value checked =>
      simp only [step, actual] at done
      cases done
      exact ⟨checked, SourceCurrentAllocatedTargetWorkerNative.of_done_ready n target input before.checked
        _ checked ready targetAvailable inputAvailable targetClosed inputClosed ranges actual, rfl⟩
  | yielded | failed | constraintError | blocked => simp only [step, actual] at done; cases done

/-- The literal leaf derives its force and checked query from their actual returned prefixes. -/
theorem leaf_graph (inventory : Inventory) {p h m s n : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : Path} {input result : Value Symbol Guard} {before after : State width}
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (ranges : LeafRanges record values path input before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (done : leaf p h m s n record values path input before = .done result after) :
    Leaf record values path input before result after := by
  obtain ⟨target, middle, first, last⟩ := (bind_done_iff _ _ result after).mp done
  have forced := force_graph formulas solver inventory ready known domains ranges.1 memos valid first
  obtain ⟨next, final, receipt⟩ := forced.verified formulas solver inventory ready known domains coherent active member
    ranges.1 memos valid
  obtain ⟨checked, query, rfl⟩ := step_graph receipt.ready.checked receipt.available
    (receipt.effects.keeps.available input available) receipt.closed closed (ranges.2 target middle forced) last
  exact .apply forced query

/-- A supplied executable force derives its own full receipt and probe heap. -/
theorem force_verified (inventory : Inventory) {p h m s n : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : Path} {before after : State width} {value : Value Symbol Guard}
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (ranges : ForceRanges record values path before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : force p h m s n record values path before = .done value after) :
    ∃ next final, SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values base path
      before value after memos final ∧ ProbeHeap after.checked.native.machine.heap := by
  have actual := force_graph formulas solver inventory ready known domains ranges memos valid done
  obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known domains coherent active member ranges memos valid
  exact ⟨next, final, receipt, SourceCurrentAllocatedProbeTargets.force_heap receipt.reads ready known probes⟩

/-- A supplied executable leaf derives narrowing and selected-subterm preservation at its own return. -/
theorem leaf_verified (inventory : Inventory) {p h m s n : Nat}
    {record : Record} {values : List (Value Symbol Guard)} {base : InternedConstructorTemplates.State Symbol Guard}
    {path : Path} {input result : Value Symbol Guard} {before after : State width}
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : path ∈ record.paths) (available : Available before.checked.native.machine.heap input)
    (closed : input.free = []) (ranges : LeafRanges record values path input before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : leaf p h m s n record values path input before = .done result after) :
    ∃ next final, SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input
      before result after memos final ∧ ProbeHeap after.checked.native.machine.heap := by
  have actual := leaf_graph formulas solver inventory ready known domains coherent active member available closed ranges memos valid done
  obtain ⟨next, final, receipt⟩ := actual.verified formulas solver inventory ready known domains coherent active member
    available closed ranges memos valid
  exact ⟨next, final, receipt, SourceCurrentAllocatedProbeTargets.leaf_heap receipt.reads ready known probes⟩

/-- Initial class support constructs stable executable forcing and all checked return facts. -/
theorem force_finite (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (ranges : ForceRanges record values path before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ value after next final,
      StableRun (fun p h m s n => force p h m s n record values path before) value after ∧
      SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values base path before value after memos final ∧
      ProbeHeap after.checked.native.machine.heap := by
  obtain ⟨value, after, next, final, _, receipt⟩ := SourceCurrentAllocatedSharedTargetForce.complete
    formulas solver inventory record values base before ready known domains coherent active path member ranges memos valid
  exact ⟨value, after, next, final, SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete receipt.actual,
    receipt, SourceCurrentAllocatedProbeTargets.force_heap receipt.reads ready known probes⟩

/-- Initial selected support constructs stable executable narrowing with the same full receipt. -/
theorem leaf_finite (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (ranges : LeafRanges record values path input before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ result after next final,
      StableRun (fun p h m s n => leaf p h m s n record values path input before) result after ∧
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input before result after memos final ∧
      ProbeHeap after.checked.native.machine.heap := by
  obtain ⟨result, after, next, final, receipt⟩ := SourceCurrentAllocatedSharedTargetLeaf.complete
    formulas solver inventory record values base before ready known domains coherent active path member input available closed ranges memos valid
  exact ⟨result, after, next, final, SourceCurrentAllocatedSharedTargetWorkerCompletion.leaf_complete receipt.actual,
    receipt, SourceCurrentAllocatedProbeTargets.leaf_heap receipt.reads ready known probes⟩

end MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerActual
