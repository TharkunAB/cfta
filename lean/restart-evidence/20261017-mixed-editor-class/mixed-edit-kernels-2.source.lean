import MicroCFTA.SourceCurrentConstrainedCapMixedEdit
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true

namespace MicroCFTA.MixedEditKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityAnnotationLanguage SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapMixedShared.Stored
local notation "Cap" => SourceCurrentConstrainedCap.Cap
local notation "outputDepth" => SourceCurrentConstrainedCapMixedEdit.outputDepth
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A warm slot and initial numeric checks construct a real leaf edit on a nonhereditary ordinary input. -/
theorem constructed_warm_nonplain_leaf
    (bits : Nat) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard))
    (base : Heap) (before : SharedState (bits + 2)) (token : EqualityNormalize.Path) (target : Value Symbol Guard)
    (ready : Ready formulas solver inventory record originals base before)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (member : token ∈ record.paths) (present : before.targets token = some target)
    (nodeEntry : Interned NodeKey) (edgeEntry : Interned (EdgeKey Symbol Guard)) (level : Nat)
    (bad : ¬ Plain edgeEntry.key.constraint)
    (available : Available before.checked.native.machine.heap (.node nodeEntry [.mk edgeEntry []] level []))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (stored : Stored record originals before) (capturedDepth : Nat)
    (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (nodes : before.checked.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.checked.native.machine.domains.next +
      2 ^ (before.checked.native.machine.heap.nodes.next +
        before.checked.native.machine.heap.nodes.next * before.checked.native.machine.heap.nodes.next) < 2 ^ (bits + 1)) :
    ¬ Annotated Plain (.node nodeEntry [.mk edgeEntry []] level []) ∧
    ∃ result after next final,
      ∃ actual : EditNode record originals (.editAt token) (.node nodeEntry [.mk edgeEntry []] level []) before result after,
        NodeReads formulas solver base actual memos final ∧
        SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base token
          (.node nodeEntry [.mk edgeEntry []] level []) before result after memos final ∧
        Stored record originals after ∧ Cap Plain (outputDepth capturedDepth 1 (.editAt token)) result := by
  let input : Value Symbol Guard := .node nodeEntry [.mk edgeEntry []] level []
  have closed : input.free = [] := rfl
  have bounded : Cap Plain 1 input := .node 0 nodeEntry [.mk edgeEntry []] level [] (by simp)
  have nonplain : ¬ Annotated Plain input := by
    intro annotated
    cases annotated with
    | node _ _ _ _ guards _ => exact bad (guards (.mk edgeEntry []) (by simp))
  have targetFacts := (ready.receipts token target present).available
  have targetOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original target before.checked.native.machine.heap
    ready.checked.good.native.machine.1.coherent targetFacts.1 targetFacts.2
  have inputOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original input before.checked.native.machine.heap
    ready.checked.good.native.machine.1.coherent available closed
  have words := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before.checked ready.checked.good
    ready.checked.semantic target input targetOriginal inputOriginal targetFacts.1 available nodes edges room).1
  have ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record originals token input before := by
    refine ⟨?_, ?_⟩
    · intro absent
      rw [present] at absent
      cases absent
    · intro value middle forced
      cases forced with
      | hit selected =>
          have same : target = value := Option.some.inj (present.symm.trans selected)
          subst value
          exact words
      | miss absent _ =>
          rw [present] at absent
          cases absent
  obtain ⟨result, after, next, final, receipt⟩ := SourceCurrentAllocatedSharedTargetLeaf.complete
    formulas solver inventory record originals base before ready known domains coherent active token member input
    available closed ranges memos valid
  let actual : EditNode record originals (.editAt token) input before result after := .leaf receipt.actual
  have reads : NodeReads formulas solver base actual memos final := .leaf receipt
  have populated : Populated (.editAt token) := by simp only [Populated]
  have nonempty : HasLeaf (.editAt token) := ⟨[], token, by simp only [leaves, List.mem_singleton]⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editAt token) := by
    simpa only [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All] using member
  have safe : Safe (.editAt token) input := by
    intro path action retained
    have same : (path, action) = ([], token) := List.mem_singleton.mp (by simpa only [leaves] using retained)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using closed
  have produced := SourceCurrentConstrainedCapMixedEdit.node reads inventory capturedDepth 1 populated nonempty allowed
    ready available safe valid known domains stored capturedCaps bounded
  exact ⟨nonplain, result, after, next, final, actual, reads, receipt, produced⟩

private theorem safe_transport {edits : Edits EqualityNormalize.Path} {values results : List (Value Symbol Guard)}
    (aligned : All₂ Transport values results)
    (safe : SourceCurrentAllocatedSharedEditEffects.ListSafe edits values) :
    SourceCurrentAllocatedSharedEditEffects.ListSafe edits results := by
  cases edits with
  | editAt => trivial
  | editBelow entries =>
      intro query child found result selected
      obtain ⟨original, earlier, relation⟩ := SourceEqualityProjectionLanguage.all₂_selected aligned query result selected
      intro path action retained
      exact relation path (safe query child found original earlier path action retained)

/-- The first actual return supplies the next stores, cap, globals, and selected domains for a second edit. -/
theorem two_actual_edits
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {originals values middleValues results : List (Value Symbol Guard)}
    {base : Heap} {before middle after : SharedState width} {memos current final : Memos}
    (firstEdits secondEdits : Edits EqualityNormalize.Path)
    {first : EditList record originals firstEdits values before middleValues middle}
    {second : EditList record originals secondEdits middleValues middle results after}
    (firstReads : ListReads formulas solver base first memos current)
    (secondReads : ListReads formulas solver base second current final)
    (firstPopulated : Populated firstEdits) (firstAllowed : SourceEqualitySharedEditEffects.Allowed record firstEdits)
    (secondPopulated : Populated secondEdits) (secondAllowed : SourceEqualitySharedEditEffects.Allowed record secondEdits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values)
    (firstSafe : SourceCurrentAllocatedSharedEditEffects.ListSafe firstEdits values)
    (secondSafe : SourceCurrentAllocatedSharedEditEffects.ListSafe secondEdits values)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (known : Values base originals)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (capturedDepth inputDepth : Nat)
    (capturedCaps : ∀ original ∈ originals, Cap Plain capturedDepth original)
    (inputCaps : ∀ value ∈ values, Cap Plain inputDepth value) :
    Stored record originals after ∧
    ∀ value ∈ results, Cap Plain (outputDepth capturedDepth (outputDepth capturedDepth inputDepth firstEdits) secondEdits) value := by
  have firstResult := SourceCurrentConstrainedCapMixedEdit.list firstReads inventory capturedDepth inputDepth
    firstPopulated firstAllowed ready available firstSafe valid known domains stored capturedCaps inputCaps
  obtain ⟨next, physical⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects firstReads firstPopulated firstAllowed
    ready available firstSafe valid
  have laterSafe := safe_transport physical.transport secondSafe
  exact SourceCurrentConstrainedCapMixedEdit.list secondReads next capturedDepth (outputDepth capturedDepth inputDepth firstEdits)
    secondPopulated secondAllowed physical.ready physical.available laterSafe physical.globals.valid known domains
    firstResult.1 capturedCaps firstResult.2

end MicroCFTA.MixedEditKernels

#print axioms MicroCFTA.MixedEditKernels.constructed_warm_nonplain_leaf
#check @MicroCFTA.MixedEditKernels.constructed_warm_nonplain_leaf
#print axioms MicroCFTA.MixedEditKernels.two_actual_edits
#check @MicroCFTA.MixedEditKernels.two_actual_edits
