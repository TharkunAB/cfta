import MicroCFTA.SourceCurrentConstrainedCapRichEditSupport
import MicroCFTA.SourceCurrentConstrainedCapForestSupport

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.RichEditChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityAnnotationLanguage SourceEqualityEdits SourceEqualityEditLeafPaths
open SourceCurrentConstrainedCapPaths SourceCurrentConstrainedCapEditSupport
open SourceCurrentConstrainedCapRequiredSupport (Preserves)
open SourceCurrentEditDomains SourceCurrentAllocatedSharedEditGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Stored" => SourceCurrentConstrainedCapSharedSupport.Stored
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
local notation "Cap" => SourceCurrentConstrainedCap.Cap

/-- A real supplied leaf receipt constructs the node read and produces all rich stores without a leaf-law premise. -/
theorem actual_leaf [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {originals : List (Value Symbol Guard)}
    {base : Heap} {token : EqualityNormalize.Path} {input result : Value Symbol Guard} {before after : SharedState width} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record originals base token input before result after memos final)
    (member : token ∈ record.paths) (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (global : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (placed : AtLeaves Plain (.editAt token) input) :
    ∃ actual : EditNode record originals (.editAt token) input before result after,
      NodeReads formulas solver base actual memos final ∧ Stored record originals after ∧
        Preserves Plain input result ∧ Cap Plain 0 result := by
  let actual : EditNode record originals (.editAt token) input before result after := .leaf receipt.actual
  have reads : NodeReads formulas solver base actual memos final := .leaf receipt
  have populated : Populated (.editAt token) := by simp only [Populated]
  have nonempty : HasLeaf (.editAt token) := ⟨[], token, by simp only [leaves, List.mem_singleton]⟩
  have allowed : SourceEqualitySharedEditEffects.Allowed record (.editAt token) := by
    simpa only [SourceEqualitySharedEditEffects.Allowed, SourceEqualityEdits.All] using member
  have safe : Safe (.editAt token) input := by
    intro path action retained
    have same : (path, action) = ([], token) := List.mem_singleton.mp retained
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact closed
  have bounded : Cap Plain 0 input := .plain 0 (at_root placed)
  have produced := SourceCurrentConstrainedCapRichEditSupport.node reads inventory 0 populated nonempty allowed ready
    available safe global known capturedClosed capturedMasks stored bounded placed
  exact ⟨actual, reads, produced⟩

private theorem placement_transport {width : Nat} {edits : Edits EqualityNormalize.Path}
    {values results : List (Value Symbol Guard)} (aligned : All₂ (Preserves Plain) values results)
    (placed : ListAtLeaves Plain edits values) : ListAtLeaves Plain edits results := by
  cases edits with
  | editAt => trivial
  | editBelow entries =>
      intro query child found result selected
      obtain ⟨original, earlier, retained⟩ := SourceEqualityProjectionLanguage.all₂_selected aligned query result selected
      exact placement_preserved retained (placed query child found original earlier)

private theorem list_safe [DecidableEq (EdgeKey Symbol Guard)] (edits : Edits EqualityNormalize.Path)
    (values : List (Value Symbol Guard)) (heap : Heap) (ready : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (available : Values heap values) (closed : ClosedValues values) :
    SourceCurrentAllocatedSharedEditEffects.ListSafe edits values := by
  cases edits with
  | editAt => trivial
  | editBelow entries =>
      intro query child found value selected
      have member := List.mem_of_getElem? selected
      exact closed_safe child value heap ready (available value member) (closed value member)

/-- Two actual edits derive the second entry stores, physical readiness, cap, and placement from the first return. -/
theorem two_edits [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {originals middleValues results : List (Value Symbol Guard)}
    {base : Heap} {before middle after : SharedState width} {memos current final : Memos}
    (firstEdits secondEdits : Edits EqualityNormalize.Path)
    {first : EditList record originals firstEdits originals before middleValues middle}
    {second : EditList record originals secondEdits middleValues middle results after}
    (firstReads : ListReads formulas solver base first memos current)
    (secondReads : ListReads formulas solver base second current final)
    (firstPopulated : Populated firstEdits) (firstAllowed : SourceEqualitySharedEditEffects.Allowed record firstEdits)
    (secondPopulated : Populated secondEdits) (secondAllowed : SourceEqualitySharedEditEffects.Allowed record secondEdits)
    (ready : Ready formulas solver inventory record originals base before)
    (global : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (known : Values base originals) (capturedClosed : ClosedValues originals)
    (capturedMasks : ∀ path ∈ record.paths, ForestSupported Plain (path.map Int.ofNat) originals)
    (stored : Stored record originals before) (depth : Nat) (bounded : ∀ value ∈ originals, Cap Plain depth value)
    (firstPlaced : ListAtLeaves Plain firstEdits originals) (secondPlaced : ListAtLeaves Plain secondEdits originals) :
    Stored record originals after ∧ All₂ (Preserves Plain) originals results ∧ (∀ value ∈ results, Cap Plain depth value) ∧
      ∀ path, ForestSupported Plain path originals → ForestSupported Plain path results := by
  have available : Values before.checked.native.machine.heap originals := fun value member => ready.captured.available value (known value member)
  have firstSafe := list_safe firstEdits originals before.checked.native.machine.heap ready.checked.semantic available capturedClosed
  have firstResult := SourceCurrentConstrainedCapRichEditSupport.list firstReads inventory depth firstPopulated firstAllowed ready available
    firstSafe global known capturedClosed capturedMasks stored bounded firstPlaced
  obtain ⟨next, physical⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects firstReads firstPopulated firstAllowed ready available firstSafe global
  have middleClosed : ClosedValues middleValues := SourceCurrentConstrainedCapForestSupport.closed_transport physical.transport capturedClosed
  have middlePlaced := placement_transport firstResult.2.1 secondPlaced
  have secondSafe := list_safe secondEdits middleValues middle.checked.native.machine.heap physical.ready.checked.semantic physical.available middleClosed
  have secondResult := SourceCurrentConstrainedCapRichEditSupport.list secondReads next depth secondPopulated secondAllowed physical.ready physical.available
    secondSafe physical.globals.valid known capturedClosed capturedMasks firstResult.1 firstResult.2.2 middlePlaced
  have aligned := SourceCurrentConstrainedCapForestSupport.trans firstResult.2.1 secondResult.2.1
  exact ⟨secondResult.1, aligned, secondResult.2.2, SourceCurrentConstrainedCapRequiredSupport.forest_supported Plain aligned⟩

end MicroCFTA.RichEditChecks

#print axioms MicroCFTA.RichEditChecks.actual_leaf
#check @MicroCFTA.RichEditChecks.actual_leaf
#print axioms MicroCFTA.RichEditChecks.two_edits
#check @MicroCFTA.RichEditChecks.two_edits
