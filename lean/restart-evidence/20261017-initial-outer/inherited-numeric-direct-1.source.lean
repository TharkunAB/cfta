import MicroCFTA.SourceCurrentAllocatedPartialStepEffects
import MicroCFTA.SourceCurrentConstrainedCapGeneratedQueryResources

/-!
# Initial resources for inherited combination and indexed descent

Both prefixes change only equality operations. The constructor heap,
native cells, domain cache, and caller tables stay exact. The initial
node, edge, domain, and payload-mass profile therefore stays sufficient.
The inherited contradiction branch demands no field or residency.
-/
namespace MicroCFTA.SourceCurrentInheritedNumeric
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Frame Fits)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
local notation "prefixState" => SourceCurrentAllocatedPartialGraph.prefixState
local notation "descend" => SourceCurrentAllocatedPartialGraph.descend
variable {width : Nat} [DecidableEq (EdgeKey Symbol Guard)]

private theorem prefix_transfer
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard) (inherited combined : EqValue) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (receipt : SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory original inherited before.checked combined) :
    Frame formulas solver inventory (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) ∧
      Fits profile (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) ∧
      Post formulas solver inventory before
        (advance before (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) before.fourth before.merge) memos := by
  refine ⟨⟨receipt.ready, receipt.admitted, frame.context, frame.joint, frame.origins⟩,
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩, ?_⟩
  exact ⟨⟨receipt.ready, receipt.admitted,
    initial.sound.advance formulas solver _ before.fourth before.merge receipt.effects,
    initial.stored, initial.covered, initial.correct, initial.globals, initial.probes⟩,
    receipt.effects, Cache.extends_refl _, fun _ _ found => found⟩

/-- Initial live fields construct the inherited prefix; inherited contradiction skips these facts. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (original : Guard) (inherited : EqValue) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (live : inherited ≠ .contradiction → FieldAvailable before.checked.operations original ∧
      EqReady before.checked.operations.constraints inherited) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory original inherited before.checked combined ∧
      Frame formulas solver inventory (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) ∧
      Fits profile (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) ∧
      Post formulas solver inventory before
        (advance before (SourceCurrentAllocatedInheritedPrefix.state before.checked original inherited) before.fourth before.merge) memos := by
  cases inherited with
  | contradiction =>
      have receipt := SourceCurrentAllocatedInheritedPrefix.contradiction formulas solver inventory original before.checked
        initial.ready initial.admitted
      exact ⟨.contradiction, receipt, prefix_transfer formulas solver inventory original .contradiction .contradiction
        before memos initial frame profile fits receipt⟩
  | live identity records =>
      obtain ⟨field, inheritedReady⟩ := live (by intro impossible; cases impossible)
      obtain ⟨combined, receipt⟩ := SourceCurrentAllocatedInheritedPrefix.finite formulas solver inventory original
        (.live identity records) before.checked initial.ready initial.admitted field inheritedReady
      exact ⟨combined, receipt, prefix_transfer formulas solver inventory original (.live identity records) combined
        before memos initial frame profile fits receipt⟩

/-- A live resident edge supplies its own initial field; inherited contradiction needs no residency. -/
theorem resident_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (edge : EdgeValue Symbol Guard) (inherited : EqValue) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (resident : inherited ≠ .contradiction → InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : inherited ≠ .contradiction → EqReady before.checked.operations.constraints inherited) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint inherited before.checked combined ∧
      Frame formulas solver inventory (prefixState before edge inherited).checked ∧ Fits profile (prefixState before edge inherited).checked ∧
      Post formulas solver inventory before (prefixState before edge inherited) memos := by
  apply complete formulas solver inventory edge.entry.key.constraint inherited before memos initial frame profile fits
  intro different
  exact ⟨initial.ready.good.fields edge.entry.key edge (resident different), inheritedReady different⟩

/-- The ready combined value constructs its literal indexed child without changing the profile. -/
theorem descent (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (before : Caller width) (memos : Memos) (combined : EqValue) (index : Nat)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked) (inheritedReady : EqReady before.checked.operations.constraints combined) :
    SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory before combined index ∧
      Frame formulas solver inventory (descend before combined index).2.checked ∧
      Fits profile (descend before combined index).2.checked ∧
      Post formulas solver inventory before (descend before combined index).2 memos := by
  obtain ⟨receipt, post⟩ := SourceCurrentAllocatedPartialStepEffects.descent formulas solver inventory before memos initial
    combined index inheritedReady
  exact ⟨receipt, ⟨receipt.ready, receipt.admitted, frame.context, frame.joint, frame.origins⟩,
    ⟨fits.nodes, fits.edges, fits.domains, fits.stored⟩, post⟩

/-- Own inherited combination feeds its actual returned value into the next indexed descent. -/
theorem prefix_descent (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (edge : EdgeValue Symbol Guard) (inherited : EqValue) (index : Nat) (before : Caller width) (memos : Memos)
    (initial : Context formulas solver inventory before memos) (frame : Frame formulas solver inventory before.checked)
    (profile : Profile) (fits : Fits profile before.checked)
    (resident : inherited ≠ .contradiction → InternedEdgeResidency.EdgeResident before.checked.native.machine.heap edge)
    (inheritedReady : inherited ≠ .contradiction → EqReady before.checked.operations.constraints inherited) :
    ∃ combined, SourceCurrentAllocatedInheritedPrefix.Receipt formulas solver inventory edge.entry.key.constraint inherited before.checked combined ∧
      SourceCurrentAllocatedPartialDescent.Receipt formulas solver inventory (prefixState before edge inherited) combined index ∧
      Frame formulas solver inventory (descend (prefixState before edge inherited) combined index).2.checked ∧
      Fits profile (descend (prefixState before edge inherited) combined index).2.checked ∧
      Post formulas solver inventory before (descend (prefixState before edge inherited) combined index).2 memos := by
  obtain ⟨combined, prefix, firstFrame, firstFits, firstPost⟩ := resident_complete formulas solver inventory edge inherited before memos
    initial frame profile fits resident inheritedReady
  obtain ⟨child, finalFrame, finalFits, lastPost⟩ := descent formulas solver inventory (prefixState before edge inherited) memos combined index
    firstPost.context firstFrame profile firstFits prefix.combinedReady
  exact ⟨combined, prefix, child, finalFrame, finalFits, firstPost.trans lastPost⟩

end MicroCFTA.SourceCurrentInheritedNumeric
