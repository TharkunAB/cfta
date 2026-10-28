import MicroCFTA.SourcePruningEnumerationPreparedEntryModels

/-!
# Original-input model transport to actual prepared branch entry

One original packet fixes a common selected-prefix work bound.
Each actual retained narrowing cache derives one native preparation.
Every earlier prefix, admission and preparation field remains available.
The same original accepted assignment reaches the prepared branch entry.
The statement supplies no future successful receipt or semantic model.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedEntryModels
open SourcePruningEnumerationRecursive (Packet)
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)
open InternedProbeProvenance
open SourcePruningEnumerationNodes (lookupNode)
open SourceCurrentConstrainedCapEditForecast (headProfile)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original inputs derive the full selected-prefix and native-preparation model path. -/
theorem packet_prefix_preparation_complete_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        selected caller before memos.query
      ((PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (bound + extra) selected caller before memos observed ∧
      Resources profile property caller observed ∧
      match observed with
      | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
      | .narrowed _ _ reached queries _ (some after) _ _ =>
          ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
            Packet formulas solver inventory reached final metadata after
      | _ => True) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment before.core →
          (∀ symbol annotation child, assignment selected = .node symbol [child] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
            admits (holeKey metadata.typing selected) annotation = true ∧
              fits (holeKey metadata.typing selected) symbol = true) →
          (∀ annotation first second third fourth,
            assignment selected = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          (∀ annotation first second,
            assignment selected = .node ("filter", FullSyntax.Formula.top) [first, second] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          match observed with
          | .parked _ (some after) _ =>
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
                residualMeaning assignment after.core
          | .narrowed _ _ reached _ _ (some after) _ _ =>
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
                residualMeaning assignment after.core
          | _ => False) ∧
    match observed with
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ (handle : Nat) (scs : List Suspended) (value : Node) (final : Memos),
          (Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after ∧
          EnumerationDriver.Ready selected after.core ∧
          after.core.values[selected]? = some (.unenumerated (some handle) scs) ∧
          lookupNode reached.checked.native.machine.heap handle = some value ∧
          Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
          EnumerationReferences.IncomingAvoid selected after.core ∧
          EnumerationDependencies.InputsPending after.core scs ∧
          (∀ sc ∈ scs, sc.var < before.core.counter) ∧
          scs.length ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
          after.core.counter = before.core.counter ∧ after.waiting = before.waiting ∧
          Fits (headProfile profile) reached.checked ∧ Heap property reached.checked.native.machine.heap) ∧
          ∃ (preparationBound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
            ((((∀ extra, SourcePruningEnumerationSelectedPreparation.run (preparationBound + extra) (preparationBound + extra) selected reached after =
              ([.ok ((selected, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
            lookupNode reached.checked.native.machine.heap handle = some decoded ∧
            Post formulas solver inventory reached
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final ∧
            Packet formulas solver inventory
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final metadata entered ∧
            EnumerationDriver.RenderStable after.core entered.core ∧
            EnumerationDriver.Ready selected entered.core ∧
            entered.core.values[selected]? = some (.unenumerated (some handle) scs) ∧
            entered.core.counter = after.core.counter ∧ entered.core.values = after.core.values ∧
            entered.expandable = after.expandable ∧ entered.waiting = after.waiting ∧
            Available heap result ∧ result.free = [] ∧
            (∀ holds ambient term,
              InternedGuardedLanguage.meaning holds ambient result term ↔
                InternedGuardedLanguage.meaning holds ambient decoded term) ∧
            ∀ holds ambient residualMeaning assignment,
              (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
                residualMeaning assignment entered.core ↔
              Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
                reached.checked.native.machine.heap) residualMeaning assignment after.core) ∧
              (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
                reached.checked.native.machine.heap) residualMeaning assignment after.core →
                InternedGuardedLanguage.meaning holds ambient result (assignment selected))) ∧
            SourceCurrentConstrainedCapGeneratedQueryResources.Fits
              (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (headProfile profile))
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap).checked ∧
            InternedValueMass.value result ≤
              (SourcePruningEnumerationSelectedValueCaller.normalizationProfile (headProfile profile)).mass) ∧
            SourceEqualityAnnotationHeap.Heap property heap) ∧
            Post formulas solver inventory caller
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment before.core →
          (∀ symbol annotation child, assignment selected = .node symbol [child] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
            admits (holeKey metadata.typing selected) annotation = true ∧
              fits (holeKey metadata.typing selected) symbol = true) →
          (∀ annotation first second third fourth,
            assignment selected = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          (∀ annotation first second,
            assignment selected = .node ("filter", FullSyntax.Formula.top) [first, second] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient heap)
            residualMeaning assignment entered.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient result (assignment selected)
    | _ => True := by
  obtain ⟨bound, complete⟩ := SourcePruningEnumerationRecursive.packet_prefix_complete_resources_models
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before packet profile property bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  have retained := complete extra selected chosen
  refine ⟨retained, ?_⟩
  exact narrowed_preparation_complete_models holeKey fits admits graph templates checkEmpty edgesOf stop order
    metadata formulas solver inventory (bound + extra) selected caller memos before packet chosen
    profile property bounded known _ rfl retained.1.1

end MicroCFTA.SourcePruningEnumerationPreparedEntryModels
