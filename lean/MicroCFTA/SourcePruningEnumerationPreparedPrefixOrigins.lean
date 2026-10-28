import MicroCFTA.SourcePruningEnumerationPreparedPrefixModels
import MicroCFTA.SourcePruningEnumerationPrefixCheckpointOrigins

/-!
# Original paths at the same actual prepared entry

The original prefix and preparation producer is used once.
All old resources and model observers remain at the same witnesses.
Unchanged counters preserve original paths at the actual entered cache.
Preparation bounds remain local to each actual prefix observation.
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

/-- Retain all actual prefix and entry fields and their same-assignment original paths. -/
theorem packet_prefix_preparation_complete_origins
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
      (((PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
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
            (((((∀ extra, SourcePruningEnumerationSelectedPreparation.run (preparationBound + extra) (preparationBound + extra) selected reached after =
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
            ambient result (assignment selected)) ∧
            ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
              SourcePruningEnumerationOrigins.AssignmentOrigins whole entered.core.counter assignment ↔
                SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
    | _ => True) ∧
      ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        match observed with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
            SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
              SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
        | _ => True := by
  obtain ⟨bound, complete⟩ := packet_prefix_preparation_complete_models
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before packet profile property bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  have retained := complete extra selected chosen
  have prefixOrigins := SourcePruningEnumerationSelectedStep.PrefixValid.assignment_origins
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (bound + extra) selected caller before memos
    (runPrefix holeKey fits admits graph templates stop order metadata
      (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      selected caller before memos.query) retained.1.1.1
  refine ⟨⟨retained.1, ?_⟩, prefixOrigins⟩
  generalize actual : runPrefix holeKey fits admits graph templates stop order metadata
    (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
    selected caller before memos.query = observed at retained ⊢
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨handle, scs, value, final, admission, preparationBound, decoded, result, heap, entered,
            preparation, post, models⟩ := retained.2
          have prefixCounter : after.core.counter = before.core.counter := by
            obtain ⟨_post, _query, _packet, _ready, _stored, _decoded, _available, _closed,
              _incoming, _pending, _ids, _length, counter, _rest⟩ := admission
            exact counter
          have entryCounter : entered.core.counter = after.core.counter := by
            obtain ⟨_run, _lookup, _post, _packet, _stable, _ready, _stored, counter, _rest⟩ := preparation.1.1
            exact counter
          refine ⟨handle, scs, value, final, admission, preparationBound, decoded, result, heap, entered,
            ⟨preparation, post, models⟩, ?_⟩
          intro whole assignment
          rw [entryCounter, prefixCounter]

end MicroCFTA.SourcePruningEnumerationPreparedEntryModels
