import MicroCFTA.SourcePruningEnumerationPrefixCheckpointModels
import MicroCFTA.SourcePruningEnumerationPrefixAdmission
import MicroCFTA.SourcePruningEnumerationPreparedPreparationResources

/-!
# Original models through the actual prefix and one native preparation

The original packet supplies every retained prefix and preparation field.
The stored narrowed handle and the prepared result remain distinct.
The same original assignment satisfies the actual entered cache and accepts
its prepared value under the original annotation policies.
No recursive output model or future branch success is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedEntryModels
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentConstrainedCapEditForecast (headProfile)
open SourcePruningEnumerationSelectedStep (Result PrefixValid runPrefix)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationNodes (lookupNode)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain actual admission and preparation resources, then transport the original model. -/
theorem narrowed_preparation_complete_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap)
    (observed : Result width Typing)
    (actual : runPrefix holeKey fits admits graph templates stop order metadata
      fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    match (generalizing := false) observed with
    | .narrowed _ _ reached queries _ (some after) _ _ =>
        ∃ (handle : Nat) (scs : List Suspended) (value : Node) (final : Memos),
          (Post formulas solver inventory caller reached final ∧ final.query = queries ∧
          Packet formulas solver inventory reached final metadata after ∧
          EnumerationDriver.Ready uv after.core ∧
          after.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
          lookupNode reached.checked.native.machine.heap handle = some value ∧
          Available reached.checked.native.machine.heap value ∧ value.free = [] ∧
          EnumerationReferences.IncomingAvoid uv after.core ∧
          EnumerationDependencies.InputsPending after.core scs ∧
          (∀ sc ∈ scs, sc.var < before.core.counter) ∧
          scs.length ≤ SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
          after.core.counter = before.core.counter ∧ after.waiting = before.waiting ∧
          Fits (headProfile profile) reached.checked ∧ Heap property reached.checked.native.machine.heap) ∧
          ∃ (preparationBound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
            ((((∀ extra, SourcePruningEnumerationSelectedPreparation.run (preparationBound + extra) (preparationBound + extra) uv reached after =
              ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
            lookupNode reached.checked.native.machine.heap handle = some decoded ∧
            Post formulas solver inventory reached
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final ∧
            Packet formulas solver inventory
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap) final metadata entered ∧
            EnumerationDriver.RenderStable after.core entered.core ∧
            EnumerationDriver.Ready uv entered.core ∧
            entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
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
                InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
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
          (∀ symbol annotation child, assignment uv = .node symbol [child] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
            admits (holeKey metadata.typing uv) annotation = true ∧
              fits (holeKey metadata.typing uv) symbol = true) →
          (∀ annotation first second third fourth,
            assignment uv = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing uv) annotation = true) →
          (∀ annotation first second,
            assignment uv = .node ("filter", FullSyntax.Formula.top) [first, second] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing uv) annotation = true) →
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient heap)
            residualMeaning assignment entered.core ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver)
            ambient result (assignment uv)
    | _ => True := by
  have admission := SourcePruningEnumerationPrefixAdmission.narrowed_admission
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller memos before packet chosen profile property bounded known observed valid
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have ready := (SourcePruningEnumerationRestart.selected stop order metadata caller before uv
    packet.valid packet.safe chosen).1
  have currentValid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos
      (runPrefix holeKey fits admits graph templates stop order metadata
        fuel fuel fuel fuel fuel fuel uv caller before memos.query) := by
    simpa only [actual] using valid
  have models := SourcePruningEnumerationSelectedStep.prefix_accepting
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
    fuel uv caller before memos packet.context ready realized currentValid
  rw [actual] at models
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          obtain ⟨handle, scs, value, final, retained⟩ := admission
          have admissionPacket := retained
          obtain ⟨post, saved, afterPacket, afterReady, stored, _decoded, _available, _closed,
            _incoming, _pending, _ids, _lengths, _counter, _waiting, afterFits, afterKnown⟩ := retained
          obtain ⟨preparationBound, decoded, result, heap, entered, preparation, preparedKnown⟩ :=
            SourcePruningEnumerationSelectedPreparation.complete_resources_known formulas solver inventory
              reached final metadata after uv handle scs afterPacket afterReady stored
              (headProfile profile) afterFits property afterKnown
          have originalPreparation := And.intro preparation preparedKnown
          obtain ⟨preparedPacket, _preparedFits, _preparedMass⟩ := preparation
          obtain ⟨_preparationRun, _lookup, preparationPost, _enteredPacket, _stable,
            _enteredReady, _enteredStored, _counterSame, _values, _flags, _waiting,
            _resultAvailable, _resultClosed, _language, preparedModels⟩ := preparedPacket
          refine ⟨handle, scs, value, final, admissionPacket, preparationBound, decoded, result,
            heap, entered, originalPreparation, post.trans preparationPost, ?_⟩
          intro ambient residualMeaning assignment satisfied unary application filtered
          have afterSatisfied := models ambient residualMeaning assignment satisfied unary application filtered
          have prepared := preparedModels (SourceEqualityPCSGuard.holds formulas solver)
            ambient residualMeaning assignment
          exact ⟨prepared.1.mpr afterSatisfied, prepared.2 afterSatisfied⟩

end MicroCFTA.SourcePruningEnumerationPreparedEntryModels
