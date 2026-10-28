import MicroCFTA.SourcePruningEnumerationSelectedOpaquePreparationModels
import MicroCFTA.SourcePruningEnumerationSelectedContinuations

/-!
# The actual hook after original-model opaque completion

The original preparation and opaque witnesses stay fixed before the hook.
The complete previous result remains before the appended hook equation.
An arbitrary hook receives the actual completed fragment, caller and cache.
Its returned stop, outputs and native endpoint remain in ReceiptContinuation.
No successful hook or emitted-output model is supplied as an input.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedDispatch
open Language EnumerationState EnumerationCorrectness EnumerationProgress
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
universe u v
variable {Typing : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Original opaque completion invokes any actual hook at the same sufficient common bound. -/
theorem complete_resources_opaque_hook_models
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (metadata : SourcePruningRecordTypes.Metadata Typing)
    (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (profile : SourceCurrentAllocatedNativeResourceForecast.Profile)
    (fits : SourceCurrentConstrainedCapGeneratedQueryResources.Fits profile caller.checked)
    (proper : ProperState before.core)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (checkEmpty : Bool) :
    ∃ (bound : Nat) (decoded result : Node) (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Cached),
      (((∀ extra, SourcePruningEnumerationSelectedPreparation.run (bound + extra) (bound + extra) uv caller before =
        ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap))) ∧
      lookupNode caller.checked.native.machine.heap handle = some decoded ∧
      Post formulas solver inventory caller
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
      Packet formulas solver inventory
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata entered ∧
      EnumerationDriver.RenderStable before.core entered.core ∧
      EnumerationDriver.Ready uv entered.core ∧
      entered.core.values[uv]? = some (.unenumerated (some handle) scs) ∧
      entered.core.counter = before.core.counter ∧ entered.core.values = before.core.values ∧
      entered.expandable = before.expandable ∧ entered.waiting = before.waiting ∧
      Available heap result ∧ result.free = [] ∧
      (∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient result term ↔
          InternedGuardedLanguage.meaning holds ambient decoded term) ∧
      ∀ holds ambient residualMeaning assignment,
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap)
          residualMeaning assignment entered.core ↔
        Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core) ∧
        (Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient
          caller.checked.native.machine.heap) residualMeaning assignment before.core →
          InternedGuardedLanguage.meaning holds ambient result (assignment uv))) ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked ∧
      InternedValueMass.value result ≤
        (SourcePruningEnumerationSelectedValueCaller.normalizationProfile profile).mass ) ∧
      (MergedOrdinaryHeight.recursiveBoundary result = true →
        ∃ (opaqueBound childHandle : Nat) (middle after : Cached),
          ((encodeNode result = some childHandle ∧
          lookupNode heap childHandle = some result ∧
          middle.core = allocated (some childHandle) entered.core ∧
          middle.core.values[entered.core.counter]? = some (.unenumerated (some childHandle) []) ∧
          middle.expandable = entered.expandable ∧ middle.waiting = entered.waiting ∧
          (∀ r n p h extra,
            SourcePruningEnumerationChildDispatch.run checkEmpty r n p h (opaqueBound + extra)
              scs result (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered memos.query =
              ((.ok (some [.ok (.hole entered.core.counter, middle.core)]),
                SourcePruningEnumerationSelectedValueCaller.advance caller heap, memos.query,
                entered.core, entered.waiting), some middle)) ∧
          (∀ r n p h extra,
            SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h (opaqueBound + extra)
              uv scs result (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered memos.query =
              some (.complete (.hole entered.core.counter)
                (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos.query after)) ∧
          after.core.counter = entered.core.counter + 1 ∧
          after.core.values[uv]? = some (.enumerated (.hole entered.core.counter)) ∧
          after.core.values[entered.core.counter]? = some (.unenumerated (some childHandle) []) ∧
          after.core.expansionAncestry = [] ∧
          Packet formulas solver inventory
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos metadata after ∧
          ProperState after.core ∧
          Post formulas solver inventory (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos) ∧
          Post formulas solver inventory caller
            (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos ∧
          (∀ (r n p h extra : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint)),
            run checkEmpty (bound + opaqueBound + extra) (bound + opaqueBound + extra)
              r n p h (bound + opaqueBound + extra) uv edgesOf caller before memos.query =
              (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)),
                .inr (some (.complete (.hole before.core.counter)
                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos.query after)))) ∧
          ∀ (ambient : InternedGuardedLanguage.Env Symbol)
            (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol),
            Satisfies (SourcePruningEnumerationNativeLanguage.handles
              (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
              residualMeaning assignment before.core →
            ∃ extended : Nat → Term Symbol,
              (∀ slot < before.core.counter, extended slot = assignment slot) ∧
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
                residualMeaning extended before.core ∧
              Fragments.fill extended (.hole before.core.counter : Fragments.Fragment Symbol) = assignment uv ∧
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient heap)
                residualMeaning extended after.core ) ∧
          ∀ (Output : Type u) (Reason : Type v)
            (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
            (r n p h extra : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint)),
            SourcePruningEnumerationSelectedContinuations.run hook checkEmpty
              (bound + opaqueBound + extra) (bound + opaqueBound + extra)
              r n p h (bound + opaqueBound + extra) uv edgesOf caller before memos.query =
              (([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)),
                some (SourcePruningEnumerationReceiptContinuation.run hook
                  (some (.complete (.hole before.core.counter)
                    (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos.query after))))) := by
  obtain ⟨bound, decoded, result, heap, entered, preparationPacket, opaqueResult⟩ :=
    complete_resources_opaque_models formulas solver inventory caller memos metadata before uv handle scs
      packet ready stored profile fits proper incoming checkEmpty
  refine ⟨bound, decoded, result, heap, entered, preparationPacket, ?_⟩
  intro boundary
  obtain ⟨opaqueBound, childHandle, middle, after, retained⟩ := opaqueResult boundary
  refine ⟨opaqueBound, childHandle, middle, after, retained, ?_⟩
  intro Output Reason hook r n p h extra edgesOf
  rcases preparationPacket with ⟨preparation, _fits, _mass⟩
  rcases preparation with ⟨preparationRun, _lookup, _preparationPost, _enteredPacket, _stable,
    _enteredReady, _enteredStored, counterSame, _valuesSame, flagsSame, waitingSame,
    _available, _closed, _language, _models⟩
  rcases retained with ⟨opaquePacket, _post, _actualDispatch, _originalModels⟩
  rcases opaquePacket with ⟨_encoded, _decoded, _middleCore, _freshStored, _flagsSame, _waitingSame,
    _childRun, opaqueRun, _counter, _capturedStored, _holeStored, _ancestry, _afterPacket,
    _afterProper, _opaquePost⟩
  have framed : EnumerationExpandableIndex.frame entered.core before = entered := by
    cases entered with
    | mk core expandable waiting =>
        simp only [EnumerationExpandableIndex.frame] at *
        congr 1
        · exact flagsSame.symm
        · exact waitingSame.symm
  have preparationAt : SourcePruningEnumerationSelectedPreparation.run
      (bound + opaqueBound + extra) (bound + opaqueBound + extra) uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done result heap)) := by
    simpa only [Nat.add_assoc] using preparationRun (opaqueBound + extra)
  have opaqueAt : SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty r n p h
      (bound + opaqueBound + extra) uv scs result
      (SourcePruningEnumerationSelectedValueCaller.advance caller heap) entered memos.query =
      some (.complete (.hole before.core.counter)
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap) memos.query after) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, counterSame] using
      opaqueRun r n p h (bound + extra)
  have actual := SourcePruningEnumerationSelectedContinuations.opaque_step hook checkEmpty
    (bound + opaqueBound + extra) (bound + opaqueBound + extra)
    r n p h (bound + opaqueBound + extra) uv uv handle scs decoded result heap entered.core
    edgesOf caller before memos.query preparationAt boundary
  simpa only [framed, opaqueAt] using actual

end MicroCFTA.SourcePruningEnumerationSelectedDispatch
