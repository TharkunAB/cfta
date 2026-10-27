import MicroCFTA.SourcePruningEnumerationAcceptedHeadPolicy
import MicroCFTA.SourcePruningEnumerationCallbackRefutation

/-!
# Actual callback continuation after an accepted native head

The head and callback bounds precede all original assignment observers.
The same captured cache supplies the actual callback resource certificate.
Original policy conditions derive non-rejection and the recursive continuation.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeHookResources
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open EnumerationDriver EnumerationCompressionFrame SourcePruningRecordTypes
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationNativeBranchCompletion (Admitted Pending FragmentHistory HeadCacheBounds edgeCost)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume Complete OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "scalar" => SourceCurrentConstrainedCapTargetForecast.scalar
local notation "guardWidth" => SourcePruningEnumerationGuardWidth.width
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "finiteStep" => SourcePruningEnumerationFiniteReservation.step
local notation "massCeil" => SourcePruningEnumerationRecursiveReservation.massCeil
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]


/-- An accepted original head derives non-rejection at its actual resource-bounded callback. -/
theorem head_finite_complete_resources_callback_policy
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : edge ∈ storedEdges) (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ selectedEdge ∈ edgesOf (.node entry rows depth free), selectedEdge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : SourcePruningEnumerationFiniteReservation.HeadReserved bits recursiveFuel seed capturedMass inherited) :
    ∃ (bound : Nat) (receipt : Receipt (bits + 2)) (middleCaller : Caller (bits + 2))
      (saved : Queries) (middleMemos : Memos) (middleInventory : Inventory),
      (((∀ extra, SourcePruningEnumerationCapturedEdge.run checkEmpty
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs edge caller before memos.query = some receipt) ∧
      Post formulas solver middleInventory caller middleCaller middleMemos ∧ middleMemos.query = saved ∧
      Admitted uv receipt ∧ Pending receipt ∧ FragmentHistory before.core receipt ∧
      HeadCacheBounds before scs (scalar seed.2) (guardWidth seed.1) receipt ∧
      Fits (afterHead seed inherited).2 middleCaller.checked ∧
      Heap (fun guard => guard ∈ (afterHead seed inherited).1) middleCaller.checked.native.machine.heap ∧
      ((receipt = .unhandled ∧ arityAllows edge.children.length scs = true ∧
          SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) ∨
        ∃ outcome : HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2),
          advance receipt = some (middleCaller, middleMemos.query) ∧
          (∀ extra, match (generalizing := false) receipt with
            | .complete fragment actual queries after =>
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
                  graph templates stop order (bound + extra) metadata uv fragment actual queries after = outcome
            | _ => outcome = .complete [] middleCaller middleMemos.query) ∧
          OutcomeResources formulas solver caller (finiteStep recursiveFuel seed capturedMass inherited) outcome ∧
          match outcome with
          | .complete _ actual queries =>
              ∃ (next : Inventory) (final : Memos),
                Post formulas solver next caller actual final ∧ final.query = queries ∧
                Packet formulas solver next actual final metadata before ∧
                Fits (finiteStep recursiveFuel seed capturedMass inherited).2 actual.checked ∧
                Heap (fun guard => guard ∈ (finiteStep recursiveFuel seed capturedMass inherited).1)
                  actual.checked.native.machine.heap
          | .stopped _ _ _ => True) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment middleCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core) ∧
      ∀ (ambient : InternedGuardedLanguage.Env Symbol)
        (assignment : Nat → Language.Term Symbol),
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient caller.checked.native.machine.heap)
          (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
          assignment before.core →
        InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
          ambient edge (assignment uv) →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.Avoids templates (assignment uv) →
        (∀ program, SourcePruningTemplates.ProgramAt (assignment uv) program →
          SourcePruningTemplates.ProgramEncoding program) →
        ∃ (extended : Nat → Language.Term Symbol) (fragment : Fragments.Fragment Symbol) (afterCache : Cached),
          (∀ old < before.core.counter, extended old = assignment old) ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient caller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended before.core ∧
          receipt = .complete fragment middleCaller saved afterCache ∧
          Fragments.fill extended fragment = assignment uv ∧
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient middleCaller.checked.native.machine.heap)
            (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
            extended afterCache.core ∧
          Fragments.fill extended fragment = extended uv ∧
          (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
            (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) extended group) ∧
          SourcePruningTemplates.Avoids templates (Fragments.fill extended fragment) ∧
          ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill extended fragment) program →
            SourcePruningTemplates.ProgramEncoding program) ∧
      match (generalizing := false) receipt with
      | .complete fragment actual queries afterCache =>
          ∃ (callbackFuel : Nat) (result : Bool × SourcePruningRecordTypes.Metadata Typing)
            (callbackAfter : EnumerationState.State Symbol Constraint),
            (((Packet formulas solver middleInventory actual middleMemos result.2 (EnumerationExpandableIndex.frame callbackAfter afterCache) ∧
      RenderStable afterCache.core callbackAfter ∧ Frame afterCache.core callbackAfter ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      ∀ extra,
        Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)) afterCache.core result callbackAfter ∧
        ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment) afterCache.core) =
          [.ok (result, callbackAfter)] ∧
        (∀ recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2),
          continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment actual middleMemos.query afterCache =
            if result.1 then .complete [] actual middleMemos.query
            else recur result.2 actual middleMemos.query (EnumerationExpandableIndex.frame callbackAfter afterCache)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame callbackAfter afterCache))) ∧
        (result.1 = false → ∀ selected,
          SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame callbackAfter afterCache) = some (.expand selected) →
          SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
            stop order result.2 formulas solver middleInventory (callbackFuel + extra) selected actual
            (EnumerationExpandableIndex.frame callbackAfter afterCache) middleMemos
            (SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order result.2
              (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra)
              selected actual (EnumerationExpandableIndex.frame callbackAfter afterCache) middleMemos.query))) ∧
      (∀ extra, result.1 = false → ∀ selected,
        SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame callbackAfter afterCache) = some (.expand selected) →
        let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
          stop order result.2 (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra)
          (callbackFuel + extra) (callbackFuel + extra) (callbackFuel + extra) selected actual
          (EnumerationExpandableIndex.frame callbackAfter afterCache) middleMemos.query
        SourcePruningEnumerationSelectedStep.Resources (afterHead seed inherited).2 (fun guard => guard ∈ (afterHead seed inherited).1) actual observed ∧
        match observed with
        | .parked _ (some reachedCache) _ =>
            Packet formulas solver middleInventory actual middleMemos result.2 reachedCache
        | .narrowed _ _ reached queries _ (some reachedCache) _ _ =>
            ∃ final, Post formulas solver middleInventory actual reached final ∧ final.query = queries ∧
              Packet formulas solver middleInventory reached final result.2 reachedCache
        | _ => True)) ∧
      ∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
        (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment afterCache.core →
        Fragments.fill assignment fragment = assignment uv →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
        (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
          SourcePruningTemplates.ProgramEncoding program) →
          result.1 = false ∧
          ∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
            (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧

          ∀ (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Language.Term Symbol),
            Satisfies
              (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                ambient caller.checked.native.machine.heap)
              (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
              assignment before.core →
            InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver)
              ambient edge (assignment uv) →
            (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
              (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
            SourcePruningTemplates.Avoids templates (assignment uv) →
            (∀ program, SourcePruningTemplates.ProgramAt (assignment uv) program →
              SourcePruningTemplates.ProgramEncoding program) →
            ∃ extended : Nat → Language.Term Symbol,
              (∀ old < before.core.counter, extended old = assignment old) ∧
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient caller.checked.native.machine.heap)
                (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                extended before.core ∧
              Fragments.fill extended fragment = assignment uv ∧
              Satisfies
                (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
                  ambient actual.checked.native.machine.heap)
                (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
                extended afterCache.core ∧
              result.1 = false ∧
              (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
                (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) extended group) ∧
              ∀ extra,
                continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (bound + callbackFuel + extra) recursiveFuel)
                  graph templates stop order (bound + callbackFuel + extra) metadata uv fragment actual queries afterCache =
                resume holeKey fits admits graph templates checkEmpty edgesOf stop order
                  (bound + callbackFuel + extra) recursiveFuel result.2 actual queries
                  (EnumerationExpandableIndex.frame callbackAfter afterCache)
                  (SourcePruningEnumerationRestart.decision stop order result.2
                    (EnumerationExpandableIndex.frame callbackAfter afterCache))
      | _ => True := by
  obtain ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, oldHead, policy⟩ :=
    head_finite_complete_resources_policy holeKey fits admits graph templates checkEmpty edgesOf stop order
      metadata recursiveFuel seed formulas solver recursive inventory caller memos before uv handle scs parentEntry
      storedEdges depth free edge packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  refine ⟨bound, receipt, middleCaller, saved, middleMemos, middleInventory, ⟨oldHead, policy⟩, ?_⟩
  cases receipt with
  | unhandled | rejected _ _ _ | stopped _ _ _ => trivial
  | complete fragment actual queries afterCache =>
      obtain ⟨_running, post, _querySame, admitted, headPending, history, _cacheBounds, headFits,
        headKnown, shape, _accepting⟩ := oldHead
      have endpoint : actual = middleCaller ∧ queries = middleMemos.query := by
        rcases shape with unsupported | ⟨_outcome, advanced, _callback, _resources, _end⟩
        · cases unsupported.1
        · exact Prod.mk.inj (Option.some.inj advanced)
      rcases endpoint with ⟨rfl, querySame⟩
      obtain ⟨level, frontier, ordered⟩ := packet.ordered
      have callbackPacket := SourcePruningEnumerationRecursive.receipt_packet before.core uv fragment afterCache
        level frontier post.context admitted history headPending ordered packet.bounded
      obtain ⟨callbackFuel, result, callbackAfter, callbackRetained, callbackSemantics⟩ :=
        SourcePruningEnumerationRecursive.callback_prefix_complete_resources_refutes formulas solver middleInventory
          graph templates metadata uv fragment middleCaller middleMemos afterCache
          holeKey fits admits checkEmpty edgesOf stop order callbackPacket admitted.2.2.1
          (afterHead seed inherited).2 (fun guard => guard ∈ (afterHead seed inherited).1) headFits headKnown
      refine ⟨callbackFuel, result, callbackAfter, ⟨callbackRetained, callbackSemantics⟩, ?_⟩
      intro ambient assignment satisfied accepted refuted avoids encoded
      obtain ⟨extended, produced, producedCache, agree, beforeModel, completed, filled, afterModel,
        self, pendingRefutes, currentAvoids, currentEncoding⟩ :=
        policy ambient assignment satisfied accepted refuted avoids encoded
      cases completed
      have semantic := callbackSemantics
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient middleCaller.checked.native.machine.heap)
        (fun guard term => SourceEqualityPCSGuard.holds formulas solver guard term = true)
        extended afterModel self pendingRefutes currentAvoids currentEncoding
      refine ⟨extended, agree, beforeModel, filled, afterModel, semantic.1, semantic.2, ?_⟩
      intro extra
      have actualCallback := (callbackRetained.1.2.2.2.2.2.2 (bound + extra)).2.2.1
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + callbackFuel + extra) recursiveFuel)
      have common : callbackFuel + (bound + extra) = bound + callbackFuel + extra := by omega
      rw [common, semantic.1] at actualCallback
      simpa only [querySame, Bool.false_eq_true, ↓reduceIte] using actualCallback

end MicroCFTA.SourcePruningEnumerationNativeHookResources
