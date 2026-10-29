import MicroCFTA.SourcePruningEnumerationConstructorIteration
import MicroCFTA.SourcePruningEnumerationRecursiveCallbackLanguage
import MicroCFTA.SourcePruningEnumerationPolicyOrigins
import MicroCFTA.SourcePruningRecordTypesRefutation
import MicroCFTA.SourcePruningEnumerationStorageCallbackProgress
import MicroCFTA.SourcePruningEnumerationCapturedEdgeResources
import MicroCFTA.SourcePruningEnumerationSelectedEdgeEndpointProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationNativeProgress

namespace MicroCFTA.SourcePruningEnumerationConstructorCallback
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationProgress
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourcePruningEnumerationRecursive (Packet continueWith)
open SourcePruningRecordTypes (recordTypes updatedTypes)
open EnumerationDriver (RenderStable)
open EnumerationCompressionFrame (Frame)
open SourcePruningEnumerationIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (SourcePruningEnumerationRecursive.Output (bits + 2) Typing)
  (SourcePruningEnumerationRecursive.Failure (bits + 2) Typing) (bits + 2)
local notation "Refutes" => @SourcePruningResume.Refutes Symbol
  (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq)

/-- A prepared constructor preserves the captured target and the complete progress result. -/
theorem accepted_prepared_constructor_callback
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (memos : Memos)
    (metadata : Metadata Typing)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (proper : ProperState before.core) (target handle : Nat)
    (ready : EnumerationDriver.Ready target before.core)
    (incoming : EnumerationReferences.IncomingAvoid target before.core)
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
    (selected : edge ∈ edges)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term : Term Symbol)
    (parentValue : assignment target = term)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group)
    (avoids : SourcePruningTemplates.Avoids templates term)
    (encoded : ∀ program, SourcePruningTemplates.ProgramAt term program →
      SourcePruningTemplates.ProgramEncoding program) :
    ∃ (r n p h k : Nat) (fragment : Fragment) (afterCaller : Caller (bits + 2))
      (recorded finalized : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (extended : Nat → Term Symbol),
      (
      (
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          scs edge caller before memos.query = .complete fragment afterCaller savedQueries recorded) ∧
      (∀ ek, SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap (k + ek)
        target fragment recorded = some finalized) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended before.core ∧
      Fragments.fill extended fragment = term ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended recorded.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended finalized.core ∧
      Safe finalized.core ∧ EnumerationValidity.Canonical finalized.core ∧
      Roots finalized.core.representatives afterRoots ∧ StorageValid finalized.core ∧
      PendingRealized afterCaller.checked.native.machine.heap finalized.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots finalized.core.values finalized.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((finalized.core.values[slot]?).getD .eliminated) = some (finalized.expandable slot)) ∧
      Fits (advance seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).2
        afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ∧
      EnumerationStorageProgress.pendingSize finalized.core extended + 1 ≤
        EnumerationStorageProgress.pendingSize before.core assignment
      ) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          target scs edge caller before memos.query =
          some (.complete fragment afterCaller savedQueries finalized)) ∧
      SourcePruningEnumerationRecursive.Packet formulas solver next afterCaller final metadata finalized ∧
      ProperState finalized.core ∧
      SourcePruningEnumerationNativeBranchCompletion.Admitted target
        (.complete fragment afterCaller savedQueries finalized) ∧
      SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core
        (.complete fragment afterCaller savedQueries finalized) ∧
      ∀ (uv : Nat) (node : Option Nat) (bucket : List Suspended),
        finalized.core.values[uv]? = some (UVarValue.unenumerated node bucket) →
        InputsPending finalized.core bucket ∧ ∀ sc ∈ bucket, sc.var < finalized.core.counter
      ) ∧
      ∃ (callbackFuel : Nat) (callback : Bool × Metadata Typing)
        (callbackCore : EnumerationState.State Symbol Constraint),
        (
        Packet formulas solver next afterCaller final callback.2 (EnumerationExpandableIndex.frame callbackCore finalized) ∧
        RenderStable finalized.core callbackCore ∧ Frame finalized.core callbackCore ∧
        callback.2.types = updatedTypes metadata target (.inl fragment) ∧
        callback.2.openHoles = metadata.openHoles ∧ callback.2.typing = metadata.typing ∧
        (∀ extra,
          Success (recordTypes graph templates (callbackFuel + extra) metadata target (.inl fragment)) finalized.core callback callbackCore ∧
          ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata target (.inl fragment) finalized.core) =
            [.ok (callback, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
            continueWith recur graph templates stop order (callbackFuel + extra) metadata target fragment afterCaller final.query finalized =
              if callback.1 then .complete [] afterCaller final.query
              else recur callback.2 afterCaller final.query (EnumerationExpandableIndex.frame callbackCore finalized)
                (SourcePruningEnumerationRestart.decision stop order callback.2
                  (EnumerationExpandableIndex.frame callbackCore finalized))) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (residualMeaning : Constraint → Language.Term Symbol → Prop)
          (assignment : Nat → Language.Term Symbol),
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment
            (EnumerationExpandableIndex.frame callbackCore finalized).core ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment finalized.core
        ) ∧
        callback.1 = false ∧
        (∀ group ∈ callback.2.pending, Refutes extended group) ∧
        ProperState (EnumerationExpandableIndex.frame callbackCore finalized).core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
          extended (EnumerationExpandableIndex.frame callbackCore finalized).core ∧
        EnumerationStorageProgress.pendingSize (EnumerationExpandableIndex.frame callbackCore finalized).core extended + 1 ≤
          EnumerationStorageProgress.pendingSize before.core assignment ∧
        (∀ (nextStop : Option (Metadata Typing → Nat → Bool))
          (nextOrder : Metadata Typing → List Nat → Option Nat),
          SourcePruningEnumerationRestart.decision nextStop nextOrder callback.2
            (EnumerationExpandableIndex.frame callbackCore finalized) ≠ some .stuck) ∧
        ∃ work, ∀ extra,
          SourcePruningEnumerationCapturedEdge.run checkEmpty (work + extra) (work + extra)
            (work + extra) (work + extra) (work + extra) target scs edge caller before memos.query =
            some (.complete fragment afterCaller savedQueries finalized) ∧
          ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result)
            (nextStop : Option (Metadata Typing → Nat → Bool))
            (nextOrder : Metadata Typing → List Nat → Option Nat),
            continueWith recur graph templates nextStop nextOrder (work + extra)
              metadata target fragment afterCaller savedQueries finalized =
              recur callback.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore finalized)
                (SourcePruningEnumerationRestart.decision nextStop nextOrder callback.2
                  (EnumerationExpandableIndex.frame callbackCore finalized)) := by
  obtain ⟨r, n, p, h, k, fragment, afterCaller, recorded, finalized, savedQueries, final, next,
    afterRoots, extended, original⟩ :=
    SourcePruningEnumerationConstructorIteration.accepted_prepared_constructor_packet seed formulas solver inventory caller
      before checkEmpty parentEntry edges depth free edge scs memos metadata packet proper target handle
      ready incoming stored parentAvailable parentClosed selected ambient assignment term parentValue satisfied accepted tries residual
      projected fits reserved known
  have retainedOriginal := original
  rcases original with ⟨constructor, capturedRun, returned, finalProper, admitted, _history, _pendingInputs⟩
  rcases constructor with ⟨_selectedRun, _finalizedRun, _post, querySame, agree, _originalModel,
    filled, _recordedModel, finalModel, _finalSafe, _finalCanonical, _finalPaths, _finalStorage,
    _finalRealized, _finalCounts, _finalFlags, _finalFits, _finalKnown, decrease⟩
  obtain ⟨callbackFuel, callback, callbackCore, callbackPacket⟩ :=
    SourcePruningEnumerationRecursive.callback_complete_semantics formulas solver next graph templates
      metadata target fragment afterCaller final finalized returned admitted.2.2.1
  have retainedCallback := callbackPacket
  rcases callbackPacket with ⟨callbackReturned, _stable, frame, _types, _holes, _typing, callbackRun, meaning⟩
  have inside : target < before.core.counter := by
    rw [packet.safe.1.aligned]
    exact (List.getElem?_eq_some_iff.mp stored).1
  have filledSelf : Fragments.fill extended fragment = extended target :=
    filled.trans ((agree target inside).trans parentValue).symm
  have extendedRefuted := SourcePruningRecordTypes.pending_refutes_extension
    before.core.counter assignment extended metadata packet.bounded agree refuted
  have callbackRefutation := SourcePruningRecordTypes.recordTypes_inl_refutes graph
    (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
      ambient afterCaller.checked.native.machine.heap)
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
    extended templates (callbackFuel + 0) target metadata fragment finalized.core callbackCore callback
    returned.safe.1.total finalModel filledSelf extendedRefuted
    (by simpa only [filled] using avoids) (by simpa only [filled] using encoded) (callbackRun 0).1
  have callbackProper : ProperState (EnumerationExpandableIndex.frame callbackCore finalized).core := by
    change ProperState callbackCore
    simpa only [ProperState, frame.values] using finalProper
  have callbackModel := (meaning ambient
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true) extended).mpr finalModel
  have callbackDecrease :
      EnumerationStorageProgress.pendingSize (EnumerationExpandableIndex.frame callbackCore finalized).core extended + 1 ≤
        EnumerationStorageProgress.pendingSize before.core assignment := by
    change EnumerationStorageProgress.pendingSize callbackCore extended + 1 ≤ _
    rw [EnumerationStorageProgress.frame_pendingSize finalized.core callbackCore extended frame]
    exact decrease
  have callbackContinue : ∀ extra
      (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result)
      (nextStop : Option (Metadata Typing → Nat → Bool))
      (nextOrder : Metadata Typing → List Nat → Option Nat),
      continueWith recur graph templates nextStop nextOrder (callbackFuel + extra)
        metadata target fragment afterCaller savedQueries finalized =
        recur callback.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore finalized)
          (SourcePruningEnumerationRestart.decision nextStop nextOrder callback.2
            (EnumerationExpandableIndex.frame callbackCore finalized)) := by
    intro extra recur nextStop nextOrder
    have actual := (callbackRun extra).2.2 recur nextStop nextOrder
    simpa only [callbackRefutation.1, Bool.false_eq_true, ↓reduceIte, querySame] using actual
  refine ⟨r, n, p, h, k, fragment, afterCaller, recorded, finalized, savedQueries, final, next,
    afterRoots, extended, retainedOriginal, callbackFuel, callback, callbackCore,
    retainedCallback, callbackRefutation.1, callbackRefutation.2, callbackProper, callbackModel,
    callbackDecrease, ?_, ?_⟩
  · intro nextStop nextOrder
    exact SourcePruningEnumerationRestart.not_stuck_of_proper formulas solver nextStop nextOrder callback.2
      afterCaller (EnumerationExpandableIndex.frame callbackCore finalized) callbackReturned.valid
      callbackReturned.safe callbackProper ambient
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true) extended callbackModel
  · let work := r + n + p + h + k + callbackFuel
    refine ⟨work, ?_⟩
    intro extra
    have sameR : r + (work + extra - r) = work + extra := by dsimp only [work]; omega
    have sameN : n + (work + extra - n) = work + extra := by dsimp only [work]; omega
    have sameK : k + (work + extra - k) = work + extra := by dsimp only [work]; omega
    refine ⟨?_, ?_⟩
    · simpa only [sameR, sameN, sameK] using capturedRun (work + extra - r) (work + extra - n)
        (work + extra) (work + extra) (work + extra - k) (by dsimp only [work]; omega)
        (by dsimp only [work]; omega)
    · intro recur nextStop nextOrder
      have sameCallback : callbackFuel + (work + extra - callbackFuel) = work + extra := by
        dsimp only [work]
        omega
      simpa only [sameCallback] using callbackContinue (work + extra - callbackFuel) recur nextStop nextOrder

/-- Original constructor and template admissions derive the actual non-rejecting callback with strict progress. -/
theorem accepted_constructor_callback
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (memos : Memos)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver inventory caller memos metadata before)
    (proper : ProperState before.core) (target handle : Nat)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand target))
    (stored : before.core.values[target]? = some (.unenumerated (some handle) scs))
    (parentLookup : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry edges depth free))
    (selected : edge ∈ edges)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term : Term Symbol)
    (parentValue : assignment target = term)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
      assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group)
    (avoids : SourcePruningTemplates.Avoids templates term)
    (encoded : ∀ program, SourcePruningTemplates.ProgramAt term program →
      SourcePruningTemplates.ProgramEncoding program) :
    ∃ (r n p h k : Nat) (fragment : Fragment) (afterCaller : Caller (bits + 2))
      (recorded finalized : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (extended : Nat → Term Symbol),
      (
      (
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationSelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          scs edge caller before memos.query = .complete fragment afterCaller savedQueries recorded) ∧
      (∀ ek, SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap (k + ek)
        target fragment recorded = some finalized) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended before.core ∧
      Fragments.fill extended fragment = term ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended recorded.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        extended finalized.core ∧
      Safe finalized.core ∧ EnumerationValidity.Canonical finalized.core ∧
      Roots finalized.core.representatives afterRoots ∧ StorageValid finalized.core ∧
      PendingRealized afterCaller.checked.native.machine.heap finalized.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots finalized.core.values finalized.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((finalized.core.values[slot]?).getD .eliminated) = some (finalized.expandable slot)) ∧
      Fits (advance seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).2
        afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ∧
      EnumerationStorageProgress.pendingSize finalized.core extended + 1 ≤
        EnumerationStorageProgress.pendingSize before.core assignment
      ) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SourcePruningEnumerationCapturedEdge.run checkEmpty (r + er) (n + en) P H (k + ek)
          target scs edge caller before memos.query =
          some (.complete fragment afterCaller savedQueries finalized)) ∧
      SourcePruningEnumerationRecursive.Packet formulas solver next afterCaller final metadata finalized ∧
      ProperState finalized.core ∧
      SourcePruningEnumerationNativeBranchCompletion.Admitted target
        (.complete fragment afterCaller savedQueries finalized) ∧
      SourcePruningEnumerationNativeBranchCompletion.FragmentHistory before.core
        (.complete fragment afterCaller savedQueries finalized) ∧
      ∀ (uv : Nat) (node : Option Nat) (bucket : List Suspended),
        finalized.core.values[uv]? = some (UVarValue.unenumerated node bucket) →
        InputsPending finalized.core bucket ∧ ∀ sc ∈ bucket, sc.var < finalized.core.counter
      ) ∧
      ∃ (callbackFuel : Nat) (callback : Bool × Metadata Typing)
        (callbackCore : EnumerationState.State Symbol Constraint),
        (
        Packet formulas solver next afterCaller final callback.2 (EnumerationExpandableIndex.frame callbackCore finalized) ∧
        RenderStable finalized.core callbackCore ∧ Frame finalized.core callbackCore ∧
        callback.2.types = updatedTypes metadata target (.inl fragment) ∧
        callback.2.openHoles = metadata.openHoles ∧ callback.2.typing = metadata.typing ∧
        (∀ extra,
          Success (recordTypes graph templates (callbackFuel + extra) metadata target (.inl fragment)) finalized.core callback callbackCore ∧
          ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata target (.inl fragment) finalized.core) =
            [.ok (callback, callbackCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
            continueWith recur graph templates stop order (callbackFuel + extra) metadata target fragment afterCaller final.query finalized =
              if callback.1 then .complete [] afterCaller final.query
              else recur callback.2 afterCaller final.query (EnumerationExpandableIndex.frame callbackCore finalized)
                (SourcePruningEnumerationRestart.decision stop order callback.2
                  (EnumerationExpandableIndex.frame callbackCore finalized))) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (residualMeaning : Constraint → Language.Term Symbol → Prop)
          (assignment : Nat → Language.Term Symbol),
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment
            (EnumerationExpandableIndex.frame callbackCore finalized).core ↔
          Satisfies
            (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
              ambient afterCaller.checked.native.machine.heap) residualMeaning assignment finalized.core
        ) ∧
        callback.1 = false ∧
        (∀ group ∈ callback.2.pending, Refutes extended group) ∧
        ProperState (EnumerationExpandableIndex.frame callbackCore finalized).core ∧
        Satisfies
          (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
            ambient afterCaller.checked.native.machine.heap)
          (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
          extended (EnumerationExpandableIndex.frame callbackCore finalized).core ∧
        EnumerationStorageProgress.pendingSize (EnumerationExpandableIndex.frame callbackCore finalized).core extended + 1 ≤
          EnumerationStorageProgress.pendingSize before.core assignment ∧
        (∀ (nextStop : Option (Metadata Typing → Nat → Bool))
          (nextOrder : Metadata Typing → List Nat → Option Nat),
          SourcePruningEnumerationRestart.decision nextStop nextOrder callback.2
            (EnumerationExpandableIndex.frame callbackCore finalized) ≠ some .stuck) ∧
        ∃ work, ∀ extra,
          SourcePruningEnumerationCapturedEdge.run checkEmpty (work + extra) (work + extra)
            (work + extra) (work + extra) (work + extra) target scs edge caller before memos.query =
            some (.complete fragment afterCaller savedQueries finalized) ∧
          ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result)
            (nextStop : Option (Metadata Typing → Nat → Bool))
            (nextOrder : Metadata Typing → List Nat → Option Nat),
            continueWith recur graph templates nextStop nextOrder (work + extra)
              metadata target fragment afterCaller savedQueries finalized =
              recur callback.2 afterCaller savedQueries (EnumerationExpandableIndex.frame callbackCore finalized)
                (SourcePruningEnumerationRestart.decision nextStop nextOrder callback.2
                  (EnumerationExpandableIndex.frame callbackCore finalized)) := by
  obtain ⟨ready, incoming, _native⟩ := SourcePruningEnumerationRestart.selected
    stop order metadata caller before target packet.valid packet.safe chosen
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  obtain ⟨actualParent, parentFound, parentKnown, parentIsClosed⟩ := realized target handle scs stored
  have parentSame : actualParent = .node parentEntry edges depth free :=
    Option.some.inj (parentFound.symm.trans parentLookup)
  have parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free) := by
    simpa only [parentSame] using parentKnown
  have parentClosed : free = [] := by
    simpa only [parentSame, Value.free] using parentIsClosed
  exact accepted_prepared_constructor_callback seed formulas solver inventory caller before checkEmpty
    parentEntry edges depth free edge scs memos metadata packet proper target handle ready incoming stored
    parentAvailable parentClosed selected ambient assignment term parentValue satisfied accepted tries residual
    projected fits reserved known graph templates refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationConstructorCallback
