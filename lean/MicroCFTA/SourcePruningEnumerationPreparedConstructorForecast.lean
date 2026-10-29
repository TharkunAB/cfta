import MicroCFTA.SourcePruningEnumerationConstructorCallback
import MicroCFTA.SourcePruningEnumerationRecursiveReservation

namespace MicroCFTA.SourcePruningEnumerationPreparedConstructorForecast
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

/-- An original resource forecast derives the projection and full prepared callback progress. -/
theorem accepted_constructor_callback
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
    (fits : Fits seed.2 caller.checked)
    (inherited : Nat) (inheritedLength : scs.length ≤ inherited)
    (reserved : Reserved bits seed (SourcePruningEnumerationRecursiveReservation.edgeCount seed inherited))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (refuted : ∀ group ∈ metadata.pending, Refutes assignment group)
    (avoids : SourcePruningTemplates.Avoids templates term)
    (encoded : ∀ program, SourcePruningTemplates.ProgramAt term program →
      SourcePruningTemplates.ProgramEncoding program) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      Reserved bits seed (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) ∧
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
  have inheritedModel : ∀ sc ∈ scs, Suspended.Holds assignment term sc := by
    have model := satisfied.1.2 target
    simp only [heap, stored, Option.getD_some, slot, Fragments.slotSatisfies,
      List.forall_mem_map] at model
    intro sc member
    simpa only [parentValue] using model.2 sc member
  obtain ⟨tries, residual, _terms, projected, _valid, _termShape, _children,
    _length, allowed, _ownEqualities, _residualHolds⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry edges depth free edge scs packet.context parentAvailable selected ambient assignment
      term accepted inheritedModel
  obtain ⟨children, own⟩ := SourcePruningEnumerationRecursiveReservation.edge_shape_from_packet
    seed formulas solver inventory caller memos metadata before packet fits known
    parentEntry edges depth free parentAvailable edge selected
  have costBound := SourcePruningEnumerationRecursiveReservation.edge_cost_le seed inherited scs
    before.core.counter edge children own inheritedLength
  have actualCost : SourcePruningEnumerationNativeBranchCompletion.edgeCost scs before.core.counter edge =
      SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries := by
    simp only [SourcePruningEnumerationNativeBranchCompletion.edgeCost, allowed, ↓reduceIte, projected]
  have actualReserved : Reserved bits seed
      (SourcePruningEnumerationSelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [actualCost] using reserved.prefix costBound
  refine ⟨tries, residual, projected, actualReserved, ?_⟩
  exact SourcePruningEnumerationConstructorCallback.accepted_prepared_constructor_callback
    seed formulas solver inventory caller before checkEmpty parentEntry edges depth free edge scs memos
    metadata packet proper target handle ready incoming stored parentAvailable parentClosed selected
    ambient assignment term parentValue satisfied accepted tries residual projected fits actualReserved known
    graph templates refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationPreparedConstructorForecast
