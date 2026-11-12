import MicroCFTA.SourcePruningEnumerationSharedEagerChildren
import MicroCFTA.SourcePruningEnumerationSharedSelectedEdgeModels
import MicroCFTA.SourcePruningEnumerationSharedNativeBranchResources
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.EnumerationStratifiedTransport

/-!
# Actual eager frontier resources and a compatible model

Every staged child takes the existing fallback dispatch.
One selected-edge producer supplies the complete receipt and model.
The eager callbacks retain that same receipt and native endpoint.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerFrontierResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation SourcePruningEnumerationOrigins
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed Reserved advance)
open SourcePruningEnumerationSharedNativeBranchCompletion (edgeCost)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild ordinaryNonterminal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
universe u v
variable {Typing : Type} {width bits : Nat} {Output : Type u} {Reason : Type v}
local notation "Fold" => NativeContinuations.Result Output Reason
local notation "Visitor" => fun (w : Nat) => List Suspended → Node → Caller w → Cached → Queries →
  (Fragment → Caller w → Queries → Cached → Fold w) →
  (Observation w → Option Cached → Fold w) → Fold w

private theorem children_congr (left right : Visitor width) (inputs : List (Node × List Suspended)) :
    (∀ child bucket, (child, bucket) ∈ inputs → ∀ caller before queries done stopped,
      left bucket child caller before queries done stopped = right bucket child caller before queries done stopped) →
    ∀ done stopped caller before queries,
      visitChildren left done stopped inputs caller before queries =
        visitChildren right done stopped inputs caller before queries := by
  induction inputs with
  | nil => intro _ _ _ _ _ _; rfl
  | cons input rest ih =>
      rcases input with ⟨child, bucket⟩
      intro same done stopped caller before queries
      simp only [visitChildren]
      rw [same child bucket (by simp)]
      apply congrArg (fun yes => right bucket child caller before queries yes
        (fun observation candidate => stopped [] observation candidate))
      funext fragment reached saved after
      exact ih (fun value retained member => same value retained (List.mem_cons_of_mem _ member))
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) reached after saved

private theorem selected_congr (left right : Visitor width) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (same : ∀ child bucket, (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
      ∀ current cache memos done stopped,
        left bucket child current cache memos done stopped = right bucket child current cache memos done stopped)
    (consume : Receipt width → Fold width) :
    visitSelected left consume scs edge caller before queries = visitSelected right consume scs edge caller before queries := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp only [visitSelected, prepared]
  | some results =>
      cases results with
      | nil => simp only [visitSelected, prepared]
      | cons first rest =>
          cases rest with
          | cons second rest => simp only [visitSelected, prepared]
          | nil =>
              rcases first with ⟨⟨symbol, staged, savedResidual⟩, middle⟩
              have shape := SourcePruningEnumerationCachedOwn.prepare_inputs caller.checked.native.machine.heap
                scs edge before middle tries residual (symbol, staged, savedResidual) projected prepared
              simp only [Prod.mk.injEq] at shape
              obtain ⟨_symbolSame, stagedSame, _residualSame⟩ := shape
              have inputsSame : staged.map (fun input => (input.1, input.2.1)) =
                  SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
                rw [stagedSame, List.map_map]
                exact List.map_id _
              simp only [visitSelected, prepared]
              exact children_congr left right _
                (fun value retained member => same value retained (by simpa only [inputsSame] using member))
                _ _ caller middle queries

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A current fallback frontier retains the actual eager receipt, full resources and model. -/
theorem visitSelected_frontier_models_packet
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (scs : List Suspended) (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry rows depth free))
    (parentClosed : free = []) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (frontier : ∀ tries residual,
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
      ∀ child bucket, (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
        ordinaryNonterminal bucket child = false)
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (edgeCost scs before.core.counter edge))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol) (term whole : Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) assignment before.core)
    (accepted : InternedGuardedLanguage.edgeMeaning
      (SourceEqualityPCSGuard.holds formulas solver) ambient edge term)
    (inherited : ∀ sc ∈ scs, Suspended.Holds assignment term sc)
    (old : AssignmentOrigins whole before.core.counter assignment) (origin : Origin whole term) :
    ∃ (tries : List EqualityTrie.Trie) (residual : Option Constraint) (r n p h k : Nat)
      (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (fragment : Fragment) (extended : Nat → Term Symbol),
      SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      arityAllows edge.children.length scs = true ∧
      edgeCost scs before.core.counter edge = SelectedEdge.cost edge scs before.core.counter tries ∧
      (∀ er en P H ek, p ≤ P → h ≤ H →
        SelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
          .complete fragment afterCaller savedQueries after) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧ InputsPending after.core scs ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationReferences.IncomingAvoid held before.core →
          EnumerationReferences.IncomingAvoid held after.core) ∧
      Safe after.core ∧ FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → FragmentAvoid after.core.representatives held fragment) ∧
      Fits (advance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (edgeCost scs before.core.counter edge)).1)
        afterCaller.checked.native.machine.heap ∧
      (∀ uv < before.core.counter, extended uv = assignment uv) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended before.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true) extended after.core ∧
      Fragments.fill extended fragment = term ∧ AssignmentOrigins whole after.core.counter extended ∧
      (∀ sc ∈ scs, Suspended.Holds extended term sc) ∧
      Packet formulas solver next afterCaller final metadata after ∧
      (∀ level bound, EnumerationOrder.Stratified before.core level bound →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel bound) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H → ∀ consume : Receipt (bits + 2) → Fold (bits + 2),
        visitSelected (eagerChild checkEmpty (r + er) (n + en) P H (k + ek) edgesOf)
          consume scs edge caller before memos.query = consume (.complete fragment afterCaller savedQueries after)) ∧
      (∀ er en P H ek, p ≤ P → h ≤ H → ∀ ceiling (consume : Receipt (bits + 2) → Fold (bits + 2)),
        visitSelected (fun bucket child current cache queries yes no =>
          if _lower : MergedOrdinaryHeight.height child < ceiling then
            eagerChild checkEmpty (r + er) (n + en) P H (k + ek) edgesOf bucket child current cache queries yes no
          else shallowVisit checkEmpty (r + er) (n + en) P H (k + ek) bucket child current cache queries yes no)
          consume scs edge caller before memos.query = consume (.complete fragment afterCaller savedQueries after)) := by
  obtain ⟨roots, paths, _oldStorage, oldRealized, oldCounts, oldFlags⟩ := packet.valid
  obtain ⟨tries, residual, _terms, projected, _valid, _shape, _children,
    _length, allowed, _equalities, _residualHeld⟩ :=
    SourcePruningEnumerationSelectedEdgeAdmission.selected_admission formulas solver inventory caller memos
      parentEntry rows depth free edge scs packet.context parentAvailable selected ambient assignment term accepted inherited
  have costSame : edgeCost scs before.core.counter edge = SelectedEdge.cost edge scs before.core.counter tries := by
    simp only [edgeCost, allowed, ↓reduceIte, projected]
  have actualReserved : Reserved bits seed (SelectedEdge.cost edge scs before.core.counter tries) := by
    simpa only [costSame] using reserved
  obtain ⟨r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    fragment, extended, running, post, query, growth, afterPaths, storage, realized, counts, flags,
    enumOrigin, afterInputs, protects, pendingPreserved, incomingPreserved, afterSafe,
    fragmentBound, fragmentPending, fragmentAvoid, returnedFits, returnedHeap, agree,
    beforeModel, afterModel, filled, origins, inheritedAfter⟩ :=
    SelectedEdge.complete_models_resources seed formulas solver inventory caller before checkEmpty
      parentEntry rows depth free edge scs roots memos packet.context parentAvailable parentClosed selected
      packet.safe oldRealized paths oldCounts oldFlags bounded pending tries residual projected fits
      actualReserved known ambient assignment term whole satisfied accepted inherited old origin
  have protectsEnumerated (held : Nat) (storedFragment : Fragment)
      (stored : before.core.values[held]? = some (.enumerated storedFragment)) :
      EnumerationDriver.Protected held before.core after.core := by
    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
    exact protects held inside root (pending held storedFragment stored)
  have ordered (level : Nat → Nat) (bound : Nat)
      (oldOrder : EnumerationOrder.Stratified before.core level bound) :
      ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel bound :=
    EnumerationOrder.stratified_preserved before.core after.core afterSafe level bound
      oldOrder enumOrigin protectsEnumerated
  have afterPacket : Packet formulas solver next afterCaller final metadata after := by
    refine ⟨post.context, afterSafe, pendingPreserved packet.pending,
      ⟨afterRoots, afterPaths, storage, realized, counts, flags⟩, ?_, ?_⟩
    · obtain ⟨level, bound, oldOrder⟩ := packet.ordered
      obtain ⟨nextLevel, nextOrder⟩ := ordered level bound oldOrder
      exact ⟨nextLevel, bound, nextOrder⟩
    · intro group member entry listed
      exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
  have finalFits : Fits (advance seed (edgeCost scs before.core.counter edge)).2 afterCaller.checked := by
    simpa only [costSame] using returnedFits
  have finalHeap : Heap (fun guard => guard ∈ (advance seed (edgeCost scs before.core.counter edge)).1)
      afterCaller.checked.native.machine.heap := by
    simpa only [costSame] using returnedHeap
  refine ⟨tries, residual, r, n, p, h, k, afterCaller, after, savedQueries, final, next, afterRoots,
    fragment, extended, projected, allowed, costSame, running, post, query, growth, afterPaths,
    storage, realized, counts, flags, enumOrigin, afterInputs, protects, pendingPreserved,
    incomingPreserved, afterSafe, fragmentBound, fragmentPending, fragmentAvoid, finalFits,
    finalHeap, agree, beforeModel, afterModel, filled, origins, inheritedAfter, afterPacket, ordered, ?_, ?_⟩
  · intro er en P H ek largeP largeH consume
    calc
      _ = visitSelected (shallowVisit checkEmpty (r + er) (n + en) P H (k + ek))
          consume scs edge caller before memos.query :=
        selected_congr _ _ scs edge caller before memos.query tries residual projected
          (fun child bucket member current cache queries done stopped =>
            SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty (r + er) (n + en) P H (k + ek)
              edgesOf bucket child current cache queries done stopped (frontier tries residual projected child bucket member)) consume
      _ = consume (SelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query) :=
        SourcePruningEnumerationSharedChildVisitors.visitSelected_shallow checkEmpty (r + er) (n + en) P H (k + ek)
          consume scs edge caller before memos.query
      _ = _ := by rw [running er en P H ek largeP largeH]
  · intro er en P H ek largeP largeH ceiling consume
    calc
      _ = visitSelected (shallowVisit checkEmpty (r + er) (n + en) P H (k + ek))
          consume scs edge caller before memos.query := by
        apply selected_congr _ _ scs edge caller before memos.query tries residual projected ?_ consume
        intro child bucket member current cache queries done stopped
        split
        · exact SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty (r + er) (n + en) P H (k + ek)
            edgesOf bucket child current cache queries done stopped (frontier tries residual projected child bucket member)
        · rfl
      _ = consume (SelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query) :=
        SourcePruningEnumerationSharedChildVisitors.visitSelected_shallow checkEmpty (r + er) (n + en) P H (k + ek)
          consume scs edge caller before memos.query
      _ = _ := by rw [running er en P H ek largeP largeH]

end MicroCFTA.SourcePruningEnumerationSharedEagerFrontierResources
