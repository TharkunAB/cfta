import MicroCFTA.SourceSynthesisProgramRolesOwnInputs
import MicroCFTA.SourceSynthesisProgramRolesChildTraversal
import MicroCFTA.SourceSynthesisProgramParentCallbackRoles
import MicroCFTA.SourcePruningEnumerationSharedCapturedPreparedResources
import MicroCFTA.SourcePruningEnumerationOwnPrefixPacket

/-!
# One captured Program edge with its exact callback

The current marked target supplies inherited annotation scope.
One own prefix and one ordered traversal supply the actual child endpoint.
One parent producer supplies finalization and its same callback receipt.
Both complete and stopped child branches retain their complete resources.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesCapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationDriver
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSharedIncomingReservation (Seed advance Reserved)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots SlotRole FragmentRoles)
open SourceSynthesisHereditaryProgramFields (EdgeFields)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge (run)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "HookResult" => NativeContinuations.HookResult
  (SourcePruningEnumerationSharedPreparedRecursive.Output (bits + 2) Typing)
  (SourcePruningEnumerationSharedPreparedRecursive.Failure (bits + 2) Typing) (bits + 2)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem node_bound (limit : Nat) (symbol : Symbol) (fragments : List Fragment)
    (bounded : ∀ fragment ∈ fragments, FragmentBound limit fragment) :
    FragmentBound limit (.node symbol fragments) := by
  induction fragments with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨bounded first (by simp), ih (fun fragment member => bounded fragment (by simp [member]))⟩

/-- One marked captured edge derives its full old receipt and same computed callback. -/
theorem complete_with_history_resources_program_slots
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (caller : Caller (bits + 2)) (before : Cached) (checkEmpty : Bool)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory caller memos)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
    (parentClosed : free = [])
    (realized : PendingRealized caller.checked.native.machine.heap before.core)
    (selected : edge ∈ edges)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (fits : Fits seed.2 caller.checked)
    (reserved : Reserved bits seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries))
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (programTarget : marked uv) (fields : EdgeFields valid literal edge) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      ((∀ er en P H ek, p ≤ P → h ≤ H →
        run checkEmpty (r + er) (n + en) P H (k + ek) uv scs edge caller before memos.query = some result) ∧
      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      (∀ held fragment, held ≠ uv → after.core.values[held]? = some (.enumerated fragment) →
        before.core.values[held]? = some (.enumerated fragment)) ∧
      InputsPending after.core scs ∧
      (∀ held, held ≠ uv → held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs → EnumerationDriver.Protected held before.core after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.IncomingAvoid uv before.core →
        EnumerationReferences.PendingReferences after.core) ∧
      ((∃ fragment, result = .complete fragment afterCaller savedQueries after ∧
          Safe after.core ∧ FragmentBound after.core.counter fragment ∧
          after.core.values[uv]? = some (.enumerated fragment) ∧ after.core.expansionAncestry = [] ∧
          IsRoot after.core.representatives uv ∧ PendingFragment after.core fragment ∧
          ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
            ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1)) ∨
        ∃ fragments outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed
        (SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.cost edge scs before.core.counter tries)).1)
        afterCaller.checked.native.machine.heap ) ∧
      ∃ finalMarked : Nat → Prop, (∀ held, marked held → finalMarked held) ∧
        ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core finalMarked ∧
        ∀ fragment, result = .complete fragment afterCaller savedQueries after →
          FragmentRoles literal finalMarked fragment ∧
          Packet formulas solver next afterCaller final metadata after ∧
          ∃ (childrenAfter : Cached) (finalizeFuel callbackFuel : Nat)
            (recorded : Bool × Metadata Typing) (recordAfter : Core),
            ((∀ extra, SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap
              (finalizeFuel + extra) uv fragment
              (SelectedEdge.finish residual fragment childrenAfter) = some after) ∧
            ExceptT.run (SourcePruningEnumerationFinalize.finish uv fragment
              (SelectedEdge.finish residual fragment childrenAfter).core) = [.ok (fragment, after.core)] ∧
            after.core = {(SelectedEdge.finish residual fragment childrenAfter).core with
              values := childrenAfter.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
            after.core.values[uv]? = some (.enumerated fragment) ∧
            after.expandable = (fun slot => if slot = uv then false else childrenAfter.expandable slot) ∧
            after.waiting = EnumerationCanonicalWaiting.count afterRoots (-1)
              (references (.unenumerated (some handle) scs : UVarValue Symbol)) childrenAfter.waiting ∧
            Roots after.core.representatives afterRoots ∧
            EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
            (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
              ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
            StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
            (Safe (SelectedEdge.finish residual fragment childrenAfter).core →
              IsRoot childrenAfter.core.representatives uv → Safe after.core)) ∧
            (Packet formulas solver next afterCaller final recorded.2
                (EnumerationExpandableIndex.frame recordAfter after) ∧
            RenderStable after.core recordAfter ∧ EnumerationCompressionFrame.Frame after.core recordAfter ∧
            recorded.2.types = updatedTypes metadata uv (.inl fragment) ∧
            recorded.2.openHoles = metadata.openHoles ∧ recorded.2.typing = metadata.typing ∧
            Fits (advance seed (SelectedEdge.cost edge scs before.core.counter tries)).2 afterCaller.checked ∧
            Heap (fun guard => guard ∈ (advance seed (SelectedEdge.cost edge scs before.core.counter tries)).1)
              afterCaller.checked.native.machine.heap ∧
            ∀ extra,
              Success (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
                after.core recorded recordAfter ∧
              ExceptT.run (recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment)
                after.core) = [.ok (recorded, recordAfter)] ∧
              ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → HookResult)
                  stop order,
                SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
                  (callbackFuel + extra) metadata uv fragment afterCaller final.query after =
                  if recorded.1 then .complete [] afterCaller final.query
                  else recur recorded.2 afterCaller final.query (EnumerationExpandableIndex.frame recordAfter after)
                    (SourcePruningEnumerationRestart.decision stop order recorded.2
                      (EnumerationExpandableIndex.frame recordAfter after))) ∧
            ProgramSlots valid literal afterCaller.checked.native.machine.heap recordAfter finalMarked := by
  have inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
    obtain ⟨payload, present, role⟩ := slots.stored uv programTarget
    have same : payload = .unenumerated (some handle) scs := Option.some.inj (present.symm.trans stored)
    subst payload
    cases role with
    | pending _native _bucket _value _decoded _fields validTries annotationPaths =>
        intro sc member
        refine ⟨validTries sc member, ?_⟩
        intro path listed
        obtain ⟨tail, same⟩ := annotationPaths sc member path listed
        exact ⟨tail, same.symm⟩
  have bounded : ∀ sc ∈ scs, sc.var < before.core.counter :=
    ready.safe.1.values _ (List.mem_of_getElem? stored)
  have avoids := ready.avoids handle scs stored
  obtain ⟨_action, own, _prepared, ownRun, _raw, ownCore, ownCounter, _ownForest,
      ownSafe, ownPaths, ownRealized, ownCounts, ownFlags, combinedPending, genuine,
      ownProtects, ownSlots, ownMarked⟩ :=
    SourceSynthesisProgramRolesOwnInputs.complete_program_slots valid literal marked
      caller.checked.native.machine.heap parentEntry edges depth free edge scs roots
      initial.ready.semantic.ready parentAvailable parentClosed selected before ready.safe realized
      paths counts flags bounded pending allowed tries residual projected slots uv (some handle) stored
  have ownPacket := SourcePruningEnumerationOpaqueEvent.own_prefix_packet formulas solver inventory
    caller memos metadata before own tries.length packet ownCore
    ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩
  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
  have readback : ((inputs.map (fun input =>
      (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))).map
      (fun input => (input.1, input.2.1))) = inputs := by
    simp only [List.map_map]
    exact List.map_id _
  obtain ⟨r, n, p, h, k, fragments, afterCaller, childrenAfter, savedQueries, final, next,
      childRoots, childResult, childrenRun, post, querySame, childGrowth, childPaths,
      childStorage, childRealized, childCounts, childFlags, childOrigin, enumProtects,
      rootsProtects, _references, pendingHistory, fragmentBounds, shape, returnedFits,
      returnedKnown, finalMarked, finalExtension, childSlots, childRoles⟩ :=
    SourceSynthesisProgramRolesChildTraversal.complete_with_fragments_resources_program_slots
      seed formulas solver inventory caller own checkEmpty inputs roots memos initial ownSafe
      ownPaths ownCounts ownFlags ownRealized genuine fits reserved known valid marked ownSlots
      edge fields scs before.core.counter tries residual inherited projected rfl
      (fun held tagged => (ownMarked held tagged).2)
  have ownOrigin : EnumeratedOrigin before.core own.core := by
    rw [ownCore]
    exact suspension_origin tries.length before.core
  have fullOrigin := ownOrigin.trans childOrigin
  have fullGrowth : before.core.counter ≤ childrenAfter.core.counter := by omega
  have ownPending : InputsPending own.core scs := by
    intro held fragment present sc member
    exact combinedPending held fragment present sc (List.mem_append_left _ member)
  have retained := ChildTraversal.retained_inputs own.core childrenAfter.core scs
    ownPending childOrigin enumProtects
  have protectedRoots : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs → Protected held before.core childrenAfter.core := by
    intro held inside root separate
    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root separate
    exact frame.trans (rootsProtects held (by omega) frame.root avoidsChildren)
  rcases shape with ⟨completed, childSafe, fragmentHistory⟩ | ⟨outer, waiting, stopped⟩
  · subst childResult
    let parent : Fragment := .node edge.entry.key.symbol fragments
    have parentBound : FragmentBound childrenAfter.core.counter parent :=
      node_bound _ _ _ fragmentBounds
    have targetFrame := protectedRoots uv ready.inside ready.root avoids
    have currentStored : childrenAfter.core.values[uv]? = some (.unenumerated (some handle) scs) :=
      targetFrame.value.trans stored
    have history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
        FragmentAvoid childrenAfter.core.representatives uv child := by
      intro child member
      exact ⟨(fragmentHistory child member).1,
        (fragmentHistory child member).2 uv (ownSlots.bounded uv programTarget)
          (ownSlots.roots uv programTarget) (ownMarked uv programTarget).2⟩
    obtain ⟨level, frontier, ownOrder⟩ := ownPacket.ordered
    obtain ⟨childLevel, childOrder⟩ := EnumerationOrder.stratified_preserved own.core childrenAfter.core
      childSafe level frontier ownOrder childOrigin enumProtects
    have childPacket : Packet formulas solver next afterCaller final metadata childrenAfter := by
      refine ⟨post.context, childSafe, pendingHistory ownPacket.pending,
        ⟨childRoots, childPaths, childStorage, childRealized, childCounts, childFlags⟩,
        ⟨childLevel, frontier, childOrder⟩, ?_⟩
      intro group member entry listed
      exact Nat.lt_of_lt_of_le (ownPacket.bounded group member entry listed) childGrowth
    have actualChildren : ChildTraversal.run checkEmpty r n p h k inputs caller own memos.query =
        .complete fragments afterCaller savedQueries childrenAfter := by
      simpa only [Nat.add_zero] using childrenRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
    have trace := ChildTraversal.complete_trace checkEmpty r n p h k inputs caller afterCaller
      own childrenAfter memos.query savedQueries fragments actualChildren
    have traceAtFinal : ChildTraversal.Trace checkEmpty r n p h k inputs caller own memos.query
        fragments afterCaller childrenAfter final.query := by
      simpa only [querySame] using trace
    obtain ⟨afterRoots, finalizeFuel, after, callbackFuel, recorded, recordAfter, finalization,
        finalPacket, callback, parentRoles, afterSlots, recordSlots⟩ :=
      SourceSynthesisProgramParentCallbackRoles.parent_callback_roles valid finalMarked formulas solver next
        graph templates metadata uv (finalExtension uv programTarget) (some handle) scs edge fields
        checkEmpty r n p h k before.core.counter scs tries residual caller afterCaller own childrenAfter
        memos.query final fragments traceAtFinal childRoles childSlots currentStored history
        (advance seed (SelectedEdge.cost edge scs before.core.counter tries)) childPacket parentBound
        returnedFits returnedKnown
    have finalizationReceipt := finalization
    obtain ⟨finishRun, _finishRaw, core, finalStored, _finalFlag, _finalWaiting, afterPaths,
      afterCounts, afterFlags, afterStorage, afterRealized, _safeFinish⟩ := finalization
    have afterCounter : after.core.counter = childrenAfter.core.counter := by rw [core]; rfl
    have selectedRun : ∀ er en P H ek, p ≤ P → h ≤ H →
        SelectedEdge.run checkEmpty (r + er) (n + en) P H (k + ek) scs edge caller before memos.query =
          .complete parent afterCaller savedQueries (SelectedEdge.finish residual parent childrenAfter) := by
      intro er en P H ek largeP largeH
      simp only [SelectedEdge.run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    have parentPending : PendingFragment (SelectedEdge.finish residual parent childrenAfter).core parent :=
      pendingFragment_node childrenAfter.core _ fragments (fun child member => (history child member).1)
    have parentSeparate : FragmentAvoid childrenAfter.core.representatives uv parent := by
      intro held hole
      change HasHole (.node edge.entry.key.symbol fragments) held at hole
      cases hole with
      | child _ _ child _ member below => exact (history child member).2 held below
    have afterFragmentPending : PendingFragment after.core parent := by
      rw [core]
      exact pendingFragment_write (SelectedEdge.finish residual parent childrenAfter).core
        uv parent parentPending parentSeparate
    have orderAdvance : ∀ level frontier, EnumerationOrder.Stratified before.core level frontier →
        ∃ nextLevel, EnumerationOrder.Stratified after.core nextLevel (frontier + 1) := by
      intro level frontier stratified
      have preparedSafe := SelectedEdge.finish_safe residual parent childrenAfter childSafe parentBound
      have oldEnums : ∀ held old, before.core.values[held]? = some (.enumerated old) →
          Protected held before.core (SelectedEdge.finish residual parent childrenAfter).core := by
        intro held old present
        obtain ⟨inside, root⟩ := enumerated_root before.core ready.safe held old present
        have frame := protectedRoots held inside root (pending held old present)
        exact frame.trans (SelectedEdge.finish_protected residual parent childrenAfter held frame.root)
      obtain ⟨middleLevel, middleOrder⟩ := EnumerationOrder.stratified_preserved before.core
        (SelectedEdge.finish residual parent childrenAfter).core preparedSafe level frontier
        stratified fullOrigin oldEnums
      obtain ⟨nextLevel, nextOrder⟩ := EnumerationOrder.write_stratified
        (SelectedEdge.finish residual parent childrenAfter).core preparedSafe middleLevel frontier uv
        middleOrder (some handle) scs currentStored parent parentPending parentSeparate
      refine ⟨nextLevel, ?_⟩
      rw [core]
      exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) nextOrder
    have afterPending : InputsPending after.core scs := by
      intro held old expanded
      by_cases same : held = uv
      · subst held
        rw [core]
        exact targetFrame.avoids scs avoids
      · rw [core] at expanded
        rw [core]
        apply retained held old
        simpa only [List.getElem?_set_ne (Ne.symm same)] using expanded
    refine ⟨r, n, p, h, k + finalizeFuel, afterCaller, after, savedQueries, final, next, afterRoots,
      .complete parent afterCaller savedQueries after, ⟨?_, post, querySame, ?_, afterPaths,
      afterStorage, afterRealized, afterCounts, afterFlags, ?_, afterPending, ?_,
      (fun _history _incoming => finalPacket.pending),
      .inl ⟨parent, rfl, finalPacket.safe, ?_, finalStored, ?_,
        afterSlots.roots uv (finalExtension uv programTarget), afterFragmentPending, orderAdvance⟩,
      returnedFits, returnedKnown⟩,
      finalMarked, finalExtension, afterSlots, ?_⟩
    · intro er en P H ek largeP largeH
      have selectedAt := selectedRun er en P H (finalizeFuel + ek) largeP largeH
      rw [← Nat.add_assoc] at selectedAt
      simp only [CapturedEdge.run, selectedAt]
      have finalAt := finishRun (k + ek)
      rw [show finalizeFuel + (k + ek) = k + finalizeFuel + ek by omega] at finalAt
      rw [finalAt]
    · rw [afterCounter]
      exact fullGrowth
    · intro held old different expanded
      apply fullOrigin held old
      rw [core] at expanded
      simpa only [List.getElem?_set_ne (Ne.symm different)] using expanded
    · intro held different inside root separate
      have frame := protectedRoots held inside root separate
      apply frame.trans
      refine ⟨?_, ?_, ?_⟩
      · rw [core]
        exact List.getElem?_set_ne (Ne.symm different)
      · rw [core]
        exact frame.root
      · rw [core]
        exact fun _ => Iff.rfl
    · rw [afterCounter]
      exact parentBound
    · rw [core]
    · intro fragment same
      have fragmentSame : parent = fragment := (SelectedEdge.Result.complete.inj same).1
      rw [← fragmentSame]
      exact ⟨parentRoles, finalPacket, childrenAfter, finalizeFuel, callbackFuel, recorded, recordAfter,
        finalizationReceipt, callback, recordSlots⟩
  · subst childResult
    refine ⟨r, n, p, h, k, afterCaller, childrenAfter, savedQueries, final, next, childRoots,
      .stopped fragments (.ok (some []), afterCaller, savedQueries, outer, waiting) (some childrenAfter),
      ⟨?_, post, querySame, fullGrowth, childPaths, childStorage, childRealized, childCounts,
      childFlags, (fun held old _different expanded => fullOrigin held old expanded), retained,
      (fun held _different inside root separate => protectedRoots held inside root separate),
      (fun _history _incoming => pendingHistory ownPacket.pending),
      .inr ⟨fragments, outer, waiting, rfl⟩, returnedFits, returnedKnown⟩,
      finalMarked, finalExtension, childSlots, ?_⟩
    · intro er en P H ek largeP largeH
      simp only [CapturedEdge.run, SelectedEdge.run, ownRun]
      rw [readback, childrenRun er en P H ek largeP largeH]
    · intro fragment impossible
      cases impossible

end MicroCFTA.SourceSynthesisProgramRolesCapturedEdge
