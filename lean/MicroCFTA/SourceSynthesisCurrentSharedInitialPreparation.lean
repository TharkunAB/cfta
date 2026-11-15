import MicroCFTA.SourceSynthesisCurrentFirstRealPrefix
import MicroCFTA.SourcePruningEnumerationPrefixCheckpoint
import MicroCFTA.SourcePruningEnumerationRecursivePrefix
import MicroCFTA.SourcePruningEnumerationSelectedPreparation
import MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy
import MicroCFTA.SourceSynthesisCurrentSharedSourceGoalFreshSlot

/-!
# One common source-prefix and shared-preparation bound

The real prefix has fixed heap and cache endpoints above one bound.
The preparation bound enlarges that same work fuel.
The actual narrowed parent supplies the shared row scan.
Each retained source row derives its own preparation and first goal input.
The child dispatch result remains separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentSharedInitialPreparation
open Cache EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedBinderProtocol (NodeKey Reference)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourcePruningEnumerationSelectedStep (Result PrefixValid runPrefix)
open SourcePruningEnumerationNodes (encodeNode lookupNode)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "advance" => SourcePruningEnumerationSelectedValueCaller.advance
universe u v
variable {Typing Key : Type} {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] SourcePruningEnumerationAction.actionMonadList

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem node_lookup
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (entry : Interned NodeKey) (rows : List Edge) (depth : Nat) (free : List Reference)
    (facts : InternedNestedFacts.Facts heap)
    (available : Available heap (.node entry rows depth free)) :
    lookupNode heap (entry.identity + 1) = some (.node entry rows depth free) := by
  have canonical : heap.nodes.table entry.key = some entry :=
    InternedFreshProbeKeys.resident_entry heap facts.coherent _ available.resident entry rfl
  have issued : heap.nodes.issued entry.identity = some entry.key :=
    (facts.coherent.valid.2.2 entry.key entry canonical).2
  simpa only [lookupNode, issued, canonical, ↓reduceIte] using available.resident entry rfl

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem source_row_own_first
    (inventory : Inventory)
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue inventory.source)
    (row : Edge) (member : row ∈ InternedEdgeResidency.nodeEdges rootValue)
    (caller : Caller width) (captured : Cached) (storage : StorageValid captured.core) :
    ∃ (symbol : Symbol) (staged : List Input) (residual : Option Constraint) (middle : Cached)
      (goal : Node) (goalHeap : InternedConstructorTemplates.State Symbol Constraint)
      (goalAction : Option (EnumerateM Symbol Constraint Fragment)),
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap [] row captured =
        some [((symbol, staged, residual), middle)] ∧
      build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
        .done goal goalHeap ∧
      staged[0]? = some (goal, [⟨.terminal, captured.core.counter⟩], goalAction) := by
  obtain ⟨_chunks, _goal, _candidate, _goalHeap, _candidateAfter, _edgeAfter,
      _chunksRun, _wholeShape, _symbol, constraint, _children, _goalBuilt,
      _candidateContext, _candidateBuilt, _edgeMade, _rootMade, _candidateGrowth, _factory⟩ :=
    SourceSynthesisCurrentFirstFilterSourceLink.current_initial_filter_interval
      lib query signed whole accepted rootValue inventory.source built row member
  let trie := EnumerationEquality.classTrie [[0], [1, 0]]
  let middle : Cached := ⟨allocated none captured.core, captured.expandable, captured.waiting⟩
  let own : List Suspended := [⟨trie, captured.core.counter⟩]
  let staged : List Input := row.children.zipIdx.map fun indexed =>
    let bucket := descendScs indexed.2 [] ++ descendScs indexed.2 own
    (indexed.1, bucket,
      SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) bucket indexed.1)
  have projected : SourcePruningEnumerationConstraint.project row.entry.key.constraint =
      some (EnumerationEquality.readClasses [[[0], [1, 0]]], none) := by
    rw [constraint]
    exact SourceSynthesisOwnChildTerminals.filter_projection
  have ownRun : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap
      (EnumerationEquality.readClasses [[[0], [1, 0]]]) captured = some (own, middle) := by
    rfl
  have prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap [] row captured =
      some [((row.entry.key.symbol, staged, none), middle)] := by
    simp only [SourcePruningEnumerationCachedOwn.prepare, arityAllows, List.all_nil,
      ↓reduceIte, projected, ownRun, Option.map_some]
    rfl
  obtain ⟨goal, goalHeap, goalAction, goalBuilt, first, _rest⟩ :=
    SourceSynthesisCurrentSharedSourceGoalFreshSlot.source_goal_prepared_fresh_slot
      inventory lib query signed whole accepted rootValue built row member caller captured middle storage
      row.entry.key.symbol staged none prepared
  exact ⟨row.entry.key.symbol, staged, none, middle, goal, goalHeap, goalAction,
    prepared, goalBuilt, first⟩

/-- One original source initialization reaches the real prefix and shared scan at one common fuel. -/
theorem accepted_shared_initial_preparation
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : build (ordinarySymbols whole) [] empty = .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : EnumerationState.Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ∃ fields cache handle bound,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (SourceEqualityConstraintOrigins.guards (ordinarySymbols whole)) Cache.emptyState fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) sourceHeap ∧
      Context formulas solver
        (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols whole) rootValue sourceHeap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap)
        SourceCurrentAllocatedPartialInitialization.globals ∧
      sourceHeap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      encodeNode rootValue = some handle ∧ lookupNode sourceHeap handle = some rootValue ∧
      let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
      let startup : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
      let inventory := SourceCurrentAllocatedPartialInitialization.inventory
        (ordinarySymbols whole) rootValue sourceHeap built
      let memos := SourceCurrentAllocatedPartialInitialization.globals
      SourcePruningEnumerationRestart.decision none (fun _ _ => none) metadata startup = some (.expand 0) ∧
      runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
        0 0 0 0 0 0 0 caller startup memos.query = .stopped [.error .representativeFuel] none ∧
      ((∃ (checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint) (final : Memos),
          Post formulas solver inventory caller (advance caller heap) final ∧ final.query = memos.query ∧
          ∀ extra,
            let w := bound + extra
            let observed := runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
              w w w w w w 0 caller startup memos.query
            observed = .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
              (advance caller heap) memos.query (some []) none none none ∧
            PrefixValid holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
              none (fun _ _ => none) metadata formulas solver inventory w 0 caller startup memos observed) ∨
        ∃ (checked : Core) (parentEntry : Interned NodeKey) (rows : List Edge) (parentDepth : Nat)
          (free : List Reference) (heap : InternedConstructorTemplates.State Symbol Constraint)
          (retained entered : Cached) (newHandle : Nat) (final : Memos),
          let parent : Node := .node parentEntry rows parentDepth free
          let reached := advance caller heap
          let preparedCaller := advance reached heap
          rootValue ≠ .empty ∧ free = [] ∧ final.query = memos.query ∧
          Post formulas solver inventory caller reached final ∧
          Packet formulas solver inventory reached final metadata retained ∧
          Packet formulas solver inventory preparedCaller final metadata entered ∧
          Context formulas solver inventory preparedCaller final ∧
          retained.core.values[0]? = some (.unenumerated (some newHandle) []) ∧
          EnumerationDriver.Ready 0 retained.core ∧
          entered.core.counter = retained.core.counter ∧
          (∀ row ∈ rows,
            row ∈ InternedEdgeResidency.nodeEdges rootValue ∧
            ∃ (symbol : Symbol) (staged : List Input) (residual : Option Constraint) (middle : Cached)
              (goal : Node) (goalHeap : InternedConstructorTemplates.State Symbol Constraint)
              (goalAction : Option (EnumerateM Symbol Constraint Fragment)),
              SourcePruningEnumerationCachedOwn.prepare preparedCaller.checked.native.machine.heap [] row
                (EnumerationExpandableIndex.frame entered.core retained) =
                some [((symbol, staged, residual), middle)] ∧
              build (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal)) [] empty =
                .done goal goalHeap ∧
              staged[0]? = some (goal, [⟨.terminal, entered.core.counter⟩], goalAction)) ∧
          ∀ extra, ∃ action : EnumerateM Symbol Constraint Unit,
            let w := bound + extra
            let observed := runPrefix holeKey fits admits graph templates none (fun _ _ => none) metadata
              w w w w w w 0 caller startup memos.query
            observed = .narrowed checked (.done (parent, some action) heap) reached memos.query
              (some [.ok ((), retained.core)]) (some retained)
              (some [.ok ((false, metadata), retained.core)]) none ∧
            PrefixValid holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
              none (fun _ _ => none) metadata formulas solver inventory w 0 caller startup memos observed ∧
            SourcePruningEnumerationSelectedPreparation.run w w 0 reached retained =
              ([.ok ((0, newHandle, [], parent), entered.core)], some (.done parent heap)) ∧
            ∀ (r n p h k : Nat)
              (hook : Fragment → Caller width → Queries → Cached →
                SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult Output Reason width),
              SourcePruningEnumerationSharedPreparedChildPolicy.runEager hook checkEmpty w w r n p h k 0
                InternedEdgeResidency.nodeEdges reached retained memos.query =
              (([.ok ((0, newHandle, [], parent), entered.core)], some (.done parent heap)),
                some (SourcePruningEnumerationSharedBranching.scan
                  (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
                    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k
                      InternedEdgeResidency.nodeEdges) hook k 0 [])
                  (EnumerationExpandableIndex.frame entered.core retained) rows preparedCaller memos.query))) := by
  obtain ⟨fields, cache, handle, firstBound, receipt, fieldFacts, context, _stored, encoded, decoded,
      zero, first⟩ :=
    SourceSynthesisCurrentFirstRealPrefix.accepted_first_real_prefix (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      formulas solver holeKey fits admits graph templates checkEmpty metadata emptyPending
  obtain ⟨_otherFields, otherCache, otherReceipt, _otherFieldFacts, _otherContext, _otherStored,
      _clear, otherHandle, otherEncoded, _otherDecoded, decision, _entryEquation⟩ :=
    SourceSynthesisCurrentNoStopSourceEntry.accepted_no_stop_eager_entry (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      formulas solver holeKey fits admits graph templates checkEmpty 0 1 metadata
  have cacheSame : otherCache = cache := congrArg Prod.snd (otherReceipt.done.symm.trans receipt.done)
  subst otherCache
  have handleSame : otherHandle = handle := Option.some.inj (otherEncoded.symm.trans encoded)
  subst otherHandle
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache sourceHeap
  let startup : Cached := ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
    fun _ => none⟩
  let inventory := SourceCurrentAllocatedPartialInitialization.inventory
    (ordinarySymbols whole) rootValue sourceHeap built
  let memos := SourceCurrentAllocatedPartialInitialization.globals
  have initialized := SourceCurrentAllocatedPartialInitialization.constructed width receipt.history
    Cache.empty_valid (ordinarySymbols whole) (fun _ member => member)
    rootValue sourceHeap built formulas solver
  obtain ⟨_identity, _emptySame, _emptyReady, available, closed, _original⟩ := initialized.2
  obtain ⟨packetHandle, packetEncoded, _packetDecoded, packet, _canonical, _initialStored,
      _suspendedBound, _initialCounts, _initialFlags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver inventory caller memos metadata
      rootValue context available closed emptyPending
  have packetHandleSame : packetHandle = handle := Option.some.inj (packetEncoded.symm.trans encoded)
  subst packetHandle
  have picked : EnumerationPureSelection.next (fun _ => none) startup = .expand 0 := Option.some.inj decision
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
  obtain ⟨prefixBound, branches⟩ := SourcePruningEnumerationSelectedStep.prefix_checkpoint_complete
    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none)
    metadata formulas solver inventory caller memos startup (fun _ => none) 0 roots
    context packet.safe packet.pending picked realized paths counts flags
  let joint := firstBound + prefixBound + 1
  have jointEq : prefixBound + (firstBound + 1) = joint := by dsimp [joint]; omega
  obtain ⟨_sourceValid, sourceChecked, sourceValue, sourceNativeHeap, sourceAction, sourceReached,
      _sourceFinal, _sourceRaw, _sourceCandidate, _sourceRight, sourceObserved, sourceNarrowed,
      _sourcePost, _sourceFinalQuery, sourceOrdinary, sourceEmpty, sourceShape⟩ := first prefixBound
  rcases branches with parked | rejected | live
  · obtain ⟨checked, stable⟩ := parked
    have atJoint := (stable (firstBound + 1)).1
    rw [jointEq] at atJoint
    have impossible := sourceObserved.symm.trans atJoint
    cases impossible
  · obtain ⟨checked, heap, stable⟩ := rejected
    have atJoint := stable (firstBound + 1)
    rw [jointEq] at atJoint
    have validNarrowed := atJoint.2
    rw [atJoint.1] at validNarrowed
    obtain ⟨final, post, finalQuery⟩ :=
      SourcePruningEnumerationPrefixPacket.prefix_context holeKey fits admits graph templates
        checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none) metadata
        formulas solver inventory joint 0 caller startup memos _ validNarrowed
    refine ⟨fields, cache, handle, joint, receipt, fieldFacts, context, stored, encoded, decoded,
      decision, zero, Or.inl ⟨checked, heap, final, post, finalQuery, ?_⟩⟩
    intro extra
    have boundLe : prefixBound ≤ joint + extra := by dsimp [joint]; omega
    have later := stable (joint + extra - prefixBound)
    rw [Nat.add_sub_of_le boundLe] at later
    exact later
  · obtain ⟨checked, value, heap, retained, nonempty, stable⟩ := live
    obtain ⟨actionAtJoint, observedAtJoint, validAtJoint⟩ := stable (firstBound + 1)
    rw [jointEq] at observedAtJoint validAtJoint
    have same := Result.narrowed.inj (sourceObserved.symm.trans observedAtJoint)
    have nativeSame := MergedSourceComparison.Result.done.inj same.2.1
    have valueSame := (Prod.mk.inj nativeSame.1).1
    have heapSame := nativeSame.2
    have ordinaryValue : SourceEqualityRequiredCache.Ordinary value := by
      rw [← valueSame]
      exact sourceOrdinary
    have narrowActual : SourcePruningOuterNarrow.narrow holeKey fits admits metadata joint 0
        rootValue sourceHeap = .done value heap := by
      rw [← valueSame, ← heapSame]
      exact sourceNarrowed
    have rootNonempty : rootValue ≠ .empty := by
      intro rootEmpty
      exact nonempty (valueSame.symm.trans (sourceEmpty rootEmpty).1)
    have shape : ∃ (parentEntry : Interned NodeKey) (rows : List Edge) (parentDepth : Nat)
        (free : List Reference), value = .node parentEntry rows parentDepth free := by
      cases value with
      | empty => exact False.elim (nonempty rfl)
      | reference _ => cases ordinaryValue
      | node parentEntry rows parentDepth free => exact ⟨parentEntry, rows, parentDepth, free, rfl⟩
      | union _ _ _ _ => cases ordinaryValue
      | mu _ _ _ _ => cases ordinaryValue
    obtain ⟨parentEntry, rows, parentDepth, free, rfl⟩ := shape
    rcases sourceShape with sourceRejected | sourceLive
    · exact False.elim (nonempty (valueSame.symm.trans sourceRejected.1))
    obtain ⟨newHandle, sourceRetained, _sourceNonempty, sourceEncoded, _sourceActionEq,
      sourceCandidate, _sourceCache, _sourceSafe, _sourcePending, sourceReady, sourceStored,
      _sourceWaiting, _sourceCallback⟩ := sourceLive
    have candidateSame := same.2.2.2.2.2.1
    have retainedSame : sourceRetained = retained := Option.some.inj (sourceCandidate.symm.trans candidateSame)
    subst sourceRetained
    have parentEncoded : encodeNode (.node parentEntry rows parentDepth free : Node) = some newHandle := by
      rw [← valueSame]
      exact sourceEncoded
    have newHandleSame : newHandle = parentEntry.identity + 1 := (Option.some.inj parentEncoded).symm
    subst newHandle
    have narrowedFacts := SourceSynthesisCurrentInitialOuterNarrowFacts.initial_outer_narrow_facts
      lib query signed whole accepted rootValue sourceHeap built metadata holeKey fits admits joint
      (.node parentEntry rows parentDepth free) heap narrowActual
    have parentLookup := node_lookup heap parentEntry rows parentDepth free narrowedFacts.1 narrowedFacts.2.1
    have validNarrowed := validAtJoint
    rw [observedAtJoint] at validNarrowed
    obtain ⟨final, post, finalQuery, retainedPacket⟩ :=
      SourcePruningEnumerationRecursive.prefix_packet holeKey fits admits graph templates
        checkEmpty InternedEdgeResidency.nodeEdges none (fun _ _ => none) metadata
        formulas solver inventory joint 0 caller memos startup packet _ validNarrowed
    let reached := advance caller heap
    have reachedHeap : reached.checked.native.machine.heap = heap := by rfl
    obtain ⟨preparationBound, decodedParent, preparedParent, preparedHeap, entered, preparation,
      decodedParentLookup, preparationPost, enteredPacket, _renderStable, _enteredReady, _enteredStored,
      counter, _values, _expandable, _waiting, _preparedAvailable, preparedClosed, _language, _models⟩ :=
      SourcePruningEnumerationSelectedPreparation.complete formulas solver inventory reached final metadata
        retained 0 (parentEntry.identity + 1) [] retainedPacket sourceReady sourceStored
    have decodedSame : decodedParent = .node parentEntry rows parentDepth free :=
      Option.some.inj (decodedParentLookup.symm.trans parentLookup)
    subst decodedParent
    have enterAtZero : ExceptT.run (SourcePruningEnumerationEntry.enter reached.checked.native.machine.heap
        preparationBound 0 retained.core) =
        [.ok ((0, parentEntry.identity + 1, [], .node parentEntry rows parentDepth free), entered.core)] := by
      simpa only [SourcePruningEnumerationSelectedPreparation.run, Nat.add_zero] using
        congrArg Prod.fst (preparation 0)
    have enterLiteral := enterAtZero
    rw [reachedHeap] at enterLiteral
    have nativeAtZero : some (.done (.node parentEntry rows parentDepth free) heap :
        MergedSourceComparison.Result Symbol Constraint Node) = some (.done preparedParent preparedHeap) := by
      simpa only [SourcePruningEnumerationSelectedPreparation.run, Nat.add_zero, enterLiteral,
        SourcePruningEnumerationSelectedValue.run, reachedHeap] using congrArg Prod.snd (preparation 0)
    have preparedSame := MergedSourceComparison.Result.done.inj (Option.some.inj nativeAtZero)
    have preparedParentSame := preparedSame.1.symm
    have preparedHeapSame := preparedSame.2.symm
    subst preparedParent
    subst preparedHeap
    let bound := joint + preparationBound
    refine ⟨fields, cache, handle, bound, receipt, fieldFacts, context, stored, encoded, decoded, decision, zero,
      Or.inr ⟨checked, parentEntry, rows, parentDepth, free, heap, retained, entered,
        parentEntry.identity + 1, final, rootNonempty, preparedClosed, finalQuery, post, retainedPacket,
        enteredPacket, preparationPost.context, sourceStored, sourceReady, counter, ?_, ?_⟩⟩
    · intro row member
      have originalMember := SourceSynthesisCurrentInitialOuterNarrowRows.initial_outer_narrow_rows
        lib query signed whole accepted rootValue sourceHeap built metadata holeKey fits admits joint
        (.node parentEntry rows parentDepth free) heap narrowActual row member
      exact ⟨originalMember, source_row_own_first inventory lib query signed whole accepted rootValue built
        row originalMember (advance reached heap) (EnumerationExpandableIndex.frame entered.core retained)
        enteredPacket.safe.1⟩
    · intro extra
      have prefixLe : prefixBound ≤ bound + extra := by dsimp [bound, joint]; omega
      obtain ⟨action, observed, prefixValid⟩ := stable (bound + extra - prefixBound)
      rw [Nat.add_sub_of_le prefixLe] at observed prefixValid
      have preparationLe : preparationBound ≤ bound + extra := by dsimp [bound]; omega
      have preparedAtWork := preparation (bound + extra - preparationBound)
      rw [Nat.add_sub_of_le preparationLe] at preparedAtWork
      refine ⟨action, observed, prefixValid, preparedAtWork, ?_⟩
      intro r n p h k hook
      have preparedLiteral := preparedAtWork
      dsimp only [reached, caller] at preparedLiteral
      simp only [SourcePruningEnumerationSharedPreparedChildPolicy.runEager,
        SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild, preparedLiteral,
        List.any_nil, Bool.false_eq_true, ite_false, InternedEdgeResidency.nodeEdges]

end MicroCFTA.SourceSynthesisCurrentSharedInitialPreparation
