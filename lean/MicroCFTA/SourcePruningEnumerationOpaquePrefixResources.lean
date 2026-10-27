import MicroCFTA.SourcePruningEnumerationTraversalResources
import MicroCFTA.SourcePruningEnumerationRecursivePacket
import MicroCFTA.SourcePruningEnumerationOpaqueEventTrace
import MicroCFTA.EnumerationStratifiedTransport

namespace MicroCFTA.SourcePruningEnumerationOpaqueEvent
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
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
local notation "cost" => SourcePruningEnumerationTraversalCompletion.cost
variable {bits : Nat}

/-- Ordered concatenation adds each original child reservation, including duplicates. -/
theorem cost_append (consumed remaining : List (Node × List Suspended)) :
    cost (consumed ++ remaining) = cost consumed + cost remaining := by
  induction consumed with
  | nil => simp only [List.nil_append, SourcePruningEnumerationTraversalCompletion.cost, Nat.zero_add]
  | cons input consumed ih =>
      rcases input with ⟨value, bucket⟩
      simp only [List.cons_append, SourcePruningEnumerationTraversalCompletion.cost, ih, Nat.add_assoc]

/-- An actual prefix retains its full native admission and the remaining original schedule. -/
def PrefixAdmission {Typing : Type} [DecidableEq (EdgeKey Symbol Constraint)]
    (seed : Seed) (consumed remaining : List (Node × List Suspended))
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (beforeCaller : Caller (bits + 2)) (before : Cached)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (eventCaller : Caller (bits + 2)) (eventBefore : Cached) (eventQueries : Queries) : Prop :=
  ∃ (next : Inventory) (eventMemos : Memos),
    Post formulas solver next beforeCaller eventCaller eventMemos ∧ eventMemos.query = eventQueries ∧
    SourcePruningEnumerationRecursive.Packet formulas solver next eventCaller eventMemos metadata eventBefore ∧
    before.core.counter ≤ eventBefore.core.counter ∧
    (∀ value bucket, (value, bucket) ∈ remaining →
      Available eventCaller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ sc ∈ bucket, sc.var < eventBefore.core.counter) ∧ InputsPending eventBefore.core bucket) ∧
    Fits (advance seed (cost consumed)).2 eventCaller.checked ∧
    Heap (fun guard => guard ∈ (advance seed (cost consumed)).1) eventCaller.checked.native.machine.heap ∧
    Reserved bits (advance seed (cost consumed)) (cost remaining)

/-- Original resources certify each selected prefix at the same sufficient diagonal execution. -/
theorem complete_with_prefix_resources
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Cached)
    (checkEmpty : Bool) (inputs : List (Node × List Suspended))
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (genuine : ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Available beforeCaller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed (cost inputs))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (consumed remaining : List (Node × List Suspended))
    (splitInputs : inputs = consumed ++ remaining) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationChildTraversal.Result (bits + 2)),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
          P H (k + extraIndex) inputs beforeCaller before memos.query = result) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      EnumeratedOrigin before.core after.core ∧
      (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
        EnumerationDriver.Protected held before.core after.core) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        (∀ incoming bucket, (incoming, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
      (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
      ((result = .complete fragments afterCaller savedQueries after ∧ Safe after.core ∧
          ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
            ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
              (∀ incoming bucket, (incoming, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
              FragmentAvoid after.core.representatives held fragment) ∨
        ∃ outer waiting, result = .stopped fragments
          (.ok (some []), afterCaller, savedQueries, outer, waiting) (some after)) ∧
      Fits (advance seed (cost inputs)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (cost inputs)).1) afterCaller.checked.native.machine.heap ∧
      ∀ {Typing : Type} (metadata : SourcePruningRecordTypes.Metadata Typing),
        SourcePruningEnumerationRecursive.Packet formulas solver inventory beforeCaller memos metadata before →
        ∀ (extra : Nat) (prefixFragments : List Fragment) (eventCaller : Caller (bits + 2))
          (eventBefore : Cached) (eventQueries : Queries),
        SourcePruningEnumerationChildTraversal.Trace checkEmpty
          (r + n + p + h + k + extra) (r + n + p + h + k + extra)
          (r + n + p + h + k + extra) (r + n + p + h + k + extra)
          (r + n + p + h + k + extra) consumed beforeCaller before memos.query
          prefixFragments eventCaller eventBefore eventQueries →
        PrefixAdmission seed consumed remaining formulas solver beforeCaller before
          metadata eventCaller eventBefore eventQueries := by
  obtain ⟨r, n, p, h, k, fragments, afterCaller, after, savedQueries, final, next, afterRoots, result,
    running, post, querySame, growth, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags,
    origin, enumeratedProtected, rootsProtected, references, pendingHistory, fragmentBounds,
    shape, returnedFits, returnedKnown⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources seed formulas solver
      inventory beforeCaller before checkEmpty inputs roots memos initial safe paths counts flags
      realized genuine fits reserved known
  have reservationSplit : Reserved bits seed (cost consumed + cost remaining) := by
    simpa only [splitInputs, cost_append] using reserved
  have consumedGenuine : ∀ value bucket, (value, bucket) ∈ consumed →
      Available beforeCaller.checked.native.machine.heap value ∧ value.free = [] ∧
      (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket := by
    intro value bucket member
    apply genuine value bucket
    rw [splitInputs]
    exact List.mem_append.mpr (.inl member)
  obtain ⟨R, N, P, H, K, prefixFragments, prefixCaller, prefixCache, prefixQueries, prefixMemos,
    prefixInventory, prefixRoots, prefixResult, prefixRunning, prefixPost, prefixQuerySame,
    prefixGrowth, prefixPaths, prefixStorage, prefixRealized, prefixCounts, prefixFlags,
    prefixOrigin, prefixProtected, _prefixRootProtected, _prefixReferences, prefixPending,
    _prefixBounds, prefixShape, prefixFits, prefixKnown⟩ :=
    SourcePruningEnumerationTraversalCompletion.complete_with_fragments_resources seed formulas solver
      inventory beforeCaller before checkEmpty consumed roots memos initial safe paths counts flags
      realized consumedGenuine fits (reservationSplit.prefix (by omega)) known
  let bound := r + n + p + h + k + R + N + P + H + K
  have large : r ≤ bound ∧ n ≤ bound ∧ p ≤ bound ∧ h ≤ bound ∧ k ≤ bound ∧
      R ≤ bound ∧ N ≤ bound ∧ P ≤ bound ∧ H ≤ bound ∧ K ≤ bound := by
    dsimp only [bound]
    omega
  refine ⟨bound, bound, bound, bound, bound, fragments, afterCaller, after, savedQueries,
    final, next, afterRoots, result, ?_, post, querySame, growth, afterPaths, afterStorage,
    afterRealized, afterCounts, afterFlags, origin, enumeratedProtected, rootsProtected,
    references, pendingHistory, fragmentBounds, shape, returnedFits, returnedKnown, ?_⟩
  · intro er en largeP largeH ek enoughP enoughH
    have stable := running (bound - r + er) (bound - n + en) largeP largeH (bound - k + ek)
      (by omega) (by omega)
    have rSame : r + (bound - r + er) = bound + er := by omega
    have nSame : n + (bound - n + en) = bound + en := by omega
    have kSame : k + (bound - k + ek) = bound + ek := by omega
    simpa only [rSame, nSame, kSame] using stable
  · intro Typing metadata packet extra actualFragments eventCaller eventBefore eventQueries actualTrace
    let work := bound + bound + bound + bound + bound + extra
    have RSame : R + (work - R) = work := by dsimp only [work]; omega
    have NSame : N + (work - N) = work := by dsimp only [work]; omega
    have KSame : K + (work - K) = work := by dsimp only [work]; omega
    have adequatePrefix : SourcePruningEnumerationChildTraversal.run checkEmpty work work work work work
        consumed beforeCaller before memos.query = prefixResult := by
      have stable := prefixRunning (work - R) (work - N) work work (work - K)
        (by dsimp only [work]; omega) (by dsimp only [work]; omega)
      simpa only [RSame, NSame, KSame] using stable
    have actualPrefix := SourcePruningEnumerationChildTraversal.trace_complete actualTrace
    change SourcePruningEnumerationChildTraversal.run checkEmpty work work work work work consumed
      beforeCaller before memos.query = .complete actualFragments eventCaller eventQueries eventBefore at actualPrefix
    have matched := adequatePrefix.symm.trans actualPrefix
    rcases prefixShape with ⟨prefixComplete, prefixSafe, _fragmentHistory⟩ | ⟨outer, waiting, prefixStopped⟩
    · rw [prefixComplete] at matched
      cases matched
      obtain ⟨level, frontier, beforeOrder⟩ := packet.ordered
      obtain ⟨afterLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core prefixCache.core
        prefixSafe level frontier beforeOrder prefixOrigin prefixProtected
      have prefixPacket : SourcePruningEnumerationRecursive.Packet formulas solver prefixInventory
          prefixCaller prefixMemos metadata prefixCache := by
        refine ⟨prefixPost.context, prefixSafe, prefixPending packet.pending,
          ⟨prefixRoots, prefixPaths, prefixStorage, prefixRealized, prefixCounts, prefixFlags⟩,
          ⟨afterLevel, frontier, afterOrder⟩, ?_⟩
        intro group member entry listed
        exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) prefixGrowth
      refine ⟨prefixInventory, prefixMemos, prefixPost, prefixQuerySame, prefixPacket, prefixGrowth,
        ?_, prefixFits, prefixKnown, reservationSplit.after_prefix⟩
      intro value bucket member
      have originalMember : (value, bucket) ∈ inputs := by
        rw [splitInputs]
        exact List.mem_append.mpr (.inr member)
      obtain ⟨available, closed, bounded, pending⟩ := genuine value bucket originalMember
      refine ⟨prefixPost.effects.keeps.available value available, closed,
        fun sc listed => Nat.lt_of_lt_of_le (bounded sc listed) prefixGrowth, ?_⟩
      intro held storedFragment stored
      have old := prefixOrigin held storedFragment stored
      exact (prefixProtected held storedFragment old).avoids bucket (pending held storedFragment old)
    · rw [prefixStopped] at matched
      cases matched

end MicroCFTA.SourcePruningEnumerationOpaqueEvent
