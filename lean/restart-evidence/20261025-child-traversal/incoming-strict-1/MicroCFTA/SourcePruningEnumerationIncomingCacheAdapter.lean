import MicroCFTA.SourcePruningEnumerationCachedIncoming

namespace MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
open EnumerationState EnumerationSchedule EnumerationCorrectness
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationIncomingNode.incomingNodeMonadList

/-- Recover a cache candidate from one original Incoming observation. -/
def adapt
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel target : Nat) (incomingScs : List EnumerationState.Suspended)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (read : EnumerationState.State Symbol Constraint) (raw : Raw) :
    Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match raw with
  | [] =>
      match read.values[target]? with
      | some (.unenumerated _oldNode oldScs) =>
        let value : EnumerationState.UVarValue Symbol :=
          .unenumerated (some 0) (incomingScs ++ oldScs)
        let core : EnumerationState.State Symbol Constraint :=
          {read with
            values := read.values.set target value
            recursionAncestry := fun other => if other = target then
              (read.expansionAncestry ++ read.recursionAncestry target).eraseDups
              else read.recursionAncestry other}
        (SourcePruningEnumerationNativeIndex.write heap indexFuel target value incomingScs []
          (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame core)
      | _ => none
  | [.ok ((), returned)] =>
      (returned.values[target]?).bind fun slotValue =>
        (SourcePruningEnumerationNativeIndex.write heap indexFuel target slotValue incomingScs []
          (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame returned)
  | _ => none

/-- A successful raw singleton supplies the candidate's exact core. -/
theorem adapt_singleton_core
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (indexFuel target : Nat) (incomingScs : List EnumerationState.Suspended)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (read returned : EnumerationState.State Symbol Constraint)
    (adapted : adapt heap indexFuel target incomingScs before read [.ok ((), returned)] = some after) :
    after.core = returned := by
  simp only [adapt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at adapted
  obtain ⟨value, _stored, cached, _written, same⟩ := adapted
  subst after
  rfl

/-- Retain one original observation and attach its optional cache candidate. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  let observed : (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint :=
    SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      beforeCaller before.core target incoming incomingScs queries
  (observed, match observed with
    | (.ok (some raw), reachedCaller, _savedQueries, read) =>
        adapt reachedCaller.checked.native.machine.heap indexFuel target incomingScs before read raw
    | _ => none)

/-- The first projection retains the original action at every fixed bound. -/
theorem erase
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel beforeCaller before
      target incoming incomingScs queries).1 =
      SourcePruningEnumerationIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        beforeCaller before.core target incoming incomingScs queries := by
  rfl

/-- Genuine initial inputs produce the original result and its completed cache. -/
theorem complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller width)
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (target : Nat) (incoming : Node)
    (incomingScs : List EnumerationState.Suspended) (memos : Memos) (roots : Nat → Nat)
    (initial : Context formulas solver inventory beforeCaller memos)
    (storage : StorageValid before.core)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (root : IsRoot before.core.representatives target)
    (pending : EnumerationCompleteness.PendingAt before.core target)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (bounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (ranges : match before.core.values[target]? with
      | some (.unenumerated (some oldHandle) _) =>
          match lookupNode beforeCaller.checked.native.machine.heap oldHandle with
          | some old => SourceCurrentAllocatedNativeRequestBounds.WordRanges
              (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain incoming old))
              beforeCaller.checked
          | none => True
      | _ => True) :
    ∃ (r n p h k : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
      (read : EnumerationState.State Symbol Constraint) (afterCaller : Caller width)
      (savedQueries : Queries) (final : Memos) (next : Inventory) (replacement : Node) (handle : Nat)
      (after : EnumerationExpandableIndex.Cached Symbol Constraint),
      (∀ extra, ExceptT.run (getValue (r + extra) target before.core) =
        [.ok (.unenumerated oldNode oldScs, read)]) ∧
      EnumerationCompressionFrame.Frame before.core read ∧
      (∀ extra extraNative P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationIncomingNode.run checkEmpty (r + extra) (n + extraNative) P H
          beforeCaller before.core target incoming incomingScs memos.query =
          (.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
            afterCaller, savedQueries, read)) ∧
      ExceptT.run ((do
        setValue target (.unenumerated (some handle) (incomingScs ++ oldScs))
        inheritAncestry target) read) = [.ok ((), after.core)] ∧
      after.core = {read with
        values := read.values.set target (.unenumerated (some handle) (incomingScs ++ oldScs))
        recursionAncestry := fun other => if other = target then
          (read.expansionAncestry ++ read.recursionAncestry target).eraseDups else read.recursionAncestry other} ∧
      after.core.values[target]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      Cache.Extends memos.unfolding final.unfolding ∧
      Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
      encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
      (∀ extra, (SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
        (k + extra) target (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
        (EnumerationExpandableIndex.frame read before)).map (EnumerationExpandableIndex.frame after.core) = some after) ∧
      (∀ extraIndex, adapt afterCaller.checked.native.machine.heap (k + extraIndex) target
        incomingScs before read (if replacement = .empty then [] else [.ok ((), after.core)]) = some after) ∧
      (∀ extra extraNative P H extraIndex, p ≤ P → h ≤ H →
        run checkEmpty (r + extra) (n + extraNative) P H (k + extraIndex)
          beforeCaller before target incoming incomingScs memos.query =
          ((.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
            afterCaller, savedQueries, read), some after)) ∧
      after.core.counter = before.core.counter ∧ after.core.representatives = read.representatives ∧
      Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      after.waiting = EnumerationCanonicalWaiting.count roots 1 incomingScs before.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      after.expandable = (fun slot => if slot = target then
        !(MergedOrdinaryHeight.recursiveBoundary replacement && (incomingScs ++ oldScs).isEmpty)
        else before.expandable slot) ∧
      (oldNode = none → replacement = incoming ∧ afterCaller = beforeCaller ∧
        savedQueries = memos.query ∧ final = memos ∧ next = inventory) ∧
      (∀ oldHandle, oldNode = some oldHandle →
        ∃ (old query : Node) (queried : Checked width),
          lookupNode beforeCaller.checked.native.machine.heap oldHandle = some old ∧
          next.source = beforeCaller.checked.native.machine.heap ∧ next.roots = inventory.roots ++ [incoming, old] ∧
          SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old beforeCaller.checked query queried memos ∧
          (∀ ambient term,
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
              InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
          (checkEmpty = false → replacement = query ∧
            afterCaller = SourceCurrentAllocatedPartialState.advance beforeCaller queried beforeCaller.fourth beforeCaller.merge ∧
            final = memos)) := by
  obtain ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present⟩ :=
      SourcePruningEnumerationCachedIncoming.complete formulas solver inventory beforeCaller before
        checkEmpty target incoming incomingScs memos roots initial storage realized paths counts flags
        root pending available closed bounded ranges
  obtain ⟨found, lookup, oldStored, _readSame⟩ :=
    (getValue_success r target before.core read (.unenumerated oldNode oldScs)).mp (by
      unfold Success
      rw [show ExceptT.run (getValue r target before.core) =
        [.ok (.unenumerated oldNode oldScs, read)] from
          by simpa only [Nat.add_zero] using reading 0]
      exact List.mem_singleton_self _)
  have foundTarget : found.representative = target := by
    obtain ⟨rootSize, rootPath⟩ := root
    exact (UnionFind.reaches_unique
      (UnionFind.findRoot_correct r before.core.representatives target found lookup).1 rootPath).1
  have readStored : read.values[target]? = some (.unenumerated oldNode oldScs) := by
    rw [frame.values, ← foundTarget]
    exact oldStored
  have adapted : ∀ extraIndex,
      adapt afterCaller.checked.native.machine.heap (k + extraIndex) target incomingScs before read
        (if replacement = .empty then [] else [.ok ((), after.core)]) = some after := by
    intro extraIndex
    by_cases empty : replacement = .empty
    ·
      have handleZero : handle = 0 := by
        simpa only [empty, encodeNode, Option.some.injEq] using encoded.symm
      simp only [ite_eq_left empty, adapt, readStored]
      simpa only [handleZero, afterSame] using cacheRun extraIndex
    · simp only [ite_eq_right empty, adapt, afterStored, Option.bind_some]
      exact cacheRun extraIndex
  refine ⟨r, n, p, h, k, oldNode, oldScs, read, afterCaller, savedQueries, final, next,
    replacement, handle, after, reading, frame, originalRun, writePrefix, afterSame, afterStored,
    afterStorage, afterRealized, post, querySame, unfolding, replacementAvailable,
    replacementClosed, encoded, decoded, cacheRun, adapted, ?_, afterCounter, afterRepresentatives,
    afterPaths, afterCounts, waiting, flagsAfter, expandableAfter, optional, present⟩
  intro extra extraNative P H extraIndex enoughP enoughH
  simp only [run, originalRun extra extraNative P H enoughP enoughH, adapted extraIndex]

end MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter
