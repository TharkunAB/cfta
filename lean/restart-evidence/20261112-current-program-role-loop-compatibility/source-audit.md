# Current startup and actual Program-role state updates
Generated 2026-11-12T21:19:55.607516+01:00.

Base `7401c26c1ffcf8b9db3b6925b667015a0552e8a0`. Integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`.

Eight new strict-checked modules. All earlier Audit bytes remain. These are startup and local transition laws. The full shallow driver induction and actual eager resource/role induction remain open. No satisfying type model or full default Haskell correspondence is claimed.

## SourceSynthesisCurrentProgramSlotsInitialization
SHA256 `9374295e5b120f35eb64db19a6031cf054f39b92850bbdb6ecb5530239f29bd7`. Lines 71.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisCurrentProgramSlotsInitialization.accepted"
]
```

Public statement:

```lean
theorem accepted (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (width : Nat) (initial : Cache.State Key) (valid : Cache.Valid initial)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ fields cache value heap,
      ∃ built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap,
      SourceEqualityOriginalAllocationPreparation.Receipt (guards (ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap ∧
      Context formulas solver (SourceCurrentAllocatedPartialInitialization.inventory (ordinarySymbols expression) value heap built)
        (SourceCurrentAllocatedPartialInitialization.caller width cache heap) SourceCurrentAllocatedPartialInitialization.globals ∧
      Facts heap ∧ Available heap value ∧
      SourceSynthesisProgramBuildRolesGeneric.ProgramValue literal value ∧
      Grows empty heap ∧ Cache.Extends (empty : State Symbol Guard).nodes.issued heap.nodes.issued ∧
      SourceEqualityAnnotationHeap.Heap
        (Derived (alphabet (encodedLibrary lib)) top SourceEqualityPCSNativeEdge.conjoin) heap ∧
      ∃ identity, SourceCurrentAllocatedPartialInitialization.emptyValue cache = .live identity [] ∧
        SourceEqualityConstraintAllocation.Ready
          (SourceCurrentAllocatedPartialInitialization.caller width cache heap).checked.operations.constraints
          (.live identity []) ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value ∧
        ValueFields (Origin (encodedLibrary lib)) literal value ∧
        ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
          ProgramSlots (Origin (encodedLibrary lib)) literal heap
            (EnumerationState.initial handle) (fun uv => uv = 0) := by
```

## SourceSynthesisProgramRolesChildRetained
SHA256 `69b820a95d09eb3e304909d4fdb2131af0b33a7532e50c5c415dc64096b62bec`. Lines 89.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesChildRetained.program_child_retained"
]
```

Public statement:

```lean
theorem program_child_retained
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap incoming) (closed : incoming.free = [])
    (fields : ValueFields valid literal incoming)
    (pathScope : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (roles : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    ∃ handle, (encodeNode incoming = some handle ∧ lookupNode heap handle = some incoming ∧
      fragment = .hole before.counter ∧
      after = {allocated (some handle) before with values :=
        (allocated (some handle) before).values.set before.counter (.unenumerated (some handle) scs)} ∧
      Safe after ∧ ProgramSlots valid literal heap after (fun uv => marked uv ∨ uv = before.counter)) ∧
      (∀ uv, marked uv → EnumerationDriver.Protected uv before after) ∧
      (∀ retained : List Suspended,
        (∀ sc ∈ retained, sc.var < before.counter) →
        (∀ uv, marked uv → Avoids before.representatives uv retained) →
        (∀ sc ∈ retained, sc.var < after.counter) ∧
        ∀ uv, marked uv ∨ uv = before.counter → Avoids after.representatives uv retained) := by
```

## SourceSynthesisProgramRolesClassAllocation
SHA256 `13bbb13d1a683d2567c320fdb860c9005a67accb19ab2aa363ff4622c6565875`. Lines 140.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots"
]
```

Public statement:

```lean
theorem suspendMany_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (tries : List EqualityTrie.Trie)
    (before after : Cached) (own : List Suspended) (marked : Nat → Prop)
    (safe : Safe before.core) (slots : ProgramSlots valid literal heap before.core marked)
    (observed : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = some (own, after)) :
    own = suspendedVars before.core.counter tries ∧
      after = ⟨suspendedState tries.length before.core, before.expandable, before.waiting⟩ ∧
      ExceptT.run ((tries.mapM (EnumerationState.suspend : EqualityTrie.Trie → EnumerateM Symbol Constraint Suspended)) before.core) = [.ok (own, after.core)] ∧
      after.core.counter = before.core.counter + tries.length ∧
      after.core.representatives = before.core.representatives ∧
      Safe after.core ∧ ProgramSlots valid literal heap after.core marked ∧
      (∀ uv, marked uv → Protected uv before.core after.core ∧ Avoids after.core.representatives uv own) ∧
      ∀ offset, offset < tries.length →
        ¬marked (before.core.counter + offset) ∧
        after.core.values[before.core.counter + offset]? = some (.unenumerated none []) ∧
        IsRoot after.core.representatives (before.core.counter + offset) := by
```

## SourceSynthesisProgramRolesSelectedPrefix
SHA256 `f1b0936b85cb4e437d24c3509380ed04ee24f119b8c56f1af3a8783e74bc4cff`. Lines 214.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix.selected_prefix_program_slots"
]
```

Public statement:

```lean
theorem selected_prefix_program_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (heap : NativeHeap) (before readAfter entry : Core)
    (readFuel uv oldHandle : Nat) (scs : List Suspended)
    (ready : SourceEqualityRequiredCache.Ready heap) (realized : PendingRealized heap before)
    (total : UnionFind.Total before.representatives)
    (observed : Success (getValue readFuel uv) before (.unenumerated (some oldHandle) scs) readAfter)
    (entered : Frame readAfter entry) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked) :
    (∃ (oldValue result : Node) (nativeFuel : Nat) (nextHeap : NativeHeap) (newHandle : Nat),
      lookupNode heap oldHandle = some oldValue ∧ encodeNode oldValue = some oldHandle ∧
      Available heap oldValue ∧ oldValue.free = [] ∧
      SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap = .done result nextHeap ∧
      (∀ extra, SourcePruningOuterNarrow.narrow holeKey fits admits metadata (nativeFuel + extra) uv oldValue heap =
        .done result nextHeap) ∧
      SourceEqualityRequiredCache.Keeps heap nextHeap ∧ Available nextHeap result ∧ result.free = [] ∧
      encodeNode result = some newHandle ∧ lookupNode nextHeap newHandle = some result ∧
      lookupNode nextHeap oldHandle = some oldValue ∧
      Frame before readAfter ∧ PendingRealized nextHeap entry ∧
      (EnumerationReferences.PendingReferences before → EnumerationReferences.PendingReferences entry) ∧
      (∀ held, EnumerationReferences.IncomingAvoid held before → EnumerationReferences.IncomingAvoid held entry) ∧
      (result ≠ .empty → oldValue ≠ .empty) ∧
      ProgramSlots valid literal nextHeap entry marked ∧
      (result = .empty → ∀ representativeFuel,
        prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
          .done (result, some (reject : EnumerateM Symbol Constraint Unit)) nextHeap ∧
        ¬ ∃ final : Core, Success (reject : EnumerateM Symbol Constraint Unit) entry () final) ∧
      (result ≠ .empty → newHandle = oldHandle →
        result = oldValue ∧
        (∀ representativeFuel,
          prepare holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap =
            .done (result, some (pure () : EnumerateM Symbol Constraint Unit)) nextHeap) ∧
        Success (pure () : EnumerateM Symbol Constraint Unit) entry () entry) ∧
      (result ≠ .empty → newHandle ≠ oldHandle →
        ∃ (root size rereadFuel : Nat) (rereadAfter final : Core),
          UnionFind.Reaches before.representatives uv root size ∧
          Success (representative rereadFuel uv) entry root rereadAfter ∧
          Frame entry rereadAfter ∧ Frame before rereadAfter ∧
          rereadAfter.values[root]? = some (.unenumerated (some oldHandle) scs) ∧
          root < rereadAfter.values.length ∧ PendingRealized nextHeap rereadAfter ∧
          Success (setValue root (.unenumerated (some newHandle) scs)) rereadAfter () final ∧
          final = {rereadAfter with values := rereadAfter.values.set root (.unenumerated (some newHandle) scs)} ∧
          final.values[root]? = some (.unenumerated (some newHandle) scs) ∧ PendingRealized nextHeap final ∧
          (EnumerationReferences.PendingReferences before → EnumerationReferences.PendingReferences final) ∧
          (∀ held, EnumerationReferences.IncomingAvoid held before → EnumerationReferences.IncomingAvoid held final) ∧
          prepare holeKey fits admits metadata nativeFuel rereadFuel uv oldHandle scs oldValue heap =
            .done (result, some ((representative rereadFuel uv >>= fun selected =>
              setValue selected (.unenumerated (some newHandle) scs)) : EnumerateM Symbol Constraint Unit)) nextHeap ∧
          Success (representative rereadFuel uv >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) scs)) entry () final ∧
          ProgramSlots valid literal nextHeap final marked)) ∧
    (∀ (target handle : Nat) (bucket : List Suspended) (value : Node) (after : Core),
      entry.values[target]? = some (.unenumerated (some handle) bucket) →
      lookupNode heap handle = some value → MergedOrdinaryHeight.recursiveBoundary value = true →
      Success (setValue target (.unenumerated (some handle) [])) entry () after →
      ¬marked target ∧ after = {entry with values := entry.values.set target (.unenumerated (some handle) [])} ∧
      ProgramSlots valid literal heap after marked) := by
```

## SourceSynthesisProgramRolesSharedTerminal
SHA256 `ef65805dd24b5fa9a192676b87e5f07ec68c5c33dff5694daadb79becf3f02ca`. Lines 255.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesSharedTerminal.terminal_resources_program_slots"
]
```

Public statement:

```lean
theorem terminal_resources_program_slots
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2))
    (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (checkEmpty : Bool) (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (roots : Nat → Nat) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (safe : Safe before.core) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
      beforeCaller.checked.native.machine.heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ first :: rest, sc.var < before.core.counter)
    (pending : InputsPending before.core (first :: rest))
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before.core)
    (nonempty : incoming ≠ .empty)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (incomingBounded : ∀ sc ∈ incomingScs, sc.var < before.core.counter)
    (fits : Fits seed.2 beforeCaller.checked)
    (reserved : Reserved bits seed ((first :: rest).length + 1))
    (known : Heap (fun guard => guard ∈ seed.1) beforeCaller.checked.native.machine.heap)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal beforeCaller.checked.native.machine.heap before.core marked)
    (terminalAvoids : ∀ uv, marked uv → Avoids before.core.representatives uv (first :: rest))
    (incomingAvoids : ∀ uv, marked uv → Avoids before.core.representatives uv incomingScs) :
    ∃ (r n p h k : Nat) (recorded : List Nat) (winner : Nat)
      (joined : EnumerationExpandableIndex.Cached Symbol Constraint)
      (foldRows : List (Unit × EnumerationExpandableIndex.Cached Symbol Constraint))
      (foldCaller : Caller (bits + 2)) (foldQueries : Queries) (foldFinal : Memos) (foldInventory : Inventory)
      (folded : EnumerationExpandableIndex.Cached Symbol Constraint)
      (raw : TerminalRaw) (afterCaller : Caller (bits + 2)) (outer : EnumerationState.State Symbol Constraint)
      (savedQueries : Queries) (final : Memos) (next : Inventory)
      (resultCache : EnumerationExpandableIndex.Cached Symbol Constraint),
      (
      (∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (r + extra) first rest before.waiting before.core) =
        [.ok ((recorded, winner, joined.waiting), joined.core)]) ∧
      recorded = (first :: rest).map (fun sc => roots sc.var) ∧ winner ∈ recorded ∧
      joined.waiting = EnumerationCanonicalWaiting.moveMany winner
        (EnumerationBuilderCaches.canonicalIds (recorded.filter (fun key => key != winner))) before.waiting ∧
      joined.core = {before.core with representatives := joined.core.representatives} ∧
      joined.expandable = before.expandable ∧
      Roots joined.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        joined.core.values joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        beforeCaller.checked.native.machine.heap
        ((joined.core.values[slot]?).getD .eliminated) = some (joined.expandable slot)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        fold checkEmpty (n + extra) P H recorded
          beforeCaller joined winner memos.query =
          ((.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core), some folded)) ∧
      (∀ extra P H, p ≤ P → h ≤ H →
        rawFold checkEmpty (n + extra) P H recorded
          beforeCaller joined.core winner memos.query =
          (.ok (some (foldRows.map (fun row => .ok (row.1, row.2.core)))),
            foldCaller, foldQueries, folded.core)) ∧
      (foldRows = [] ∨ foldRows = [((), folded)]) ∧
      Post formulas solver foldInventory beforeCaller foldCaller foldFinal ∧ foldFinal.query = foldQueries ∧
      folded.core.counter = joined.core.counter ∧ folded.core.representatives = joined.core.representatives ∧
      Roots folded.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      StorageValid folded.core ∧ PendingRealized foldCaller.checked.native.machine.heap folded.core ∧
      IsRoot folded.core.representatives winner ∧ PendingAt folded.core winner ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        folded.core.values folded.waiting ∧ folded.waiting = joined.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        foldCaller.checked.native.machine.heap
        ((folded.core.values[slot]?).getD .eliminated) = some (folded.expandable slot)) ∧
      (∀ (slot : Nat), joined.core.values[slot]? = some .eliminated →
        folded.core.values[slot]? = some .eliminated) ∧
      (foldRows = [((), folded)] → ∀ source ∈ recorded, source ≠ winner →
        folded.core.values[source]? = some .eliminated) ∧
      (∀ (slot : Nat), slot ∉ recorded → folded.core.values[slot]? = before.core.values[slot]?) ∧
      (foldRows = [((), folded)] → Safe folded.core) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        folded.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) ∧
      (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty (r + extraRepresentative) (n + extraNative) P H
          first rest before.waiting beforeCaller before.core incoming incomingScs memos.query =
          (.ok (some raw), afterCaller, savedQueries, outer, joined.waiting)) ∧
      Post formulas solver next beforeCaller afterCaller final ∧ final.query = savedQueries ∧
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        run checkEmpty (r + extraRepresentative) (n + extraNative) P H (k + extraIndex)
          first rest beforeCaller before incoming incomingScs memos.query =
          ((.ok (some raw), afterCaller, savedQueries, outer, joined.waiting), some resultCache)) ∧
      resultCache.core.counter = before.core.counter ∧
      Roots resultCache.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
      StorageValid resultCache.core ∧ PendingRealized afterCaller.checked.native.machine.heap resultCache.core ∧
      EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
        resultCache.core.values resultCache.waiting ∧
      (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
        afterCaller.checked.native.machine.heap
        ((resultCache.core.values[slot]?).getD .eliminated) = some (resultCache.expandable slot)) ∧
      (∀ (slot : Nat), slot ∉ recorded → resultCache.core.values[slot]? = before.core.values[slot]?) ∧
      (raw ≠ [] → Safe resultCache.core) ∧
      (∀ (held : Nat), IsRoot before.core.representatives held →
        Avoids before.core.representatives held (first :: rest) →
        EnumerationDriver.Protected held before.core resultCache.core) ∧
      (∀ (slot : Nat) (fragment : Fragments.Fragment Symbol),
        resultCache.core.values[slot]? = some (.enumerated fragment) →
        before.core.values[slot]? = some (.enumerated fragment)) ∧
      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
        EnumerationReferences.InputsAllowed allowed incomingScs →
        EnumerationReferences.ReferencesAllowed allowed resultCache.core) ∧
      (foldRows = [] → resultCache = folded) ∧
      (foldRows = [] → raw = [] ∧ afterCaller = foldCaller ∧ savedQueries = foldQueries ∧
        outer = folded.core ∧ final = foldFinal ∧ next = foldInventory) ∧
      (foldRows = [((), folded)] →
        ∃ (incomingK : Nat) (oldNode : Option Nat) (oldScs : List EnumerationState.Suspended)
          (read : EnumerationState.State Symbol Constraint)
          (after : EnumerationExpandableIndex.Cached Symbol Constraint) (replacement : Node) (handle : Nat),
          after = resultCache ∧ outer = read ∧
          (∀ extra, ExceptT.run (getValue (r + extra) winner folded.core) =
            [.ok (.unenumerated oldNode oldScs, read)]) ∧
          EnumerationCompressionFrame.Frame folded.core read ∧
          (∀ extraRepresentative extraNative P H, p ≤ P → h ≤ H →
            SourcePruningEnumerationSharedIncomingNode.run checkEmpty (r + extraRepresentative) (n + extraNative) P H
              foldCaller folded.core winner incoming incomingScs foldQueries =
              (.ok (some (if replacement = .empty then [] else [.ok ((), after.core)])),
                afterCaller, savedQueries, read)) ∧
          ExceptT.run ((do
            setValue winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            inheritAncestry winner) read) = [.ok ((), after.core)] ∧
          after.core = {read with
            values := read.values.set winner (.unenumerated (some handle) (incomingScs ++ oldScs))
            recursionAncestry := fun other => if other = winner then
              (read.expansionAncestry ++ read.recursionAncestry winner).eraseDups else read.recursionAncestry other} ∧
          after.core.values[winner]? = some (.unenumerated (some handle) (incomingScs ++ oldScs)) ∧
          StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
          Post formulas solver next foldCaller afterCaller final ∧
          Cache.Extends foldFinal.unfolding final.unfolding ∧
          (∀ extra, (SourcePruningEnumerationNativeIndex.write afterCaller.checked.native.machine.heap
            (incomingK + extra) winner (.unenumerated (some handle) (incomingScs ++ oldScs)) incomingScs []
            (EnumerationExpandableIndex.frame read folded)).map (EnumerationExpandableIndex.frame after.core) = some after) ∧
          after.core.counter = folded.core.counter ∧ after.core.representatives = read.representatives ∧
          Roots after.core.representatives (EnumerationCanonicalUnion.mergedRoots roots recorded winner) ∧
          EnumerationCanonicalWaiting.Correct (EnumerationCanonicalUnion.mergedRoots roots recorded winner)
            after.core.values after.waiting ∧
          after.waiting = EnumerationCanonicalWaiting.count
            (EnumerationCanonicalUnion.mergedRoots roots recorded winner) 1 incomingScs joined.waiting ∧
          (∀ (slot : Nat), SourcePruningEnumerationNativeIndex.candidate
            afterCaller.checked.native.machine.heap
            ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
          after.expandable = (fun slot => if slot = winner then
            !(MergedOrdinaryHeight.recursiveBoundary replacement && (incomingScs ++ oldScs).isEmpty)
            else folded.expandable slot) ∧
          raw = (if replacement = .empty then [] else [.ok (.hole winner, after.core)]) ∧
          FragmentBound after.core.counter (.hole winner : Fragments.Fragment Symbol) ∧
          Available afterCaller.checked.native.machine.heap replacement ∧ replacement.free = [] ∧
          encodeNode replacement = some handle ∧ lookupNode afterCaller.checked.native.machine.heap handle = some replacement ∧
          (oldNode = none → replacement = incoming ∧ afterCaller = foldCaller ∧
            savedQueries = foldQueries ∧ final = foldFinal ∧ next = foldInventory) ∧
          (∀ oldHandle, oldNode = some oldHandle →
            ∃ (old query : Node) (queried : Checked (bits + 2)),
              lookupNode foldCaller.checked.native.machine.heap oldHandle = some old ∧
              next.source = foldCaller.checked.native.machine.heap ∧ next.roots = foldInventory.roots ++ [incoming, old] ∧
              SourceCurrentAllocatedTargetQuery.Receipt formulas solver next incoming old foldCaller.checked query queried foldFinal ∧
              (∀ ambient term,
                InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient replacement term ↔
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient incoming term ∧
                  InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient old term) ∧
              (checkEmpty = false → replacement = query ∧
                afterCaller = SourceCurrentAllocatedPartialState.advance foldCaller queried foldCaller.fourth foldCaller.merge ∧
                final = foldFinal))) ∧
      Fits (advance seed (first :: rest).length).2 foldCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed (first :: rest).length).1) foldCaller.checked.native.machine.heap ∧
      Fits (advance seed ((first :: rest).length + 1)).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (advance seed ((first :: rest).length + 1)).1) afterCaller.checked.native.machine.heap) ∧
      ProgramSlots valid literal afterCaller.checked.native.machine.heap resultCache.core marked := by
```

## SourceSynthesisProgramRolesUnmarkedChild
SHA256 `69dcc7572735d0cd22a09392f95107c2541d12e843495699a2a32a256ae70425`. Lines 61.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesUnmarkedChild.prepared_child_program_slots"
]
```

Public statement:

```lean
theorem prepared_child_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (incoming : Node) (scs : List Suspended)
    (before after : Core) (marked : Nat → Prop)
    (safe : Safe before) (slots : ProgramSlots valid literal heap before marked)
    (bounded : ∀ sc ∈ scs, sc.var < before.counter)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv scs)
    (action : EnumerateM Symbol Constraint (Fragment Symbol)) (fragment : Fragment Symbol)
    (prepared : SourcePruningEnumerationShallowChild.prepareChild scs incoming = some action)
    (actual : Success action before fragment after) :
    Safe after ∧ EnumeratedOrigin before after ∧
      (∀ held, held < before.counter → IsRoot before.representatives held →
        Protected held before after) ∧
      ProgramSlots valid literal heap after marked := by
```

## SourceSynthesisProgramRolesUnmarkedFinalize
SHA256 `8b08684f5e1a7503168033a1b85be42bd5df841b53d65a29532f054d4fd13bd2`. Lines 75.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesUnmarkedFinalize.complete_unmarked_program_slots"
]
```

Public statement:

```lean
theorem complete_unmarked_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (heap : NativeHeap) (before : Cached)
    (target : Nat) (fragment : Fragment) (old : UVarValue Symbol)
    (stored : before.core.values[target]? = some old)
    (roots : Nat → Nat) (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (storage : StorageValid before.core)
    (bounded : FragmentBound before.core.counter fragment)
    (realized : PendingRealized heap before.core)
    (slots : ProgramSlots valid literal heap before.core marked)
    (unmarked : ¬marked target) :
    ∃ (fuel : Nat) (after : Cached),
      (∀ extra, SourcePruningEnumerationFinalize.run heap (fuel + extra) target fragment before = some after) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish (EnumGuard := Constraint) target fragment before.core) =
        [.ok (fragment, after.core)] ∧
      after.core = {before.core with
        values := before.core.values.set target (.enumerated fragment),
        expansionAncestry := []} ∧
      after.core.values[target]? = some (.enumerated fragment) ∧
      after.expandable = (fun slot => if slot = target then false else before.expandable slot) ∧
      after.waiting = EnumerationCanonicalWaiting.count roots (-1) (references old) before.waiting ∧
      Roots after.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      StorageValid after.core ∧ PendingRealized heap after.core ∧
      (Safe before.core → IsRoot before.core.representatives target → Safe after.core) ∧
      ProgramSlots valid literal heap after.core marked ∧
      ∀ held, marked held → Protected held before.core after.core := by
```

## SourceSynthesisProgramRolesUnmarkedWrite
SHA256 `71e0c22ba71e4956527d2cfc0ec9c26ea1d828a74a8c66d509b367cbf6fcc980`. Lines 50.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite.setValue_unmarked_program_slots"
]
```

Public statement:

```lean
theorem setValue_unmarked_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol)
    (heap : NativeHeap) (before after : Core) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal heap before marked)
    (target : Nat) (unmarked : ¬marked target) (payload : UVarValue Symbol)
    (avoids : ∀ held, marked held → Avoids before.representatives held (references payload))
    (written : Success (EnumerationState.setValue target payload) before () after) :
    after = {before with values := before.values.set target payload} ∧
      ProgramSlots valid literal heap after marked ∧
      ∀ held, marked held → Protected held before after := by
```

## Operational notes and frozen-header repairs

The following notes distinguish the initial syntax drafts from the final checked sources. No repair adds a semantic premise or drops an existing resource field.

### current-program-slots-initialization-note.md

# Current initial Program slots at the same native build

Frozen source: SourceSynthesisCurrentProgramSlotsInitialization.lean, 71 lines.
SHA256: 9374295e5b120f35eb64db19a6031cf054f39b92850bbdb6ecb5530239f29bd7
One public law: accepted.
Frozen header SHA256: 704454b16e846716f1f52c96be24faf88b67781e15af513a07e3a3f456080c6e.
The public header is unchanged after proof construction.

The theorem invokes CurrentCallerInitialization.accepted ONCE and retains its
ENTIRE fields/cache/value/heap/built tuple, preparation Receipt, conjunction
Fields, full caller Context, Facts, Available, ProgramValue, native growth,
issued history, full Derived(alphabet(encodedLibrary lib)) annotation Heap,
emptyValue identity/equality/readiness, closed value, and Original certificate.
All input assumptions are the same as the old initializer: actual current
source .ok, width, current cache Valid, formulas/solver and the same instances.
No second initializer, build producer, worker, model or Room is invoked.

On the SAME actual built value/heap, current_root_fields derives ValueFields.
Its validity predicate is Origin(encodedLibrary lib), the existing Derived
closure of the actual encoded library Type pool. It is not arbitrary supplied
guard validity. The original full-alphabet Heap predicate remains unchanged.
available_readback uses the SAME Facts.coherent/Available/closed certificates
to derive the exact model encodeNode handle and lookupNode readback.
initial_program_slots then derives roles for EnumerationState.initial handle
with the literal mark predicate uv=0. ValueFields, handle encoding/readback
and complete ProgramSlots are all appended to that same initialization tuple.

This result does not assert native-handle extraction to Haskell NodeId,
execute a checked/native/enumeration worker, establish a completed Packet,
prove all reached driver roles, or establish enumeration termination.
Unverified runtime draft; ROOT alone performs strict checking/publication.
No compiler, repository, Git, Haskell, root docs, or evidence changes.


### program-roles-child-retained-note.md

# R254 Retained buckets after the actual Program child event

Status: FROZEN SOURCE ONLY. ROOT compilation is pending.

Source: SourceSynthesisProgramRolesChildRetained.lean, 89 lines.
SHA256: 69b820a95d09eb3e304909d4fdb2131af0b33a7532e50c5c415dc64096b62bec
Public header: program-roles-child-retained-header.txt, 47 lines.
Header SHA256: c3e0d3150688fa54c0cacae0f8c9232850366b19af7a76f4f98d4d5cbf3925e7

Namespace: MicroCFTA.SourceSynthesisProgramRolesChildRetained.
Public law: program_child_retained.
No worker, observer datatype or invariant type is added.

The proof calls program_child_role_step once and retains its entire result
predicate in parentheses. That receipt includes the actual encoded handle,
native readback, returned fresh-hole fragment, exact allocated-and-written
Core, reached Safe, and complete ProgramSlots for old marks or the fresh root.
The operation, native heap, prepared action and actual Success stay fixed.

The appended protection fact covers every old marked raw root. The proof
uses the actual fresh write shape and allocation_protected. Each old mark
lies below the original counter, so the fresh write retains its exact payload.
The literal child state has the same union-find forest as the original state.
It therefore retains old roots and their complete classes.

The appended universal bucket observer takes a current retained bucket after
the producer output. Its inputs are a bound below BEFOREcounter and Avoids
for every OLD mark in the BEFORE forest. It derives the reached bound and
Avoids for ALL extended marks in the AFTER forest. The old case uses the
unchanged forest. In the fresh case, current Safe.forest and outside_class
exclude any reference below BEFOREcounter from the fresh singleton class.
No desired after-bucket property is assumed. Actual EdgeInputs bounds can
instantiate this observer for later sibling buckets.

All public inputs match the existing child role law. No new role, retained
bucket, future callback state, projection, model, rank or completion supplier
is added. The conclusion observes one actual successful prepared shallow
child event. The general child loop, native heap transport between events,
ordinary eager descent, whole-source completion and source lazy demand remain
separate. No Haskell change or defect claim was made.

Exact dependencies:
- ProgramChildRoleStep.program_child_role_step:44.
- EnumerationDriver.allocation_protected:57.
- EnumerationCorrectness.outside_class:672.
- EnumerationState.allocated:569.


### program-roles-class-allocation-note.md

# Actual selected-prefix equality-class allocation

Frozen source: SourceSynthesisProgramRolesClassAllocation.lean, 136 lines.
SHA256: 80a33ba7dda20a2889c3d9dda650725e59fbfcf36fe356c6b23f6c6a801d1d87
One public law: suspendMany_program_slots.
Frozen header SHA256: c0a8bf782cdb037a27e406dd335636e82aca4efe9e8975975bac7e4140c76924.
The raw mapM action has explicit Symbol/Constraint parameters in both occurrences.

Literal action: SourcePruningEnumerationCachedOwn.suspendMany heap tries before.
CachedOwn.prepare calls this exact action after the actual guard projection.
Each step calls CachedChild.allocate heap none. It does not perform a separate
Type or Program write. allocated retains its real recursionAncestry update.
The full returned Cached shape includes that complete suspendedState endpoint.
The law also retains the corresponding exact raw mapM suspend singleton receipt.

Current inputs are Safe, ProgramSlots, and the SAME actual successful cached observation.
No native Ready/readback/heap-validity/flags gate, desired prepared Packet,
model, or after-role provider is supplied. The mark predicate is unchanged.
Existing suspendMany_core/vars identify the same complete core and own list.
A small private cache observer retains the literal unchanged flags/waiting fields.
Existing suspension_safe/protected/allowed retain old roles and IncomingAvoid.
Existing fresh_avoids proves separation from every marked old root using CURRENT
Safe forest bounds and the unchanged actual forest, not raw IDs alone.
Every fresh offset is unmarked, stores pure unenumerated none [], and is a root.
A private value-list identity exposes the exact appended replicate for that lookup.

The theorem does not mark equality slots as Program occurrences.
It does not assert that an arbitrary supplied cached flag function is correct;
its exact preservation lets the real caller reuse its existing index invariants.
It does not prove selected-prefix success, pending guard preparation, Type dispatch,
all reached role histories, decoder Projection, or whole enumeration termination.
Unverified runtime draft; ROOT alone performs strict checking/publication.
No compiler, repository, Git, Haskell, root docs, or evidence changes.

First strict check: two elaboration failures in the polymorphic mapM action.
The following incomplete-proof diagnostics were cascades from those failures.
The repair pins EnumerationState.suspend to the same Symbol and Constraint.
The header has the same inputs, outputs, action and operational singleton receipt.
No premise or execution gate is added. No proof body changes are made beyond
that same action annotation in the local raw receipt.
Original source SHA256:
d8bb22b1d968b4135e4737910bd2037fbc1a68e6dad462fa36062ba552ef8799.
Original header SHA256:
c0781c4215897bfbe94b2acc40e093cc9cab8f37bfaaeaabdfe3f693e1a08c60.
The original source, header, note and strict log remain preserved.
Repaired runtime source awaits ROOT strict checking.

ROOT parser correction: local Symbol notation prevents the named-argument spelling. Both occurrences now use the same suspend action with an explicit Trie-to-EnumerateM type. Old named-argument source retained. No operational change or new premise.

ROOT fixed the remaining concrete instance scope: add the same singleton/flatMap Monad List that the existing suspension producer uses. This is a local concrete instance, not a public assumption. The corrected typed public declaration remains unchanged.


### program-roles-selected-prefix-note.md

# Selected-prefix Program roles

Source: `SourceSynthesisProgramRolesSelectedPrefix.lean`. Frozen runtime draft. No compiler was run by this owner.
Source size: 214 lines.
Source SHA256: `f1b0936b85cb4e437d24c3509380ed04ee24f119b8c56f1af3a8783e74bc4cff`.
Frozen public-header SHA256: `c6f6c8ba95755fcd89a77e0ab9e427f30c8d7591c54b7e2524831acf2575b658`.
The initial header stays in the saved -header.txt file.
Corrected public-header SHA256: `0af8d6dce04a6d620f1a4baec402b6b1bc31b0866a3c1df0ee66d1a987dafb95`.
The only header change removes the invalid explicit EnumGuard argument from
prepare. A mechanical comparison confirms this exact one-spelling difference.
The action, premises, receipt, and endpoints are unchanged.

Public law: `SourceSynthesisProgramRolesSelectedPrefix.selected_prefix_program_slots`.
The only additions to the existing native producer inputs are `marked` and the
initial `ProgramSlots`. The native inputs remain Ready, PendingRealized, Total,
the actual successful getValue observation, and the actual compression Frame.

The first conjunct calls `Action.prepare_pending_complete` exactly once. It
retains every original lookup, encoding, availability, closedness, native run,
all-larger-native-fuel identity, Keeps, Frame, realized storage, pending history,
incoming avoidance, empty rejection, unchanged-handle action, and changed-handle
read/write/cache/action receipt. It adds ProgramSlots at the SAME native-after
entry and at the SAME final state selected by the changed-handle branch.

The second conjunct uses the actual recursive-clear store, native lookup,
recursiveBoundary result, and successful setValue at that SAME compression
entry. It derives that the target is unmarked. It returns the exact Core update
and ProgramSlots. This observer can attach to the existing Clear.complete
receipt without replacing or discarding its cache, waiting, flag, and readiness
facts. It does not invoke another native producer.

Private `narrowed_fields` handles the actual OuterNarrow exemptions and ordinary
row filtering. It derives the output fields from the original fields, current
native Ready/Available facts, direct nodeEdges, resident_edges, and the checked
HereditaryProgramFields.makeNode_fields. No after-field or after-lookup supplier
is required. Private `write_slots` only factors an exact actual store write.
Its role and reference premises are derived inside the public producer.

Imports: ProgramRolesCompression, ProgramRolesNativeHeap, EnumerationAction.
The private store observer omits the unused EdgeKey equality instance.

Scope: actual prefix narrowing/action and recursive-clear events. This is not
the whole runPrefix resource/Right-callback composition, class allocation,
non-Program child handling, driver induction, or eager Haskell traversal.
Empty results retain the actual reject action and its lack of Success. No role
claim is made about a final state of reject. No model, Projection, rank, capacity,
whole traversal completion, or original-input resource bound is added.

## Focused first-check repair

Root's first strict check failed. The full log is
`program-roles-selected-prefix-210811-failure.txt`. The initial source remains
in `SourceSynthesisProgramRolesSelectedPrefix-2a70457e.lean`.
The repair adds the same concrete singleton/flatMap local Monad List as the
source workers. It adds no caller instance gate. It fixes the action spelling,
uses the actual old-handle payload to derive suspended-reference allowance,
and lets the dependent pending constructor infer its indexed bucket.
This repaired runtime draft awaits Root's strict check. No compiler was run.

## Focused second-check repair

Root's second strict check stopped at an unconstrained EnumGuard in the header.
The log is `program-roles-selected-prefix-211327-failure.txt`.
The previous source stays in `SourceSynthesisProgramRolesSelectedPrefix-80f7679f.lean`.
The SAME changed-handle action now has the explicit result type
`EnumerateM Symbol Constraint Unit`. No operation or premise changes.
Current typed-action header SHA256: `8f1f06afc0411fe4b0b9f208b3c5c6b9326b5e0ff683c8de944103f311fad5f1`.
The mechanical comparison confirms that only this type ascription was added.


### program-roles-shared-terminal-note.md

# R254 Program roles at the shared terminal resource endpoint

Status: ROOT strict PASS, 1 public law. Source and header are frozen.

Source: SourceSynthesisProgramRolesSharedTerminal.lean, 255 lines.
SHA256: ef65805dd24b5fa9a192676b87e5f07ec68c5c33dff5694daadb79becf3f02ca
Public header: program-roles-shared-terminal-header.txt, 211 lines.
Header SHA256: 60633930169e6ac9cdc419d04d8975e7cf49337ccdbc3cce1afc11c56837bfe4

Namespace: MicroCFTA.SourceSynthesisProgramRolesSharedTerminal.
Public law: terminal_resources_program_slots.
No worker, observer, datatype or invariant type is added.

The proof calls actual terminalAdapter_complete_resources exactly once.
The entire original existential result predicate remains in parentheses.
The new conjunction adds ProgramSlots at the same resultCache.core and
same afterCaller.checked.native.machine.heap with the same marked predicate.
All original fuels, ordered prefix/fold/raw actions, caches, native callers,
query memos, full Memos, inventories, Post, guards, Fits and Heap facts remain.
Both rejected and completed branch receipts remain intact. The distinct outer
read Core remains distinct from resultCache.core.

Current extra inputs are the initial marked ProgramSlots and transient
terminal-source and incoming bucket Avoids for each marked raw root.
The original producer retains exact counter equality and resultProtects.
These facts retain each marked root, its full class and its raw payload.
Its predicate-parametric resultReferences and the actual incoming bucket
Avoids derive the reached IncomingAvoid fact through incoming_preserved.
The same actual Post.effects.keeps transports pending lookup roles with
keeps_program_slots before the retained raw payload is reused at the endpoint.
The proof derives every output role field internally from this one receipt.

The checked Prefix154 and both finish162 observers isolate component effects.
The stronger existing full terminal carrier already retains their required
protection and reference effects. Reusing that carrier avoids a second
traversal proof, independent completion witness or worker execution.
No Safe claim is made for an intermediate prefix or a rejected raw endpoint.
No final-role, after-Packet, native readback, model or completion oracle is
an input. Native callback work is outside this role conclusion.

Scope: the original current resource prerequisites remain explicit, including
Context, initial Safe, native availability and closedness, Fits, Reserved and
current annotation guard Heap. This does not derive a whole original-input
budget. It does not close arbitrary consumers, the whole parent role loop,
eager global completion, source lazy demand or Haskell correspondence.
Existing singleton_core can transport the appended cache role to a matching
actual successful raw singleton endpoint. No duplicate row observer is added.
No Haskell change or defect claim was made.

Exact dependencies:
- SharedTerminalAdapterResources.terminalAdapter_complete_resources:34-202.
- NativeReferences.incoming_preserved:177.
- ProgramRolesNativeHeap.keeps_program_slots:21.
- EnumerationDriver.Protected:35.


### program-roles-unmarked-child-note.md

The law retains all three original ChildEffects.child conclusions. It adds ProgramSlots for the unchanged mark set. The same actual shallow child action supplies safety, origin, and root protection. Existing prepared_allowed supplies incoming-reference preservation. No new slot role, native readback, future Packet, rank, model, or capacity input is used. This law covers the shallow action. Actual eager ordinary-child recursion still needs height induction.

Frozen public prefix SHA256: 8761939b9dcebd505630279eed9a9e085f1f07d4aae6314dbf2659ec23b1b9f3

ROOT prelude/proof correction: open the existing EnumerationDependencies namespace for EnumeratedOrigin. Destructure the existing getElem existence receipt explicitly. No new input or changed output. The public declaration text remains unchanged.


### program-roles-unmarked-finalize-note.md

# Actual unmarked finalization with Program roles

Frozen source: SourceSynthesisProgramRolesUnmarkedFinalize.lean, 75 lines.
SHA256: 8b08684f5e1a7503168033a1b85be42bd5df841b53d65a29532f054d4fd13bd2
One public law: complete_unmarked_program_slots.
Frozen header SHA256: 6dcd12544137627859e82cfa7e2e07ba86b652233c466b249eb58efeb07b3085.
The public header is unchanged after proof construction.

The header specializes Finalize.complete to the existing source Symbol/Constraint
Core and NativeHeap. It retains all original finalizer inputs and all 12 original
output fields, in their original order, under the SAME returned fuel/after tuple:
all larger-fuel actual runs, raw finish singleton, complete Core identity, stored
fragment, exact flag update, exact waiting count update, roots, correct counts,
all candidates, storage validity, PendingRealized, and conditional Safe.
It adds only CURRENT ProgramSlots and an unmarked raw target as inputs.
It appends ProgramSlots at that SAME after Core and Protected for each old mark.

The proof invokes Finalize.complete ONCE. It observes the returned exact Core.
The actual ancestry-reset Core retains current ProgramSlots by its unchanged
values/counter/representatives. modify_success identifies the same raw write
from that reset Core to the SAME returned after Core. One UnmarkedWrite theorem
then retains roles and incoming reference avoidance. The enumerated fragment
has no suspended references, so the write requires no fragment-role premise.
Each Protected receipt is rebuilt over the original Core; resetting ancestry
changes none of its three fields. No second finalizer/callback is executed.

The fragment retains the original FragmentBound prerequisite. No new SlotRole,
FragmentRoles, Safe, rank, model, Packet, after-role, or callback input is added.
Safety remains the ORIGINAL conditional output and is not strengthened.
This result does not assemble a Program parent, certify callback effects,
prove selected-prefix completion, or close the driver role invariant.
Unverified runtime draft; ROOT alone performs strict checking/publication.
No compiler, repository, Git, Haskell, root docs, or evidence changes.


### program-roles-unmarked-write-note.md

# Actual unmarked raw-slot write

Frozen source: SourceSynthesisProgramRolesUnmarkedWrite.lean, 50 lines.
SHA256: 71e0c22ba71e4956527d2cfc0ec9c26ea1d828a74a8c66d509b367cbf6fcc980
One public law: setValue_unmarked_program_slots.
Frozen header SHA256: 1f2bf08f485920f3479ad240100d02d59d0985981c657381dd6776a8ceff2205.
The public header is unchanged after proof construction.

The current inputs are ProgramSlots, an unmarked target, an arbitrary payload,
current avoidance of each marked class by the payload's suspended references,
and the SAME actual setValue Success.
The result retains the exact complete Core update, derives ProgramSlots after,
and proves Protected for each old marked root. The mark predicate is unchanged.
No SlotRole, ordinary layout, Safe, rank, or after-role supplier is required
for the unmarked payload. No supplied after-state bound or forest fact is needed.

The proof reuses modify_success and setValue_allowed.
Marked roots differ from the unmarked raw target, so getElem?_set_ne retains
all their stored payloads/roles. The counter and representatives do not change.
The current payload avoidance retains IncomingAvoid under that same forest.
The incoming payload may reference unmarked classes arbitrarily.
For .eliminated and .enumerated fragment, references is []; their avoidance
condition is vacuous, independently of the fragment's holes/layout/cycles.
Thus real prefix clears and non-Program finalizers instantiate without new gates.

Unverified runtime draft; ROOT runs strict checking/publication.
This is one raw setValue cut. It does not duplicate the selected action,
execute a callback, prove safety/rank, or establish a whole driver role invariant.
No compiler, repository, Git, Haskell, root documentation, or evidence changes.


## Next driver obligation (unproved plan)

# Actual shared driver Program-role induction

2026-11-12 20:53 CET. Read-only audit. Proposed laws below are not checked.

The existing finite producer covers the SHALLOW prepared worker. The actual
Haskell eager traversal remains a primary obligation. ChildPolicy.runWithChild
with shallowVisit equals PreparedRecursive.run (RecursiveChildPolicy:135).
An arbitrary Visitor can change every store. Its preservation cannot be a public
assumption that replaces the actual policy proof. runEager needs its own height
induction through eagerChild; SharedEagerChildren.prepared_child_lt:57 supplies
actual selected-child descent. That law does not establish eager role history.

## One prospective shallow producer header

Use the aliases and instances of SharedPreparedFiniteResources:19-29, in
SourcePruningEnumerationSharedPreparedRecursive. literal is the existing
SourceSynthesisLabelProgramBuildRoles.literal. No new proof predicate is needed.
The parameters through reserved match run_finite_complete_resources:74 exactly.

```lean
theorem run_finite_complete_resources_program_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      caller.checked.native.machine.heap before.core marked) (root : marked 0) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra)
        recursiveFuel metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, marked uv → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked
```

emitted already includes stopped output prefixes (SharedPreparedLiveRoot:31).
Keep this receipt intact. Readback then applies at each actual noStop done output;
early metadata stops do not establish noStop done. No model witness is derived.

## Exact induction and endpoint discipline

Strengthen the existing ResumeComplete / finite_complete induction, rather than
request role preservation from a future callback. The zero decision cases are
literal; resume_zero_output (SharedPreparedLiveRoot:99) keeps the same cache.
At positive depth, use the actual runPrefix result, common preparation ONCE,
then the actual ordinary scan or opaque dispatch, Left callback, and smaller
resume. See RecursiveChildPolicy:173, PreparedContinuations:60, and
PreparedFiniteExpansionResources:44. Right and Left recordTypes successes have
recordTypes_frame; apply RolesCompression.compression_frame_program_slots:19.

The ordinary proof has nested list inductions over selected rows and ordered
children. Branching.scan:29 restores the SAME captured Core for each sibling;
only caller/query endpoints thread. Reset to that captured marked set as well.
Transport its pending lookups through the actual Post.effects.keeps using
RolesNativeHeap.keeps_program_slots:21. Each output has its own finalMarked;
never carry fresh marks from one branch into the next branch's older Core.
Keep outputs before stops and all actual endpoint/resource receipts.

For a marked selected parent, get its ValueFields and annotation-only scs from
slots.stored. SelectedProgramChildRetention.prepared_fields:91 preserves the
actual preparation. ProgramChildScope.program_child_scope:92 supplies fields
and annotation-only buckets at app children 2/3 and filter child 1. Apply
ProgramChildRoleStep.program_child_role_step:44 at those exact occurrences.
Construct FragmentRoles from the SAME ordered child list. Then use the checked
parent_callback_roles:115, FragmentWrite:20, and the actual Left continuation.
An annotated component has no recursive Program child, even if its name is app.

## Small remaining operational seams

1. Selected-prefix rows and writes. NativeView.narrowAt:33 filters COMPLETE
original rows; HereditaryProgramFields.makeNode_fields:123 can retain fields.
Close actual narrowAt/OuterNarrow ValueFields preservation under current
Ready/Available/closed facts, then the actual Action.prepare:17 replacement.
For marked slots, ValueFields excludes recursiveBoundary, so checkRepeated
cannot park them (Recursion:17). Unmarked clear writes retain other slots.
Compression plus an unchanged transient bucket retains IncomingAvoid; a new
marked handle needs the SAME lookup and the filtered fields, not just Keeps.
2. Unmarked allocation and finalization. Own suspendMany creates only unmarked
classes. Combine CachedOwn.suspendMany_complete:46 with allocation_allowed,
suspension_protected, and Safe bounds to retain all existing ProgramSlots.
For an ordinary/Mu/union TYPE child, retain old marks through actual shallow
allocation without requiring its ValueFields or adding its fresh slot to marks.
A Type parent finalizer writes an unmarked target; derive preservation from its
exact write and empty suspended references. Existing FragmentWrite:20 assumes
a marked target, so it cannot directly discharge this case.
3. Transient Avoids is a derived traversal fact. For a STORED source bucket,
slots.incoming and its actual store membership give avoidance of every marked
class. EdgeInputs.complete:25 derives avoidance of old marks for each descended
bucket, including fresh own classes. Its bounds and Safe isolation separate
new Program marks from every already-captured remaining bucket. Carry this
fact across UF edits with Protected.avoids (EnumerationDriver:51), and across
fresh child allocation with the exact unchanged forest. InputsPending alone
protects expanded roots, not every pending Program mark. Do not substitute it.
Terminal partitions inherit avoidance by list membership and descent. Compose
TerminalPrefix:117 and Assimilation.finish_program_slots:108 with the actual
full terminal resource observer; both assimilation source and target must be
derived unmarked. Native value IDs do not identify marked raw UVar slots.

These are phase-local obligations with a CURRENT reservation, Fits and Heap.
The header does not derive original-input capacity, adequate recursive depth,
eager termination, literal Haskell pipeline correspondence, order, completeness,
or a satisfying assignment. Preserve these boundaries after root startup.


## Haskell and resources

No Haskell source or Cabal manifest differs from this base. Main is integrated. The external Liquid duplicate-name/refinement repair remains with claude-gondolin. The prior source-pinned negative packets remain unchanged. Their repaired-main rejection is intentional. All compiler and portable checks use the serial 4 GiB cap. Local usage was 28 percent at 21:03 CET; /tmp had 176.20 GiB free.
