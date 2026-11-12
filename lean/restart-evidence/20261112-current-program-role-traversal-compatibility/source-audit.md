# Actual ordered children and captured-parent Program roles
Generated 2026-11-12T21:48:10.824352+01:00.

Base `7c767bd067dfdd1f4c2e234a9c97669e33dd4576`; integrated main `e53852064d3ef5a2eafec47d754c27504b11de5f`. Four strictly checked source modules, 1161 lines, four public laws. These are actual producer attachments, not the full driver theorem. The full driver remains unproved.

## SourceSynthesisProgramRolesCapturedEdge
SHA256 `5724ecdbb0ed8b7c1b7d834c83baadf9441ef1d8d925af435174dad3b0e761a1`; 366 lines.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesCapturedEdge.complete_with_history_resources_program_slots"
]
```

Full public statement:

```lean
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
```

## SourceSynthesisProgramRolesChildTraversal
SHA256 `49f67f20dd4c3bd7cb6af23f470c5a405ff7baf32d1b26f0985185c1b42f6bba`; 470 lines.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesChildTraversal.complete_with_fragments_resources_program_slots"
]
```

Full public statement:

```lean
theorem complete_with_fragments_resources_program_slots
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
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal beforeCaller.checked.native.machine.heap before.core marked)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (scs : List Suspended) (start : Nat) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
      ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (actualInputs : inputs = SourcePruningEnumerationEdgeInputs.children edge scs start tries)
    (avoids : ∀ uv, marked uv → ∀ incoming bucket, (incoming, bucket) ∈ inputs →
      Avoids before.core.representatives uv bucket) :
    ∃ (r n p h k : Nat) (fragments : List Fragment) (afterCaller : Caller (bits + 2))
      (after : Cached) (savedQueries : Queries) (final : Memos) (next : Inventory)
      (afterRoots : Nat → Nat) (result : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Result (bits + 2)),
      (∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
        SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty (r + extraRepresentative) (n + extraNative)
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
      ∃ finalMarked : Nat → Prop, (∀ uv, marked uv → finalMarked uv) ∧
        ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core finalMarked ∧
        ∀ index child,
          ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
            (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
          fragments[index]? = some child → FragmentRoles literal finalMarked child := by
```

## SourceSynthesisProgramRolesOwnInputs
SHA256 `11c25ac96931f490291f73dc767801c12141da8334366130cc0f5b8eaa9cf1e5`; 105 lines.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesOwnInputs.complete_program_slots"
]
```

Full public statement:

```lean
theorem complete_program_slots
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (roots : Nat → Nat)
    (ready : SourceEqualityRequiredCache.Ready heap)
    (parentAvailable : Available heap (.node parentEntry edges depth free))
    (parentClosed : free = []) (selected : edge ∈ edges)
    (before : Cached) (safe : Safe before.core) (realized : PendingRealized heap before.core)
    (paths : Roots before.core.representatives roots)
    (counts : EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting)
    (flags : ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
      ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot))
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (allowed : arityAllows edge.children.length scs = true)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual))
    (slots : ProgramSlots valid literal heap before.core marked)
    (parentSlot : Nat) (parentNode : Option Nat)
    (parentStored : before.core.values[parentSlot]? = some (.unenumerated parentNode scs)) :
    ∃ (action : EnumerateM Symbol Constraint
        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
      (after : Cached),
      SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
      SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
        some [((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after)] ∧
      ExceptT.run (action before.core) =
        [.ok ((edge.entry.key.symbol,
          (children edge scs before.core.counter tries).map (fun input =>
            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), after.core)] ∧
      after.core = suspendedState tries.length before.core ∧
      after.core.counter = before.core.counter + tries.length ∧
      after.core.representatives = before.core.representatives ∧
      Safe after.core ∧ Roots after.core.representatives roots ∧ PendingRealized heap after.core ∧
      EnumerationCanonicalWaiting.Correct roots after.core.values after.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
      InputsPending after.core (scs ++ suspendedVars before.core.counter tries) ∧
      (∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
        Available heap incoming ∧ incoming.free = [] ∧
        (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket) ∧
      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
        Avoids before.core.representatives held scs →
        EnumerationDriver.Protected held before.core after.core ∧
          ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
            Avoids after.core.representatives held bucket) ∧
      ProgramSlots valid literal heap after.core marked ∧
      ∀ held, marked held → EnumerationDriver.Protected held before.core after.core ∧
        ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
          Avoids after.core.representatives held bucket := by
```

## SourceSynthesisProgramRolesUnmarkedCapturedEdge
SHA256 `19737980e12bad40ec787af9982447a4ed7707053beeea8e51f0f032514d4f9c`; 220 lines.

Checked public names:

```json
[
  "MicroCFTA.SourceSynthesisProgramRolesUnmarkedCapturedEdge.complete_with_history_resources_prepared_program_slots"
]
```

Full public statement:

```lean
theorem complete_with_history_resources_prepared_program_slots
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
    (valid : Constraint → Prop) (literal : String → Symbol) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (r n p h k : Nat) (afterCaller : Caller (bits + 2)) (after : Cached) (savedQueries : Queries)
      (final : Memos) (next : Inventory) (afterRoots : Nat → Nat) (result : Result (bits + 2)),
      (∀ er en P H ek, p ≤ P → h ≤ H →
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
        afterCaller.checked.native.machine.heap ∧
      ProgramSlots valid literal afterCaller.checked.native.machine.heap after.core marked := by
```

## Producer and frozen-header notes

No new desired after-role, future child, Packet, Projection or model provider is a public premise. Current source fields/buckets are derived from actual source receipts.

### program-roles-captured-edge-note.md

# One marked captured edge with its same computed callback

Frozen source: SourceSynthesisProgramRolesCapturedEdge.lean, 366 lines.
SHA256: 5724ecdbb0ed8b7c1b7d834c83baadf9441ef1d8d925af435174dad3b0e761a1
One public law: complete_with_history_resources_program_slots.
Frozen header SHA256: 28af0f37e177e1f6c5ee6cc85c1dccbfbaa68197db6a55dc494a271f40322fe5.
The public header is unchanged after proof construction.

The public header retains the ENTIRE parenthesized original existential packet
from CapturedEdge.complete_with_history_resources_prepared. All old inputs,
fuels/stability quantifiers, actual run/result, Post/full final Memos/query,
raw growth/roots/storage/realization/counts/flags, non-target origin, retained
inputs, protected roots, pending-history implication, completion or exact
stopping branch, fragment history/order advance, Fits and physical Heap remain.
It adds CURRENT graph/templates/metadata/Packet, ProgramSlots, marked target,
and actual full EdgeFields at the fixed source literal. No future endpoint,
role, Packet, model, Projection, child receipt or callback supplier is added.

The producer invokes OwnInputs ONCE, coupled ChildTraversal ONCE, and
parent_callback_roles ONCE on the actual completed branch. It does not invoke
the old captured aggregate producer, another traversal, another finalizer or
another callback to obtain independently chosen receipts. The actual cached
own prefix supplies the initial child cache. The actual returned caller,
full final Memos and query feed parent_callback_roles unchanged.

The marked target's SAME stored payload supplies inherited valid tries and
annotation-only scope internally. OwnInputs derives current all-mark child
bucket avoidance. Coupled traversal extends the raw mark set and derives
actual child FragmentRoles. Its native Post/growth/origin/protected-enumerated
receipts and the current original Packet derive the current post-child Packet.
Its exact successful child run derives the ordered Trace. No after-child
Packet or per-child role is supplied as a public premise.

On completion, parent_callback_roles assembles the full parent layout and
performs the SAME finalization plus callback. The outer afterRoots/after cache
share its finalization witnesses. The public completed-result observer retains
ALL finalizer equations and ALL computed callback fields: callback fuel,
verdict/metadata/core, Packet, RenderStable, compression Frame, types/openHoles/
typing equalities, same resources, all-fuel recordTypes Success and singleton,
full arbitrary-recur continueWith/restart equation, and callback-after roles.
The outer callback must consume this returned receipt; it need not run another
callback producer. Native caller and full final Memos remain the same.

The original universal order-advance field is derived at arbitrary current
level/frontier from the SAME actual origin/protection and finalizer Core.
Stopped children retain their exact old stopping receipt and reached mark set.
The complete-only callback observer is vacuous for that stopped result.
No prior-sibling completion, adequate recursive depth, whole driver result,
accepted semantic assignment or whole enumeration termination is claimed.

Unverified runtime draft; ROOT alone performs strict checking/publication.
No compiler, repository, Git, Haskell, root docs, or evidence changes.


### program-roles-child-traversal-note.md

# Ordered shallow ChildTraversal Program roles

Runtime draft: `SourceSynthesisProgramRolesChildTraversal.lean`, 470 lines.
Source SHA256: `49f67f20dd4c3bd7cb6af23f470c5a405ff7baf32d1b26f0985185c1b42f6bba`.
Public-header SHA256: `f9dee949b2a78b6dd24802691deaa68f52892584aecace7ed58168577caa0bbf`.
The header equals the frozen 68-line header byte for byte.
Owner did not compile or change repository files.

Public law:
`SourceSynthesisProgramRolesChildTraversal.complete_with_fragments_resources_program_slots`.
It retains EVERY output field of ChildTraversal.complete_with_fragments_resources.
The selected input list has the explicit actual EdgeInputs.children identity.
Current source fields, inherited annotation paths, actual guard projection,
initial ProgramSlots, and old-mark bucket avoidance are the added inputs.

The result appends one finalMarked predicate. It extends the initial marks.
The SAME afterCaller.heap and after.core satisfy ProgramSlots. The SAME returned
fragments have FragmentRoles at exact app indices 2/3 and filter index 1.
The law retains both complete results and stopped/rejected fragment prefixes.

The private complete_aux strengthens the existing ordered child induction.
Each reached head calls ChildDispatch.complete_with_fragments_resources once.
Its Protected, reference history, counter growth and Post.effects.keeps retain
all old marked slots, including terminal and rejected outcomes. No second
terminal resource producer runs. The full original receipt stays intact.

For an actual Program position, program_action inverts the SAME successful
child observation. Annotation-only paths exclude a terminal trie. The exact
prepared action is passed to checked ChildRetained.program_child_retained.
That law marks the actual fresh raw counter and derives avoidance for every
captured bounded suffix bucket. The suffix induction shifts the original child
index and transports collected fragments to the extending mark predicate.
The public wrapper derives each private field/scope fact with the checked
ProgramChildScope.program_child_scope and the actual indexed input identity.
There is no public future per-child mark, role, Packet, model or Projection gate.

Imports: SharedTraversalResources, ProgramRolesChildRetained,
ProgramRolesNativeHeap, ProgramChildScope. Private helpers reuse the existing
FragmentRoles, ProgramSlots, literal Symbol layout, and actual shallow worker.
A concrete singleton/flatMap local List monad fixes the existing action type.

Scope: a current reserved shallow child traversal. Capacity and guard Heap
premises remain explicit. This law does not prove adequate outer recursive
fuel, an original-input resource bound, eager traversal, a model witness, or
whole default Haskell enumeration correctness. Alpha owns the outer driver.
Gamma owns the actual captured parent composition at this exact endpoint.

## First strict-check proof repair

Root's first check found one private proof error at line 113. The case split
had already rewritten the prepareChild equality to reflexivity. The repair
uses rfl in that one proof field. The initial source remains in
`SourceSynthesisProgramRolesChildTraversal-b2f71b50.lean`.
The full log is `program-roles-child-traversal-213457-failure.txt`.
The public header is unchanged. No premise or operation changes.
The repaired source awaits Root's strict recheck. Owner did not compile.


### program-roles-own-inputs-note.md

# Actual own-class preparation with all current Program roots

Frozen source: SourceSynthesisProgramRolesOwnInputs.lean, 105 lines.
SHA256: 11c25ac96931f490291f73dc767801c12141da8334366130cc0f5b8eaa9cf1e5
One public law: complete_program_slots.
Frozen header SHA256: 3843362f5d9ced49548e2cc32f9c8e7446b6882ec6c9faeb486da3452684137c.
The public header is unchanged after proof construction.

The theorem invokes EdgeInputs.complete ONCE and retains its ENTIRE original
action/after tuple and receipt in the original order. This includes actual
prepare/cached-prepare/raw execution, exact suspendedState/counter/forest,
Safe/roots/realization/counts/flags, combined pending inputs, genuine current
child admission/closedness/bounds/pending, and arbitrary old-root conditional
protection plus every actual child-bucket Avoids conclusion.

Additional CURRENT inputs are ProgramSlots and an actual stored raw pending
parent payload whose suspended bucket is exactly the inherited scs. The parent
raw slot and optional native handle need no additional role or future supplier.
For every marked held, slots.incoming applied to that SAME stored payload derives
Avoids of inherited scs. slots.bounded/roots then discharge the old producer's
existing conditional protection inputs. The appended protection and child
avoidance therefore apply unconditionally to every current marked Program root.

The SAME returned cached-prepare equation exposes its actual suspendMany result.
The endpoint is projected from that equation, not selected by another producer.
ClassAllocation.suspendMany_program_slots observes that actual allocation once
to derive ProgramSlots at the SAME returned after. Fresh equality slots remain
unmarked. No second own-prefix/child/native/semantic producer is invoked.
All prior inputs and outputs remain; no desired after-role, child receipt,
future bucket avoidance, model, rank or after-state supplier is assumed.

This is the own-prefix component. It does not execute child hooks, establish
the child driver induction, prove traversal completion, or prove whole search
termination. Original EdgeInputs positive admission premises remain explicit.
Unverified runtime draft; ROOT alone performs strict checking/publication.
No compiler, repository, Git, Haskell, root docs, or evidence changes.


### program-roles-unmarked-captured-edge-note.md

ROOT freezes the complete actual Shared CapturedEdge.complete_with_history_resources_prepared statement, adding only current valid/literal/marks/ProgramSlots and an unmarked captured target. The entire old stable-run/native/Memos/storage/index/origin/conditionalhistory/completed-or-stopped/Fits/Heap tuple remains. One actual SelectedEdge.complete_with_fragments_resources supplies current incomingHistory, root protection and native Keeps before those fields are hidden. The actual stored source bucket derives marked avoidance. One full unmarked Finalize producer preserves the same role set; it retains every old finalizer field. No after-role, child provider, Packet, Projection, model or extra capacity witness is supplied. The old final Packet closure remains available in the outer proof from the unchanged original receipt.

Frozen public header SHA256: 356413059bea3ae707e9544856abcf59ffe519e01dfea36e7cb5d1de018b414e

ROOT proof-only repair: qualify the two existing CapturedEdge.run unfoldings. The wrapper namespace also opens the native constructor run, so unqualified simp/rw names were ambiguous. Same literal action and public header; first source retained.


## Private driver scaffold only

The immutable 179-line shared-driver-scaffold-78ba5038.lean strictly compiles under 4 GiB. It has no public theorem. Its source SHA256 is `78ba5038b40b4cee4c4ca1f75778c7a17874ae7f924b702ef097dff36cc1a962`. It checks zero-depth and computed callback glue only. The proposed public driver header below is UNPROVED; no public-law count includes this draft.

```lean
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The same finite worker retains Program roles at every complete or stopped output. -/
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
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, marked uv → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked

```

## Boundaries

The completed parent callback retains the actual computed singleton/Frame/Packet receipt and all native/Memos endpoints. It does not execute a second callback. Sibling scans require separate mark sets per captured Core branch. Existing finite resources cover shallow runWithChild; actual eager Haskell traversal still needs height/resource induction. Original-input total resources, model existence, default Mu semantics, stream order/multiplicity, inverses and Haskell correspondence remain separate. No Haskell source changes. External Liquid duplicate-name/refinement repair remains with claude-gondolin. The previous focused16examples were not rerun for these Lean-only changes. Usage29percent at21:39CET, /tmp175.49GiB free. Two latest temporary proof workspaces total under1MiB as measured21:46.

## Independent declaration review

# R255 public-header review

2026-11-12 21:46 CET. Read-only review of actual declarations and the frozen
SharedDriver header. No compiler, source, repository, or Haskell changes.
No substantive signature defect was found.

## Comparison method and receipt preservation

The original conclusion is an exact whitespace-normalized prefix of each new
conclusion below. For marked Capture and SharedDriver, remove only the outer
parentheses that group the unchanged original receipt. No original conjunct is
removed, weakened, renamed, or given a different endpoint in these comparisons.
This syntactic comparison supports header preservation. It is not a kernel check.

- OwnInputs.complete_program_slots: compare EdgeInputs.complete:25.
  The original action, CachedOwn.prepare identity, exact singleton raw action,
  suspendedState/counter/forest, Safe, roots, realized slots, waiting counts,
  flags, combined InputsPending, every child admission, and root protection
  remain. The source has no fuel quantifier to remove. New outputs add roles
  and child-bucket avoidance at the SAME after state.
- ChildTraversal.complete_with_fragments_resources_program_slots: compare
  SharedTraversalResources.complete_with_fragments_resources:36.
  Every r/n/p/h/k bound and all larger er/en/ek with P/H lower bounds remain.
  Full Post, final Memos, saved-query identity, counter growth, roots/storage,
  realized slots, counts/flags, origins, both protection clauses, reference and
  pending history, all fragment bounds, complete PendingFragment/FragmentAvoid
  observers, stopped prefixes, final Fits and Heap remain. Roles and indexed
  Program fragments refer to the SAME afterCaller, after.core, and fragments.
- CapturedEdge.complete_with_history_resources_program_slots: compare
  SharedCapturedPreparedResources.complete_with_history_resources_prepared:34.
  The complete old captured receipt remains: all larger bounds, actual run,
  native Post/full Memos, growth/storage/realized/counts/flags, enumerated
  origins away from uv, inherited inputs, root protection, pending history,
  complete final store/ancestry/root/pending/Stratified observers, stopped
  fragment prefix and candidate cache, and final Fits/Heap.
- UnmarkedCapturedEdge.complete_with_history_resources_prepared_program_slots
  retains that SAME prepared captured receipt and appends same-mark roles.
  It does not replace native Post or full Memos with a query-only statement.
- SharedDriver.run_finite_complete_resources_program_slots: compare
  SharedPreparedFiniteResources.run_finite_complete_resources:74.
  The same all-larger-work-fuel equation and COMPLETE OutcomeResources remain.
  OutcomeResources:32 retains reached native endpoint, inventory/full Memos,
  Post/Fits/Heap, stopped optional endpoint, and every output resource packet.
  The extra roles quantify over emitted, which includes stopped output prefixes
  (SharedPreparedLiveRoot.emitted:31). Each output has its own extending marks.

## Added inputs and operational scope

OwnInputs adds current ProgramSlots and a literal current parent store equation.
The parentSlot need not be marked. Its stored bucket and current incoming
invariant derive exclusion from old marked classes; no child exclusion supplier
is added there.

ChildTraversal adds current source EdgeFields, inherited valid annotation paths,
actual guard projection, exact EdgeInputs identity, initial roles, and current
old-mark exclusion for those concrete input buckets. OwnInputs now derives the
last item from that actual stored parent. ProgramChildScope derives per-child
fields/scope inside the wrapper. No future child-role or child-Packet gate occurs.

Marked Capture requires marked uv, current EdgeFields, and the CURRENT input
Packet at caller/memos/metadata/before. Its new after/final/callback Packets and
roles are OUTPUTS. The forall recur/stop/order clause is a returned literal
continueWith equation. It does not assume a role-preserving callback or that
recursion completes. The prepared parent availability/closedness were already
inputs of the original prepared producer; they are not new future suppliers.

Unmarked Capture requires not marked uv. It retains the old marks and makes no
Program-fragment claim for that unmarked target. It does not replace the marked
case. Marked Capture extends marks through actual Program children and returns
Program fragment roles only for a complete captured result; stopped receipts
retain their old resource data and output roles without a false completion claim.

SharedDriver adds only CURRENT initial roles and marked 0. Its frozen header
contains no future callback roles, source acceptance, model, Projection, or
worker-completion supplier. The working module at review time contains private
proofs but no public driver declaration yet; this review covers its frozen53L
header, not a completed or checked driver implementation.

These laws cover the SHALLOW worker. RecursiveChildPolicy.runWithChild_shallow
identifies that specialization with PreparedRecursive.run. An arbitrary Visitor
has no such guarantee. Actual Haskell eager traversal still needs the real
child-policy/height induction. Current Reserved/Fits/Heap and finite depth stay
explicit. No original-input capacity, adequate depth, eager termination,
model/completion existence, output order, or whole pipeline claim follows here.

## Frozen public declaration hashes

OwnInputs: 577b5e8b1ff054954072c8c0b4a978a671911822534955e7059f8bb8610f08b6
ChildTraversal: 0aaada8ae8b77f0f2f09c0df09f5eaea0d70b731ca686d05ae64110e844d7c9e
MarkedCapture: 1adaa834ad209d7aef1c9df97c3dbd06e0eb4b0ddadb5566f24739c11e875ffc
UnmarkedCapture: 356413059bea3ae707e9544856abcf59ffe519e01dfea36e7cb5d1de018b414e
SharedDriver frozen declaration: 4ec93f747f3414ce508326cef1757f588ca8082f593d3fba812b409274f3671a
Hashes cover theorem declarations before their proofs; they exclude imports.

## Preserved private scaffold draft (zero public laws)

This immutable source is retained for review and reproduction. It does not implement the public driver theorem.

```lean
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourceSynthesisProgramRolesCompression
import MicroCFTA.SourceSynthesisProgramRolesNativeHeap
import MicroCFTA.SourceSynthesisProgramRolesSelectedPrefix
import MicroCFTA.SourceSynthesisProgramRolesOwnInputs
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles

/-!
# Program roles in the actual shallow finite shared worker

Each output retains its own marks and exact native endpoint.
Completed callbacks run before the next captured sibling.
The proof does not derive an adequate recursive depth.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourceSynthesisProgramEnumerationRoles (ProgramSlots FragmentRoles)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type} {bits : Nat}
local notation "RoleResult" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

private def programOutputs (valid : Constraint → Prop) (marked : Nat → Prop)
    (outcome : RoleResult) : Prop :=
  ∀ output ∈ emitted outcome, ∃ extended : Nat → Prop,
    (∀ uv, marked uv → extended uv) ∧
    ProgramSlots valid literal output.caller.checked.native.machine.heap output.cache.core extended

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def programResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (depth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth seed ceiling →
    ∀ (valid : Constraint → Prop) (marked : Nat → Prop),
    ProgramSlots valid literal caller.checked.native.machine.heap before.core marked →
    ∃ bound outcome,
      (∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (bound + extra) depth metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final depth seed ceiling) outcome ∧
      programOutputs valid marked outcome

private theorem zero_program_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    _selectionMembers _selectionLength _mass _reserved valid marked slots
  obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
    caller memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
    seed packet bounded known
  refine ⟨0, outcome, fun extra => running (0 + extra), resources, ?_⟩
  intro output member
  have actualMember : output ∈ emitted (resume holeKey fits admits graph templates checkEmpty
      edgesOf stop order 0 0 metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before)) := by
    rw [running 0]
    exact member
  obtain ⟨cacheSame, callerSame, _querySame⟩ := resume_zero_output
    holeKey fits admits graph templates checkEmpty edgesOf stop order 0 metadata caller memos.query
    before (SourcePruningEnumerationRestart.decision stop order metadata before) output actualMember
  refine ⟨marked, fun _ tagged => tagged, ?_⟩
  simpa only [cacheSame, callerSame] using slots

private theorem computed_callback_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (depth : Nat)
    (recursive : programResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty
      edgesOf stop order formulas solver depth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (before : Cached) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragments.Fragment Symbol)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits depth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing) (after : Core)
    (returned : Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before))
    (framed : EnumerationCompressionFrame.Frame before.core after)
    (recorded : ∀ extra, ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates
      (callbackFuel + extra) metadata uv (.inl fragment) before.core) = [.ok (result, after)]) :
    ∃ bound outcome,
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) depth)
        graph templates stop order (bound + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final depth seed ceiling) outcome ∧
      programOutputs valid marked outcome := by
  have callback (extra : Nat)
      (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → RoleResult) :
      continueWith recur graph templates stop order (callbackFuel + extra) metadata uv fragment
        caller memos.query before =
        if result.1 then .complete [] caller memos.query
        else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
          (SourcePruningEnumerationRestart.decision stop order result.2
            (EnumerationExpandableIndex.frame after before)) := by
    unfold continueWith
    rw [recorded extra]
    obtain ⟨flag, updated⟩ := result
    cases flag <;> rfl
  by_cases rejected : result.1 = true
  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge depth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2, ?_⟩
    · intro extra
      rw [callback extra, ite_eq_left rejected]
    · intro output member
      exact (List.not_mem_nil member).elim
  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      caller.checked.native.machine.heap before.core after marked framed slots
    have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound after ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after framed.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources, outputRoles⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength afterMass reserved valid marked afterSlots
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources, outputRoles⟩
    intro extra
    have actual := callback (resumeFuel + extra)
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        (callbackFuel + resumeFuel + extra) depth)
    rw [← Nat.add_assoc] at actual
    rw [actual, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive

```
