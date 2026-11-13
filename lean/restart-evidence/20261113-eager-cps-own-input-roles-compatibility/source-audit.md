# Checked eager CPS bases and current-bucket Program roles

Base: e1107dfe0bf3f66c9b8398a9d0938ed7c4b71a8a.
Main: e53852064d3ef5a2eafec47d754c27504b11de5f, fetched unchanged at 2026-11-13 01:38 CET.
The checkpoint contains two modules and 1662 lines. Four public laws are declared.
One public law is new. The three arithmetic laws keep their exact old declarations and proofs.
All old execution definitions remain. No Haskell source changed.

The private CPS bases now form the live Lean reservation module. The current public
runEager_finite_complete_resources target remains UNPROVED and is not declared.
The source proves actual fallback resources, height-zero child and depth-zero resume
cases, full tuple resources under a PRIVATE child-height induction hypothesis,
and the actual own-plus-successful-tuple parent input receipt. The callback proof
uses a PRIVATE lower-depth hypothesis with the literal actual Restart.decision.
It retains the same caller, complete Memos, Fold, endpoints and OutcomeResources.
The positive ordinary-row, captured scan/height and outer-depth inductions remain open.
No future child Packet, producer, roles or model provider is added to a public law.

The new role primitive runs EdgeInputs.complete once. It observes the SAME actual
own-class allocation. It retains every old output conjunct. Current ProgramSlots
and bucket avoidance preserve every old marked slot and protect each actual child
bucket. It does not require a stored parent slot. The old stored-parent primitive
is unchanged. Full eager Program-role induction remains open.

Two repairs concern the private proof contracts. They do not identify Haskell defects.
The old universal after-reference predicate was stronger than the actual suspended
fresh variables allow. The new conditional field carries the CURRENT future-variable
property. Tuple tails transport that property through actual counter growth. The
existing fresh_separate lemma supplies it for protected current classes. No new
public supplier is needed. The old checked stronger lemmas remain valid as stated.
The stopped-head tuple branch must pad the ORIGINAL continuation's numeric allowance
across the remaining planned stages. Existing arithmetic lemmas derive the original
admission, Fits, physical Heap and final-plan domination. The actual failure consumer
runs once. This repair uses no rejected-state Packet or Safe claim, worker replay,
new native operation or comparison between plans at unrelated seeds.

The cold shallow current-input Program-output result and exact completed-nodeCall
source-language result remain the strongest established whole-path contracts in
their stated scopes. Eager full resources and roles, shared backward source history,
finite Type solvability, output/depth adequacy, total work/host capacity, streams,
both inverses and Haskell correspondence remain open. The external Liquid repeated
argument-name/refinement issue remains in FINDINGS. This checkpoint changes no Haskell.

## Exact public declarations

### SourceSynthesisProgramRolesOwnInputsAvoids

Source SHA256 `b71aacf3fe300866849e3aecb52457f5f183b1512b25684f1bd4bb1146299ac2`. 102 lines.

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
    (avoids : ∀ held, marked held → Avoids before.core.representatives held scs) :
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
          Avoids after.core.representatives held bucket
```

### SourcePruningEnumerationSharedEagerReservation

Source SHA256 `292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232`. 1560 lines.

```lean
theorem eagerFinal_ge (depth : Nat) (seed : Seed) (ceiling : Nat) :
    Le seed.2 (eagerFinal depth seed ceiling).2 ∧
      seed.1 ⊆ (eagerFinal depth seed ceiling).1
```

```lean
theorem first_row_callback_le_final (depth : Nat) (seed : Seed) (ceiling : Nat)
    (positive : 0 < scalar (preparedSeed seed).2) :
    let captured := preparedSeed seed
    let N := scalar captured.2
    let b := ceiling + SourcePruningEnumerationGuardWidth.width captured.1
    let rowStart := eagerFinal depth (advance captured (ceiling + 1)) (ceiling + ceiling)
    let first := eagerFinal depth (advance rowStart (N * (b + 1))) (ceiling + N * b)
    let whole := eagerFinal (depth + 1) seed ceiling
    Le first.2 whole.2 ∧ first.1 ⊆ whole.1
```

```lean
theorem eagerReserved_of_final_room (bits depth : Nat) (seed : Seed) (ceiling : Nat)
    (room : Room bits (eagerFinal depth seed ceiling).2) :
    eagerReserved bits depth seed ceiling
```

## Private source history

The registered source is checked1560. Apply the reverse patches below in order.
Every patch was replayed with GNU patch --output and matched the target bytes.
Previous stages through checked1057 remain in the preceding Git checkpoint.
These patches also retain all subsequent failed drafts and stronger contracts.

```json
[
  {
    "stage": "checked381",
    "lines": 381,
    "source_sha256": "988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1057",
    "lines": 1057,
    "source_sha256": "a335c974561f4e7582dbc797d3b22877013187f9a213663f67716f6297a67277",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1179",
    "lines": 1179,
    "source_sha256": "0b18ed3a958619b820aeaa48f1ee4348ec49e74d4e58d4ef39f1d967c7022434",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1179",
    "lines": 1179,
    "source_sha256": "dc0a4f85caad0271c40399476ee1863f083e31ba4dff5b8570343f63c9e9931a",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1267",
    "lines": 1267,
    "source_sha256": "8f5b35234a38d083b898ad890c8ff6b8013e16ce32a9ab994bb805712872d319",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1267",
    "lines": 1267,
    "source_sha256": "8ce4041b06a0f2eba5b037570b649c8ff5e6f8927d768e879a3deffe2c27813b",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1273",
    "lines": 1273,
    "source_sha256": "52c860fd8a92ccdfbde663a02ecb9afb9f9b041275e5edb0a025815fd0922d92",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1463",
    "lines": 1463,
    "source_sha256": "e733903803302b70916e2340063fe893bf71e323d70bf849921a585948568269",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1475",
    "lines": 1475,
    "source_sha256": "e36d630f8bbf94f7881b6daa6a983d466664e599bd0df6c6b22210918314ee77",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1560",
    "lines": 1560,
    "source_sha256": "292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  }
]
```

### checked1560 to checked1475

```diff
--- checked1560.lean
+++ checked1475.lean
@@ -1475,85 +1474,0 @@
-section ActualOwnTupleInputs
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem own_tuple_child_inputs
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (caller : Caller (bits + 2)) (metadata : Metadata Typing) (before own : Cached)
-    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (tries : List EqualityTrie.Trie)
-    (residual : Option Constraint)
-    (ownCore : own.core = suspendedState tries.length before.core)
-    (ownCounter : own.core.counter = before.core.counter + tries.length)
-    (ownProtects : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-      Avoids before.core.representatives held scs →
-      EnumerationDriver.Protected held before.core own.core ∧
-        ∀ incoming bucket, (incoming, bucket) ∈
-          SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
-          Avoids own.core.representatives held bucket)
-    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
-    (history : TupleInputs formulas solver caller metadata own
-      (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)
-      fragments reached saved after) :
-    ChildInputs formulas solver caller metadata before scs (.node edge.entry.key.symbol fragments) reached saved
-      (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
-    := by
-  obtain ⟨next, final, post, querySame, afterPacket, growth, origin, _enumProtects,
-    rootsProtects, references, fragmentBounds, fragmentHistory⟩ := history
-  have ownGrowth : before.core.counter ≤ own.core.counter := by
-    rw [ownCounter]
-    exact Nat.le_add_right _ _
-  have ownOrigin : EnumeratedOrigin before.core own.core := by
-    rw [ownCore]
-    exact suspension_origin tries.length before.core
-  have nodeBound : FragmentBound after.core.counter (.node edge.entry.key.symbol fragments) := by
-    have listBound : ∀ pieces : List Fragment,
-        (∀ child ∈ pieces, FragmentBound after.core.counter child) → FragmentsBound after.core.counter pieces := by
-      intro pieces
-      induction pieces with
-      | nil => intro _; trivial
-      | cons first rest ih =>
-        intro bounded
-        exact ⟨bounded first (by simp), ih (fun child member => bounded child (List.mem_cons_of_mem _ member))⟩
-    exact listBound fragments fragmentBounds
-  let fragment : Fragment := .node edge.entry.key.symbol fragments
-  let finished := SelectedEdge.finish residual fragment after
-  have finishedSafe : Safe finished.core := SelectedEdge.finish_safe residual fragment after afterPacket.safe nodeBound
-  have finishedPacket : Packet formulas solver next reached final metadata finished := by
-    obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := afterPacket.valid
-    obtain ⟨level, frontier, ordered⟩ := afterPacket.ordered
-    exact ⟨afterPacket.context, finishedSafe, afterPacket.pending,
-      ⟨roots, paths, finishedSafe.1, realized, counts, flags⟩,
-      ⟨level, frontier, ordered.classes, ordered.expanded, ordered.pending⟩, afterPacket.bounded⟩
-  refine ⟨next, final, post, querySame, finishedPacket, Nat.le_trans ownGrowth growth,
-    ownOrigin.trans origin, ?_, ?_, nodeBound, ?_, ?_⟩
-  · intro held inside root avoids
-    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
-    have childFrame := rootsProtects held (Nat.lt_of_lt_of_le inside ownGrowth) frame.root avoidsChildren
-    exact frame.trans (childFrame.trans (SelectedEdge.finish_protected residual fragment after held childFrame.root))
-  · intro allowed valid inherited future
-    have ownAllowed : EnumerationReferences.ReferencesAllowed allowed own.core := by
-      rw [ownCore]
-      exact EnumerationReferences.suspension_allowed allowed tries.length before.core valid
-    have freshAllowed : EnumerationReferences.InputsAllowed allowed (suspendedVars before.core.counter tries) :=
-      EnumerationReferences.suspended_allowed allowed before.core.counter before.core.counter tries (Nat.le_refl _) future
-    apply references allowed ownAllowed
-    · intro child bucket member
-      obtain ⟨indexed, _indexedMember, pairSame⟩ := List.mem_map.mp member
-      cases pairSame
-      intro sc listed
-      rcases List.mem_append.mp listed with inheritedMember | freshMember
-      · exact EnumerationReferences.descend_allowed allowed scs indexed.2 inherited sc inheritedMember
-      · exact EnumerationReferences.descend_allowed allowed (suspendedVars before.core.counter tries)
-          indexed.2 freshAllowed sc freshMember
-    · intro uv lower
-      exact future uv (Nat.le_trans ownGrowth lower)
-  · exact pendingFragment_node after.core edge.entry.key.symbol fragments
-      (fun child member => (fragmentHistory child member).1)
-  · intro held inside root avoids uv hole
-    obtain ⟨frame, avoidsChildren⟩ := ownProtects held inside root avoids
-    change HasHole (.node edge.entry.key.symbol fragments) uv at hole
-    cases hole with
-    | child _ _ child _ member below =>
-      exact (fragmentHistory child member).2 held (Nat.lt_of_lt_of_le inside ownGrowth)
-        frame.root avoidsChildren uv below
-
-end ActualOwnTupleInputs
-
```

### checked1475 to failed1463

```diff
--- checked1475.lean
+++ failed1463.lean
@@ -1451,13 +1451 @@
-              let entry := advance current (count * (bound + 1))
-              have entryFits : Fits entry.2 reached.checked := fitted.mono
-                (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge current (count * (bound + 1)))
-              have entryKnown : Heap (fun guard => guard ∈ entry.1) reached.checked.native.machine.heap := by
-                intro key edge found
-                exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge current
-                  (count * (bound + 1)) (supported key edge found)
-              have entryAdmitted : admitted (retained + count * bound) entry :=
-                tupleReserved_first_callback bits limit own height count bound retained continuation admitted current accepted
-              obtain ⟨fuel, outcome, running, resources⟩ := consumers.2 [] reached saved after outer waiting next final
-                post query entry (retained + count * bound) entryFits entryKnown entryAdmitted
-              have included := first_callback_le_tuple_of_growth limit own height count bound retained continuation growth current
-              exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
+              exact consumers.2 [] reached saved after outer waiting next final post query current retained fitted supported accepted
```

### failed1463 to checked1273

```diff
--- failed1463.lean
+++ checked1273.lean
@@ -1273,190 +1272,0 @@
-section ActualTupleConsumers
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private def TupleConsumers
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
-    (inputs : List (Node × List Suspended)) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
-  (∀ fragments reached saved after,
-    TupleInputs formulas solver original metadata before inputs fragments reached saved after →
-    ∀ current retained, Fits current.2 reached.checked →
-      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
-      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
-      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragments reached saved after = outcome) ∧
-        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
-  (∀ (completed : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
-      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
-      (next : Inventory) (final : Memos),
-    Post formulas solver next original reached final → final.query = saved →
-    ∀ current retained, Fits current.2 reached.checked →
-      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
-      ∃ fuel outcome,
-        (∀ extra, stopped (fuel + extra) completed ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
-        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))
-end ActualTupleConsumers
-
-section ActualPlannedTuple
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private def EagerTupleComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
-  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (inputs : List (Node × List Suspended)) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
-    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
-    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
-    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
-    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → inputs.length ≤ count →
-    (∀ child bucket, (child, bucket) ∈ inputs →
-      Available captured child ∧ child.free = [] ∧ MergedOrdinaryHeight.height child ≤ height ∧ bucket.length ≤ bound ∧
-        (∀ sc ∈ bucket, sc.var < before.core.counter) ∧ InputsPending before.core bucket) →
-    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
-      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
-        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
-          tries.length ≤ own) →
-    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
-    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
-    tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      count bound ceiling continuation admitted seed →
-    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
-    TupleConsumers formulas solver caller metadata before inputs uv continuation admitted done stopped →
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        (done (fuel + extra)) (stopped (fuel + extra)) inputs caller before memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome)
-
-private theorem eager_tuple_nil_resources
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
-    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (uv : Nat)
-    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (packet : Packet formulas solver inventory caller memos metadata before) (fits : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      count bound ceiling continuation admitted seed)
-    (consumers : TupleConsumers formulas solver caller metadata before [] uv continuation admitted done stopped) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
-  let visit : Nat → Visitor := fun fuel =>
-    SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf
-  exact tuple_nil_reserved_resources limit own height count bound ceiling continuation admitted growth seed formulas solver
-    caller memos before uv visit done stopped fits known mass reserved (fun retained current bounded supported mass accepted =>
-      consumers.1 [] caller memos.query before
-        (tuple_inputs_nil formulas solver inventory caller memos metadata before packet)
-        current retained bounded supported mass accepted)
-
-private theorem eager_tuple_complete_of_child
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (child : EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver)
-    (count : Nat) :
-    EagerTupleComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
-  induction count with
-  | zero =>
-      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
-        packet fits known kept mass length _genuine _shapes _selectionMembers _selectionLength reserved growth consumers
-      cases inputs with
-      | nil =>
-          exact eager_tuple_nil_resources checkEmpty edgesOf limit own height 0 bound ceiling continuation admitted growth
-            seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved consumers
-      | cons first rest => simp only [List.length_cons] at length; omega
-  | succ count ih =>
-      intro inventory caller memos metadata before seed bound ceiling inputs uv continuation admitted done stopped
-        packet fits known kept mass length genuine shapes selectionMembers selectionLength reserved growth consumers
-      cases inputs with
-      | nil =>
-          exact eager_tuple_nil_resources checkEmpty edgesOf limit own height (count + 1) bound ceiling continuation admitted growth
-            seed formulas solver inventory caller memos metadata before uv done stopped packet fits known mass reserved consumers
-      | cons input rest =>
-          rcases input with ⟨incoming, bucket⟩
-          obtain ⟨available, closed, ranked, bucketBound, bounded, pending⟩ := genuine incoming bucket (by simp)
-          let tailPlan := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
-          let tailAdmitted := fun retained current => tupleReserved (nodePlan limit own height)
-            (nodeReserved bits limit own height) count bound retained continuation admitted current
-          let yes : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
-            fun fuel fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren
-              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty fuel fuel fuel fuel fuel edgesOf)
-              (fun fragments => done fuel (fragment :: fragments))
-              (fun completed => stopped fuel (fragment :: completed)) rest reached after saved
-          let no : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
-            fun fuel observation candidate => stopped fuel [] observation candidate
-          have tailGrowth : ∀ retained current, Le current.2 (tailPlan retained current).2 ∧
-              current.1 ⊆ (tailPlan retained current).1 := by
-            intro retained current
-            exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
-              count bound retained continuation growth current
-          have headConsumers : ChildConsumers formulas solver caller metadata before bucket uv tailPlan tailAdmitted yes no := by
-            constructor
-            · intro fragment reached saved after head current retained fitted supported afterMass admittedAfter
-              have currentGenuine : ∀ value retainedBucket, (value, retainedBucket) ∈ (incoming, bucket) :: rest →
-                  Available caller.checked.native.machine.heap value ∧ value.free = [] ∧
-                  (∀ sc ∈ retainedBucket, sc.var < before.core.counter) ∧ InputsPending before.core retainedBucket := by
-                intro value bucket member
-                obtain ⟨oldAvailable, closed, _ranked, _width, bounded, pending⟩ := genuine value bucket member
-                exact ⟨kept.available value oldAvailable, closed, bounded, pending⟩
-              have combined := child_then_tuple_inputs formulas solver inventory caller memos metadata before incoming bucket rest
-                packet currentGenuine fragment reached saved after head
-              obtain ⟨next, final, post, query, afterPacket, _growth, _origin, _protected,
-                _references, _bounded, _pending, _avoids⟩ := head
-              have tailGenuine : ∀ value bucket, (value, bucket) ∈ rest →
-                  Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧ bucket.length ≤ bound ∧
-                    (∀ sc ∈ bucket, sc.var < after.core.counter) ∧ InputsPending after.core bucket := by
-                intro value bucket member
-                obtain ⟨oldAvailable, closed, ranked, width, _bounded, _pending⟩ :=
-                  genuine value bucket (List.mem_cons_of_mem _ member)
-                obtain ⟨_available, _closed, bounded, pending⟩ := combined.1 value bucket member
-                exact ⟨oldAvailable, closed, ranked, width, bounded, pending⟩
-              let tailDone : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
-                fun fuel fragments => done fuel (fragment :: fragments)
-              let tailStopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
-                fun fuel completed => stopped fuel (fragment :: completed)
-              have tailConsumers : TupleConsumers formulas solver reached metadata after rest uv continuation admitted
-                  tailDone tailStopped := by
-                constructor
-                · intro fragments finalCaller queries finished history entry ceiling fitted supported mass accepted
-                  exact consumers.1 (fragment :: fragments) finalCaller queries finished
-                    (combined.2 fragments finalCaller queries finished history) entry ceiling fitted supported mass accepted
-                · intro completed finalCaller queries finished outer waiting inventory memos later query
-                    entry ceiling fitted supported accepted
-                  exact consumers.2 (fragment :: completed) finalCaller queries finished outer waiting inventory memos
-                    (post.trans later) query entry ceiling fitted supported accepted
-              have tailLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
-              obtain ⟨fuel, outcome, running, resources⟩ := ih next reached final metadata after current bound retained rest uv
-                continuation admitted tailDone tailStopped afterPacket fitted supported (kept.trans post.effects.keeps)
-                afterMass tailLength tailGenuine shapes selectionMembers selectionLength admittedAfter growth tailConsumers
-              refine ⟨fuel, outcome, ?_, resources⟩
-              intro extra
-              simpa only [yes, tailDone, tailStopped, query] using running extra
-            · intro reached saved after outer waiting next final post query current retained fitted supported accepted
-              exact consumers.2 [] reached saved after outer waiting next final post query current retained fitted supported accepted
-          obtain ⟨fuel, outcome, running, resources⟩ := child inventory caller memos metadata before seed bound ceiling bucket
-            incoming uv tailPlan tailAdmitted yes no packet fits known available kept closed bounded pending mass bucketBound
-            ranked shapes selectionMembers selectionLength reserved tailGrowth headConsumers
-          refine ⟨fuel, outcome, ?_, resources⟩
-          intro extra
-          change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller before
-            memos.query (yes (fuel + extra)) (no (fuel + extra)) = outcome
-          exact running extra
-end ActualPlannedTuple
-
```

### checked1273 to checked1267

```diff
--- checked1273.lean
+++ checked1267.lean
@@ -923,3 +923 @@
-      EnumerationReferences.InputsAllowed allowed bucket →
-      (∀ uv, before.core.counter ≤ uv → allowed uv) →
-      EnumerationReferences.ReferencesAllowed allowed after.core) ∧
+      EnumerationReferences.InputsAllowed allowed bucket → EnumerationReferences.ReferencesAllowed allowed after.core) ∧
@@ -1029,2 +1027 @@
-        ⟨next, final, post, query, afterPacket, growth, origin, protects,
-          (fun allowed valid supplied _future => references allowed valid supplied),
+        ⟨next, final, post, query, afterPacket, growth, origin, protects, references,
@@ -1079 +1075,0 @@
-      (∀ uv, before.core.counter ≤ uv → allowed uv) →
@@ -1137,6 +1133,4 @@
-    · intro allowed valid allowedInputs future
-      apply tailReferences allowed (headReferences allowed valid (allowedInputs incoming bucket (by simp)) future)
-      · intro child retained member
-        exact allowedInputs child retained (List.mem_cons_of_mem _ member)
-      · intro uv inside
-        exact future uv (Nat.le_trans growth inside)
+    · intro allowed valid allowedInputs
+      apply tailReferences allowed (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
+      intro child retained member
+      exact allowedInputs child retained (List.mem_cons_of_mem _ member)
@@ -1173 +1167 @@
-    (fun _ valid _ _ => valid), ?_, ?_⟩
+    (fun _ valid _ => valid), ?_, ?_⟩
```

### checked1267 to failed1267

```diff
--- checked1267.lean
+++ failed1267.lean
@@ -1243 +1243 @@
-    EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
+    EagerChildComplete (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
```

### failed1267 to checked1179

```diff
--- failed1267.lean
+++ checked1179.lean
@@ -1179,88 +1178,0 @@
-section ActualConsumers
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private def ChildConsumers
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold) : Prop :=
-  (∀ fragment reached saved after,
-    ChildInputs formulas solver original metadata before bucket fragment reached saved after →
-    ∀ current retained, Fits current.2 reached.checked →
-      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
-      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
-      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
-        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome)) ∧
-  (∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
-      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
-      (next : Inventory) (final : Memos),
-    Post formulas solver next original reached final → final.query = saved →
-    ∀ current retained, Fits current.2 reached.checked →
-      Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap → admitted retained current →
-      ∃ fuel outcome,
-        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
-        OutcomeResources formulas solver reached (continuation retained current) (finish uv outcome))
-end ActualConsumers
-
-section ActualHeightBase
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private def EagerChildComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
-  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (bucket : List Suspended) (incoming : Node) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
-    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
-    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
-    Available captured incoming → SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
-    incoming.free = [] → (∀ sc ∈ bucket, sc.var < before.core.counter) → InputsPending before.core bucket →
-    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → bucket.length ≤ bound →
-    MergedOrdinaryHeight.height incoming ≤ height →
-    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
-      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
-        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
-          tries.length ≤ own) →
-    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
-    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
-    nodeReserved bits limit own height bound ceiling continuation admitted seed →
-    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
-    ChildConsumers formulas solver caller metadata before bucket uv continuation admitted done stopped →
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf bucket incoming caller
-        before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
-      OutcomeResources formulas solver caller
-        (nodePlan limit own height bound ceiling continuation seed) (finish uv outcome)
-
-private theorem eager_child_height_zero_complete
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
-    EagerChildComplete (bits := bits) checkEmpty edgesOf captured limit own 0 formulas solver := by
-  intro inventory caller memos metadata before seed bound ceiling bucket incoming uv continuation admitted done stopped
-    packet fits known capturedAvailable kept closed bounded pending mass bucketBound heightBound
-    _shapes _selectionMembers _selectionLength reserved _growth consumers
-  have fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false := by
-    cases incoming with
-    | empty => rfl
-    | reference name => rfl
-    | node entry rows depth free =>
-        simp only [MergedOrdinaryHeight.height] at heightBound
-        omega
-    | union entry members depth free => rfl
-    | mu entry body depth ordinary => rfl
-  exact eager_fallback_resources seed bound ceiling continuation admitted formulas solver inventory caller memos metadata
-    before checkEmpty edgesOf bucket incoming uv done stopped packet bounded pending
-    (kept.available incoming capturedAvailable) closed fits known mass bucketBound reserved fallback
-    (fun fragment reached saved after inputs bounded known mass accepted =>
-      consumers.1 fragment reached saved after inputs (advance seed (bound + 1)) (ceiling + bound)
-        bounded known mass accepted)
-    (fun reached saved after outer waiting next final post query bounded known accepted =>
-      consumers.2 reached saved after outer waiting next final post query (advance seed (bound + 1)) (ceiling + bound)
-        bounded known accepted)
-end ActualHeightBase
-
```

### checked1179 to failed1179

```diff
--- checked1179.lean
+++ failed1179.lean
@@ -1144 +1144 @@
-          tailGrowth child fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
+          tailGrowth fragment fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
@@ -1150 +1150 @@
-        exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held child
+        exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held fragment
```

### failed1179 to checked1057

```diff
--- failed1179.lean
+++ checked1057.lean
@@ -1057,122 +1056,0 @@
-section ActualTupleInputs
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private def TupleInputs
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached)
-    (inputs : List (Node × List Suspended)) (fragments : List Fragment)
-    (reached : Caller (bits + 2)) (queries : Queries) (after : Cached) : Prop :=
-  ∃ (next : Inventory) (final : Memos),
-    Post formulas solver next original reached final ∧ final.query = queries ∧
-    Packet formulas solver next reached final metadata after ∧ before.core.counter ≤ after.core.counter ∧
-    EnumeratedOrigin before.core after.core ∧
-    (∀ held fragment, before.core.values[held]? = some (.enumerated fragment) →
-      EnumerationDriver.Protected held before.core after.core) ∧
-    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-      (∀ child bucket, (child, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
-      EnumerationDriver.Protected held before.core after.core) ∧
-    (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
-      (∀ child bucket, (child, bucket) ∈ inputs → EnumerationReferences.InputsAllowed allowed bucket) →
-      EnumerationReferences.ReferencesAllowed allowed after.core) ∧
-    (∀ fragment ∈ fragments, FragmentBound after.core.counter fragment) ∧
-    ∀ fragment ∈ fragments, PendingFragment after.core fragment ∧
-      ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-        (∀ child bucket, (child, bucket) ∈ inputs → Avoids before.core.representatives held bucket) →
-        FragmentAvoid after.core.representatives held fragment
-
-private theorem child_then_tuple_inputs
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (genuine : ∀ child retained, (child, retained) ∈ (incoming, bucket) :: rest →
-      Available caller.checked.native.machine.heap child ∧ child.free = [] ∧
-      (∀ sc ∈ retained, sc.var < before.core.counter) ∧ InputsPending before.core retained)
-    (fragment : Fragment) (middleCaller : Caller (bits + 2)) (middleQueries : Queries) (middle : Cached)
-    (head : ChildInputs formulas solver caller metadata before bucket fragment middleCaller middleQueries middle) :
-    (∀ child retained, (child, retained) ∈ rest →
-      Available middleCaller.checked.native.machine.heap child ∧ child.free = [] ∧
-      (∀ sc ∈ retained, sc.var < middle.core.counter) ∧ InputsPending middle.core retained) ∧
-    ∀ fragments afterCaller saved after,
-      TupleInputs formulas solver middleCaller metadata middle rest fragments afterCaller saved after →
-      TupleInputs formulas solver caller metadata before ((incoming, bucket) :: rest)
-        (fragment :: fragments) afterCaller saved after
-    := by
-  obtain ⟨_middleInventory, _middleMemos, headPost, _headQueries, middlePacket,
-    growth, headOrigin, headProtected, headReferences, fragmentBound, fragmentPending, fragmentSeparate⟩ := head
-  have pending : InputsPending before.core bucket := (genuine incoming bucket (by simp)).2.2.2
-  have protects : ∀ held storedFragment, before.core.values[held]? = some (.enumerated storedFragment) →
-      EnumerationDriver.Protected held before.core middle.core := by
-    intro held storedFragment stored
-    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
-    exact headProtected held inside root (pending held storedFragment stored)
-  constructor
-  · intro child retained member
-    obtain ⟨childAvailable, childClosed, childBounded, childPending⟩ :=
-      genuine child retained (List.mem_cons_of_mem _ member)
-    refine ⟨headPost.effects.keeps.available child childAvailable, childClosed,
-      fun sc member => Nat.lt_of_lt_of_le (childBounded sc member) growth, ?_⟩
-    intro held storedFragment stored
-    have old := headOrigin held storedFragment stored
-    exact (protects held storedFragment old).avoids retained (childPending held storedFragment old)
-  · intro fragments afterCaller saved after tail
-    obtain ⟨next, final, tailPost, querySame, afterPacket, tailGrowth, tailOrigin,
-      tailProtected, tailRootsProtected, tailReferences, tailBounds, fragmentHistory⟩ := tail
-    refine ⟨next, final, headPost.trans tailPost, querySame, afterPacket, Nat.le_trans growth tailGrowth,
-      headOrigin.trans tailOrigin, ?_, ?_, ?_, ?_, ?_⟩
-    · intro held storedFragment stored
-      have first := protects held storedFragment stored
-      have middleStored : middle.core.values[held]? = some (.enumerated storedFragment) := first.value.trans stored
-      exact first.trans (tailProtected held storedFragment middleStored)
-    · intro held inside root avoids
-      have first := headProtected held inside root (avoids incoming bucket (by simp))
-      apply first.trans
-      apply tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root
-      intro child retained member
-      exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member))
-    · intro allowed valid allowedInputs
-      apply tailReferences allowed (headReferences allowed valid (allowedInputs incoming bucket (by simp)))
-      intro child retained member
-      exact allowedInputs child retained (List.mem_cons_of_mem _ member)
-    · intro child member
-      rcases List.mem_cons.mp member with rfl | member
-      · exact fragmentBound_mono _ _ tailGrowth _ fragmentBound
-      · exact tailBounds child member
-    · intro child member
-      rcases List.mem_cons.mp member with rfl | member
-      · refine ⟨pendingFragment_preserved middle.core after.core middlePacket.safe afterPacket.safe
-          tailGrowth fragment fragmentBound fragmentPending tailOrigin tailProtected, ?_⟩
-        intro held inside root avoids
-        have first := headProtected held inside root (avoids incoming bucket (by simp))
-        have last := tailRootsProtected held (Nat.lt_of_lt_of_le inside growth) first.root (by
-          intro child retained member
-          exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member)))
-        exact (fragmentAvoid_classes middle.core.representatives after.core.representatives held fragment
-          last.classes).mpr (fragmentSeparate held inside root (avoids incoming bucket (by simp)))
-      · obtain ⟨childPending, childSeparate⟩ := fragmentHistory child member
-        refine ⟨childPending, ?_⟩
-        intro held inside root avoids
-        have first := headProtected held inside root (avoids incoming bucket (by simp))
-        apply childSeparate held (Nat.lt_of_lt_of_le inside growth) first.root
-        intro child retained member
-        exact first.avoids retained (avoids child retained (List.mem_cons_of_mem _ member))
-
-private theorem tuple_inputs_nil
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (packet : Packet formulas solver inventory caller memos metadata before) :
-    TupleInputs formulas solver caller metadata before [] [] caller memos.query before
-    := by
-  refine ⟨inventory, memos, Post.refl packet.context, rfl, packet, Nat.le_refl _, .refl _, ?_, ?_,
-    (fun _ valid _ => valid), ?_, ?_⟩
-  · intro held fragment stored
-    exact EnumerationDriver.Protected.refl held before.core (enumerated_root before.core packet.safe held fragment stored).2
-  · intro held _ root _
-    exact EnumerationDriver.Protected.refl held before.core root
-  · intro fragment member
-    cases member
-  · intro fragment member
-    cases member
-
-end ActualTupleInputs
-
```

### checked1057 to checked381

```diff
--- checked1057.lean
+++ checked381.lean
@@ -1,7 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
-import MicroCFTA.EnumerationStratifiedTransport
-import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds
-import MicroCFTA.SourcePruningEnumerationSharedPreparedZeroOutcomeResources
-import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
-import MicroCFTA.SourcePruningEnumerationSharedChildResources
-import MicroCFTA.SourcePruningEnumerationSharedPreparedOutcomeResources
@@ -389,669 +381,0 @@
-
-namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
-open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
-open InternedConstructorTemplates InternedProbeProvenance
-open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
-open SourceCurrentAllocatedNativeInventoryState (Inventory)
-open SourceCurrentAllocatedPartialInvariant (Post)
-open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
-open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
-open SourcePruningEnumerationRecursive (Packet)
-open SourcePruningEnumerationSharedPreparedRecursive (OutcomeResources Output Failure finish)
-open SourcePruningEnumerationSharedSelectedContinuations
-local notation "Symbol" => SourcePruningTemplates.Symbol
-local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
-local notation "Node" => Value Symbol Constraint
-local notation "Caller" => SourceCurrentAllocatedPartialState.State
-local notation "Memos" => EndpointMemoGateTrace.Memos
-local notation "Queries" => SourceEndpointMemo.Memos
-local notation "Metadata" => SourcePruningRecordTypes.Metadata
-local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
-local notation "Fragment" => Fragments.Fragment Symbol
-local notation "Heap" => SourceEqualityAnnotationHeap.Heap
-local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
-variable {Typing : Type} {bits : Nat}
-local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
-local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries →
-  (Fragment → Caller (bits + 2) → Queries → Cached → Fold) →
-  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold
-
-section ActualFallback
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem fallback_complete_resources_cps
-    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
-    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
-    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (bucket : List Suspended) (incoming : Node)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
-    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
-    (fits : Fits seed.2 caller.checked)
-    (reserved : SourcePruningEnumerationSharedIncomingReservation.Reserved bits seed (bucket.length + 1))
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false) :
-    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
-      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
-      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
-      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
-        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
-          P H (k + extraIndex) bucket incoming caller before memos.query =
-          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
-      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
-      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
-      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
-      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
-      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
-        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
-      EnumeratedOrigin before.core after.core ∧
-      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
-      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
-        EnumerationReferences.InputsAllowed allowed bucket →
-        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
-      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
-      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
-        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
-        PendingFragment after.core fragment ∧
-        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-          Avoids before.core.representatives held bucket →
-          FragmentAvoid after.core.representatives held fragment) ∧
-      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
-      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap) ∧
-      (∀ er en P H ek, p ≤ P → h ≤ H →
-        ∀ (done : Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-          (stopped : ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
-        SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (r + er) (n + en) P H (k + ek)
-          edgesOf bucket incoming caller before memos.query done stopped =
-          match raw with
-          | [.ok (fragment, _returned)] => done fragment afterCaller savedQueries after
-          | _ => stopped ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) := by
-  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
-  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained⟩ :=
-    ChildDispatch.complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty bucket
-      incoming roots memos packet.context packet.safe paths counts flags realized bounded pending available closed
-      fits reserved known
-  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained, ?_⟩
-  intro er en P H ek representative native done stopped
-  rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty (r + er) (n + en) P H (k + ek)
-    edgesOf bucket incoming caller before memos.query done stopped fallback]
-  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
-  rw [retained.1 er en P H ek representative native]
-  cases raw with
-  | nil => rfl
-  | cons first rest =>
-      cases first with
-      | error fault => rfl
-      | ok returned =>
-          rcases returned with ⟨fragment, core⟩
-          cases rest <;> rfl
-end ActualFallback
-
-section ActualTuple
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem visitChildren_nil_resources
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
-    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
-    (actual : OutcomeResources formulas solver original seed (finish uv (done [] caller queries before))) :
-    OutcomeResources formulas solver original seed (finish uv
-      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped [] caller before queries)) := actual
-
-private theorem visitChildren_cons_resources
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
-    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
-    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
-    (good : Fragment → Caller (bits + 2) → Queries → Cached → Prop)
-    (bad : ChildDispatch.Observation (bits + 2) → Option Cached → Prop)
-    (head : ∀ yes no,
-      (∀ fragment reached saved after, good fragment reached saved after →
-        OutcomeResources formulas solver original seed (finish uv (yes fragment reached saved after))) →
-      (∀ observation candidate, bad observation candidate →
-        OutcomeResources formulas solver original seed (finish uv (no observation candidate))) →
-      OutcomeResources formulas solver original seed (finish uv
-        (visit bucket incoming caller before queries yes no)))
-    (tail : ∀ fragment reached saved after, good fragment reached saved after →
-      OutcomeResources formulas solver original seed (finish uv
-        (SourcePruningEnumerationSharedChildVisitors.visitChildren visit
-          (fun fragments => done (fragment :: fragments))
-          (fun completed => stopped (fragment :: completed)) rest reached after saved)))
-    (failed : ∀ observation candidate, bad observation candidate →
-      OutcomeResources formulas solver original seed (finish uv (stopped [] observation candidate))) :
-    OutcomeResources formulas solver original seed (finish uv
-      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped
-        ((incoming, bucket) :: rest) caller before queries)) := by
-  exact head
-    (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren visit
-      (fun fragments => done (fragment :: fragments))
-      (fun completed => stopped (fragment :: completed)) rest reached after saved)
-    (fun observation candidate => stopped [] observation candidate) tail failed
-end ActualTuple
-
-
-section ActualZero
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem resume_eager_zero_resources
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
-    (metadata : Metadata Typing) (decision : Option Next) (seed : Seed)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (bounded : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
-    ∃ outcome,
-      (∀ workFuel, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
-        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
-        metadata caller memos.query before decision = outcome) ∧
-      OutcomeResources formulas solver caller seed outcome := by
-  obtain ⟨outcome, running, resources⟩ :=
-    SourcePruningEnumerationSharedPreparedRecursive.resume_zero_outcome_resources holeKey fits admits graph templates
-      checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata decision seed packet bounded known
-  refine ⟨outcome, ?_, resources⟩
-  intro workFuel
-  rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_zero]
-  cases decision with
-  | none => simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
-  | some selected =>
-      cases selected <;> simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
-end ActualZero
-
-section ActualOrdinaryPrefix
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem ordinary_prefix_packet
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
-    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
-    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
-    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
-    (parentClosed : free = []) (selected : edge ∈ edges)
-    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
-    (allowed : arityAllows edge.children.length scs = true)
-    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
-    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
-    ∃ (roots : Nat → Nat) (action : EnumerateM Symbol Constraint
-        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
-      (own : Cached),
-      Roots before.core.representatives roots ∧
-      (SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
-      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
-        some [((edge.entry.key.symbol,
-          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
-            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own)] ∧
-      ExceptT.run (action before.core) =
-        [.ok ((edge.entry.key.symbol,
-          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
-            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own.core)] ∧
-      own.core = suspendedState tries.length before.core ∧
-      own.core.counter = before.core.counter + tries.length ∧
-      own.core.representatives = before.core.representatives ∧
-      Safe own.core ∧ Roots own.core.representatives roots ∧ PendingRealized caller.checked.native.machine.heap own.core ∧
-      EnumerationCanonicalWaiting.Correct roots own.core.values own.waiting ∧
-      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
-        ((own.core.values[slot]?).getD .eliminated) = some (own.expandable slot)) ∧
-      InputsPending own.core (scs ++ suspendedVars before.core.counter tries) ∧
-      (∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
-        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
-        (∀ sc ∈ bucket, sc.var < own.core.counter) ∧ InputsPending own.core bucket) ∧
-      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-        Avoids before.core.representatives held scs →
-        EnumerationDriver.Protected held before.core own.core ∧
-          ∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
-            Avoids own.core.representatives held bucket)) ∧
-      Packet formulas solver inventory caller memos metadata own ∧
-      SourcePruningEnumerationPrefixAdmission.suspendedBound own.core =
-        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
-      (∀ child bucket, (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
-        MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry edges depth free)) ∧
-      ∀ (visit : Visitor) (consume : SelectedEdge.Result (bits + 2) → Fold),
-        SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before memos.query =
-          SourcePruningEnumerationSharedChildVisitors.visitChildren visit
-            (fun fragments reached saved after =>
-              let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
-              consume (.complete fragment reached saved (SelectedEdge.finish residual fragment after)))
-            (fun completed observation candidate => consume (.stopped completed observation candidate))
-            (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) caller own memos.query := by
-  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
-  obtain ⟨action, own, retained⟩ := SourcePruningEnumerationEdgeInputs.complete
-    caller.checked.native.machine.heap parentEntry edges depth free edge scs roots
-    packet.context.ready.semantic.ready parentAvailable parentClosed selected before packet.safe realized
-    paths counts flags bounded pending allowed tries residual projected
-  refine ⟨roots, action, own, paths, retained, ?_⟩
-  obtain ⟨_prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, ownSafe,
-    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, _genuine, _ownProtects⟩ := retained
-  have origin : EnumeratedOrigin before.core own.core := by
-    rw [ownCore]
-    exact suspension_origin tries.length before.core
-  have protects (held : Nat) (inside : held < before.core.counter)
-      (root : IsRoot before.core.representatives held) :
-      EnumerationDriver.Protected held before.core own.core := by
-    rw [ownCore]
-    exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
-  have protectsEnumerated (held : Nat) (fragment : Fragment)
-      (stored : before.core.values[held]? = some (.enumerated fragment)) :
-      EnumerationDriver.Protected held before.core own.core := by
-    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
-    exact protects held inside root
-  have afterPending : EnumerationReferences.PendingReferences own.core := by
-    intro held fragment stored
-    have previous := origin held fragment stored
-    have incoming : EnumerationReferences.ReferencesAllowed
-        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
-      rw [ownCore]
-      exact EnumerationReferences.suspension_allowed _ tries.length before.core
-        (packet.pending held fragment previous)
-    intro value member sc listed related
-    exact incoming value member sc listed (((protectsEnumerated held fragment previous).classes sc.var).mp related)
-  have growth : before.core.counter ≤ own.core.counter := by rw [ownCounter]; omega
-  have ownPacket : Packet formulas solver inventory caller memos metadata own := by
-    refine ⟨packet.context, ownSafe, afterPending,
-      ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩, ?_, ?_⟩
-    · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
-      obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core own.core
-        ownSafe level frontier oldOrder origin protectsEnumerated
-      exact ⟨nextLevel, frontier, afterOrder⟩
-    · intro group member entry listed
-      exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
-  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
-  let staged := inputs.map (fun input =>
-    (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
-  have actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
-      some [((edge.entry.key.symbol, staged, residual), own)] := ownRun
-  have readback : staged.map (fun input => (input.1, input.2.1)) = inputs := by
-    dsimp only [staged]
-    simp only [List.map_map]
-    exact List.map_id _
-  refine ⟨ownPacket, ?_, ?_, ?_⟩
-  · rw [ownCore]
-    exact (SourcePruningEnumerationCachedOwn.suspendedState_scalars tries.length before.core).2
-  · intro child bucket member
-    obtain ⟨_tries, _projected, _inputs, lower⟩ := SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
-      caller.checked.native.machine.heap parentEntry edges depth free edge selected scs before own
-      edge.entry.key.symbol staged residual actual child bucket (by rw [readback]; exact member)
-    exact lower
-  · intro visit consume
-    unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
-    rw [actual]
-    simp only []
-    rw [readback]
-end ActualOrdinaryPrefix
-
-section ActualEagerCallback
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private def EagerResumeComplete
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat) : Prop :=
-  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
-    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
-    Packet formulas solver inventory caller memos metadata before →
-    Fits seed.2 caller.checked →
-    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
-    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
-    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
-    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
-    eagerReserved bits recursiveDepth seed ceiling →
-    ∃ bound outcome,
-      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
-          (bound + extra) (bound + extra) (bound + extra) edgesOf)
-        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
-        metadata caller memos.query before
-        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
-      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
-
-private theorem eager_resume_zero_complete
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
-    EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
-      formulas solver 0 := by
-  intro inventory caller memos before metadata seed ceiling packet bounded known
-    _selectionMembers _selectionLength _mass _reserved
-  obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey fits admits graph templates
-    checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata
-    (SourcePruningEnumerationRestart.decision stop order metadata before) seed packet bounded known
-  exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩
-
-private theorem callback_eager_induction_resources
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
-    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (recursiveDepth : Nat)
-    (recursive : EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
-      stop order formulas solver recursiveDepth)
-    (seed : Seed) (ceiling : Nat)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (allocated : FragmentBound before.core.counter fragment)
-    (bounded : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : eagerReserved bits recursiveDepth seed ceiling) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
-        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
-          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
-            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
-      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
-  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
-    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
-  change ∃ fuel outcome,
-    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
-      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
-    OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
-  obtain ⟨callbackFuel, result, after, returned, _stable, frame, _types, _holes, _typing,
-    _currentFits, _currentKnown, callback⟩ :=
-    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver inventory graph templates
-      metadata uv fragment caller memos before seed packet allocated bounded known
-  by_cases rejected : result.1 = true
-  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
-        (.complete [] caller memos.query) := by
-      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
-      intro output member
-      exact (List.not_mem_nil member).elim
-    have growth := eagerFinal_ge recursiveDepth seed ceiling
-    refine ⟨callbackFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2⟩
-    intro extra
-    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
-  · have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
-        (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
-      change SourcePruningEnumerationPrefixAdmission.suspendedBound after ≤ ceiling
-      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
-      exact mass
-    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
-      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
-      returned bounded known selectionMembers selectionLength massAfter reserved
-    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
-    intro extra
-    have actual := callback (resumeFuel + extra)
-    rw [← Nat.add_assoc] at actual
-    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
-    have observed := running (callbackFuel + extra)
-    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
-    rw [common] at observed
-    exact observed
-end ActualEagerCallback
-
-open SourceCurrentAllocatedNativeResourceForecast (Le)
-open SourcePruningEnumerationSharedIncomingReservation (advance_add)
-
-private theorem nodeReserved_fallback (bits limit own height bound ceiling : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
-    (reserved : nodeReserved bits limit own height bound ceiling continuation admitted seed) :
-    fallbackReserved bits bound ceiling admitted seed := by
-  cases height with
-  | zero => exact reserved
-  | succ height => exact reserved.1
-
-private theorem tupleReserved_first_callback (bits limit own height count bound ceiling : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
-    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      count bound ceiling continuation admitted seed) :
-    admitted (ceiling + count * bound) (advance seed (count * (bound + 1))) := by
-  induction count generalizing ceiling seed with
-  | zero => simpa only [tupleReserved, Nat.zero_mul, Nat.add_zero, advance] using reserved
-  | succ count ih =>
-      let tail := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
-      let covered := fun retained current => tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-        count bound retained continuation admitted current
-      have child : nodeReserved bits limit own height bound ceiling tail covered seed := reserved
-      have later := ih (ceiling + bound) (advance seed (bound + 1))
-        (nodeReserved_fallback bits limit own height bound ceiling tail covered seed child).2
-      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
-      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
-      rw [counts, advance_add, masses]
-      exact later
-
-private theorem first_callback_le_tuple_of_growth (limit own height count bound ceiling : Nat)
-    (continuation : Nat → Seed → Seed)
-    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
-    Le (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).2
-      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).2 ∧
-    (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).1 ⊆
-      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).1 := by
-  induction count generalizing ceiling seed with
-  | zero =>
-      simp only [Nat.zero_mul, Nat.add_zero, advance, tuplePlan]
-      exact ⟨Le.refl _, fun _ member => member⟩
-  | succ count ih =>
-      let child := nodePlan limit own height
-      let tail := fun retained current => tuplePlan child count bound retained continuation current
-      have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
-          current.1 ⊆ (tail retained current).1 := by
-        intro retained current
-        exact tuplePlan_ge child (nodePlan_ge limit own height) count bound retained continuation growth current
-      have first := ih (ceiling + bound) (advance seed (bound + 1))
-      have later := fallbackPlan_le_nodePlan limit own height bound ceiling tail tailGrowth seed
-      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
-      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
-      rw [counts, advance_add, masses]
-      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩
-
-section ActualTuplePadding
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem tuple_nil_reserved_resources
-    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed)
-    (admitted : Nat → Seed → Prop)
-    (growth : ∀ retained current, SourceCurrentAllocatedNativeResourceForecast.Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1)
-    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
-    (solver : SourceGuards.Entailment FullSyntax.Formula) (caller : Caller (bits + 2))
-    (memos : Memos) (before : Cached) (uv : Nat)
-    (visit : Nat → Visitor)
-    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (fits : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      count bound ceiling continuation admitted seed)
-    (consumer : ∀ retained current,
-      Fits current.2 caller.checked →
-      Heap (fun guard => guard ∈ current.1) caller.checked.native.machine.heap →
-      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ retained → admitted retained current →
-      ∃ fuel outcome, (∀ extra, done (fuel + extra) [] caller memos.query before = outcome) ∧
-        OutcomeResources formulas solver caller (continuation retained current) (finish uv outcome)) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren (visit (fuel + extra))
-        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
-  let entry := advance seed (count * (bound + 1))
-  have entryFits : Fits entry.2 caller.checked := fits.mono
-    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (count * (bound + 1)))
-  have entryKnown : Heap (fun guard => guard ∈ entry.1) caller.checked.native.machine.heap := by
-    intro key edge found
-    exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed
-      (count * (bound + 1)) (known key edge found)
-  have entryMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling + count * bound :=
-    Nat.le_trans mass (Nat.le_add_right _ _)
-  have entryAdmitted : admitted (ceiling + count * bound) entry :=
-    tupleReserved_first_callback bits limit own height count bound ceiling continuation admitted seed reserved
-  obtain ⟨fuel, outcome, running, resources⟩ := consumer (ceiling + count * bound) entry
-    entryFits entryKnown entryMass entryAdmitted
-  have included := first_callback_le_tuple_of_growth limit own height count bound ceiling continuation growth seed
-  exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
-end ActualTuplePadding
-
-section ActualChildInputs
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private def ChildInputs
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended)
-    (fragment : Fragment) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached) : Prop :=
-  ∃ (next : Inventory) (final : Memos),
-    Post formulas solver next original reached final ∧ final.query = queries ∧
-    Packet formulas solver next reached final metadata after ∧ before.core.counter ≤ after.core.counter ∧
-    EnumeratedOrigin before.core after.core ∧
-    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-      Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
-    (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
-      EnumerationReferences.InputsAllowed allowed bucket → EnumerationReferences.ReferencesAllowed allowed after.core) ∧
-    FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
-    ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-      Avoids before.core.representatives held bucket → FragmentAvoid after.core.representatives held fragment
-end ActualChildInputs
-
-section ActualFallbackResources
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_fallback_resources
-    (seed : Seed) (bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (bucket : List Suspended) (incoming : Node) (uv : Nat)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
-    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
-    (fits : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (bucketBound : bucket.length ≤ bound)
-    (reserved : fallbackReserved bits bound ceiling admitted seed)
-    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
-    (yes : ∀ fragment reached saved after,
-      ChildInputs formulas solver caller metadata before bucket fragment reached saved after →
-      Fits (advance seed (bound + 1)).2 reached.checked →
-      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
-      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound →
-      admitted (ceiling + bound) (advance seed (bound + 1)) →
-      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
-        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
-          (finish uv outcome))
-    (no : ∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
-        (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
-        (next : Inventory) (final : Memos),
-      Post formulas solver next caller reached final → final.query = saved →
-      Fits (advance seed (bound + 1)).2 reached.checked →
-      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
-      admitted (ceiling + bound) (advance seed (bound + 1)) →
-      ∃ fuel outcome,
-        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
-        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
-          (finish uv outcome)) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
-        edgesOf bucket incoming caller before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
-      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
-  have countLe : bucket.length + 1 ≤ bound + 1 := by omega
-  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
-    outer, waiting, retained, eagerExact⟩ := fallback_complete_resources_cps seed formulas solver inventory caller memos
-      metadata before checkEmpty edgesOf bucket incoming packet bounded pending available closed fits
-      (reserved.1.prefix countLe) known fallback
-  obtain ⟨headRun, post, query, growth, paths, storage, realized, counts, flags,
-    origin, protects, references, pendingAfter, shape, actualFits, actualKnown⟩ := retained
-  have paddedFits : Fits (advance seed (bound + 1)).2 afterCaller.checked :=
-    actualFits.mono (SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed countLe)
-  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
-      afterCaller.checked.native.machine.heap := by
-    have included : (advance seed (bucket.length + 1)).1 ⊆ (advance seed (bound + 1)).1 := by
-      obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le countLe
-      rw [same, advance_add seed (bucket.length + 1) extra]
-      exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge
-        (advance seed (bucket.length + 1)) extra
-    intro key edge found
-    exact included (actualKnown key edge found)
-  have observed : ChildDispatch.run checkEmpty r n p h k bucket incoming caller before memos.query =
-      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
-    simpa only [Nat.add_zero] using headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
-  have scalars := ChildDispatch.observed_scalar_bounds checkEmpty r n p h k bucket incoming
-    caller before memos.query after (congrArg Prod.snd observed)
-  have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound :=
-    Nat.le_trans scalars.2 (Nat.add_le_add mass bucketBound)
-  have completed : ∃ fuel outcome,
-      (∀ extra,
-        (match raw with
-        | [.ok (fragment, _returned)] => done (fuel + extra) fragment afterCaller savedQueries after
-        | _ => stopped (fuel + extra) ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) = outcome) ∧
-      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
-    rcases shape with rejected | ⟨fragment, singleton, afterSafe, fragmentBound, fragmentPending, fragmentAvoid⟩
-    · obtain ⟨fuel, outcome, running, resources⟩ := no afterCaller savedQueries after outer waiting next final
-        post query paddedFits paddedKnown reserved.2
-      refine ⟨fuel, outcome, ?_, resources.post post⟩
-      intro extra
-      rw [rejected]
-      exact running extra
-    · have protectsEnumerated (held : Nat) (storedFragment : Fragment)
-          (stored : before.core.values[held]? = some (.enumerated storedFragment)) :
-          EnumerationDriver.Protected held before.core after.core := by
-        obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
-        exact protects held inside root (pending held storedFragment stored)
-      have afterPacket : Packet formulas solver next afterCaller final metadata after := by
-        refine ⟨post.context, afterSafe, pendingAfter packet.pending,
-          ⟨afterRoots, paths, storage, realized, counts, flags⟩, ?_, ?_⟩
-        · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
-          obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core after.core
-            afterSafe level frontier oldOrder origin protectsEnumerated
-          exact ⟨nextLevel, frontier, afterOrder⟩
-        · intro group member entry listed
-          exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
-      have inputs : ChildInputs formulas solver caller metadata before bucket fragment afterCaller savedQueries after :=
-        ⟨next, final, post, query, afterPacket, growth, origin, protects, references,
-          fragmentBound, fragmentPending, fragmentAvoid⟩
-      obtain ⟨fuel, outcome, running, resources⟩ := yes fragment afterCaller savedQueries after inputs
-        paddedFits paddedKnown afterMass reserved.2
-      refine ⟨fuel, outcome, ?_, resources.post post⟩
-      intro extra
-      rw [singleton]
-      exact running extra
-  obtain ⟨callbackFuel, outcome, consumeRun, resources⟩ := completed
-  let total := r + n + p + h + k + callbackFuel
-  refine ⟨total, outcome, ?_, resources⟩
-  intro extra
-  let work := total + extra
-  have rle : r ≤ work := by dsimp [work, total]; omega
-  have nle : n ≤ work := by dsimp [work, total]; omega
-  have kle : k ≤ work := by dsimp [work, total]; omega
-  have re : r + (work - r) = work := by omega
-  have ne : n + (work - n) = work := by omega
-  have ke : k + (work - k) = work := by omega
-  have head := eagerExact (work - r) (work - n) work work (work - k)
-    (by dsimp [work, total]; omega) (by dsimp [work, total]; omega) (done work) (stopped work)
-  simp only [re, ne, ke] at head
-  change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work
-    edgesOf bucket incoming caller before memos.query (done work) (stopped work) = outcome
-  rw [head]
-  have actual := consumeRun (r + n + p + h + k + extra)
-  have same : callbackFuel + (r + n + p + h + k + extra) = work := by dsimp [work, total]; omega
-  simpa only [same] using actual
-end ActualFallbackResources
-
-end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
```

```json
[
  {
    "from": "checked1560",
    "to": "checked1475",
    "from_sha256": "292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232",
    "to_sha256": "e36d630f8bbf94f7881b6daa6a983d466664e599bd0df6c6b22210918314ee77",
    "patch_sha256": "475f5777cf9df17958432079b8ae997211193318034061b836f62dcfaaab7de5",
    "replayed_exact": true
  },
  {
    "from": "checked1475",
    "to": "failed1463",
    "from_sha256": "e36d630f8bbf94f7881b6daa6a983d466664e599bd0df6c6b22210918314ee77",
    "to_sha256": "e733903803302b70916e2340063fe893bf71e323d70bf849921a585948568269",
    "patch_sha256": "34f6e4a48bf667231a31279d99ad35f8ab9038ab9ab6863fec236ed9a4224274",
    "replayed_exact": true
  },
  {
    "from": "failed1463",
    "to": "checked1273",
    "from_sha256": "e733903803302b70916e2340063fe893bf71e323d70bf849921a585948568269",
    "to_sha256": "52c860fd8a92ccdfbde663a02ecb9afb9f9b041275e5edb0a025815fd0922d92",
    "patch_sha256": "dc07775f1fd5d011ada14e9486b25859db435f4db965900a318ae7fb38a24068",
    "replayed_exact": true
  },
  {
    "from": "checked1273",
    "to": "checked1267",
    "from_sha256": "52c860fd8a92ccdfbde663a02ecb9afb9f9b041275e5edb0a025815fd0922d92",
    "to_sha256": "8ce4041b06a0f2eba5b037570b649c8ff5e6f8927d768e879a3deffe2c27813b",
    "patch_sha256": "b07ee27f65c5401785e61b8fa9f3fab1d17d709116e2add5f091a6ca45464e04",
    "replayed_exact": true
  },
  {
    "from": "checked1267",
    "to": "failed1267",
    "from_sha256": "8ce4041b06a0f2eba5b037570b649c8ff5e6f8927d768e879a3deffe2c27813b",
    "to_sha256": "8f5b35234a38d083b898ad890c8ff6b8013e16ce32a9ab994bb805712872d319",
    "patch_sha256": "ffa1002609fb1acdd393f98728ce55f746d0a81a7d477514eaef32ed1714664a",
    "replayed_exact": true
  },
  {
    "from": "failed1267",
    "to": "checked1179",
    "from_sha256": "8f5b35234a38d083b898ad890c8ff6b8013e16ce32a9ab994bb805712872d319",
    "to_sha256": "dc0a4f85caad0271c40399476ee1863f083e31ba4dff5b8570343f63c9e9931a",
    "patch_sha256": "02291d41e204269fe274724a555cf166b0184a993b235ff0fe24aa58507bb6c8",
    "replayed_exact": true
  },
  {
    "from": "checked1179",
    "to": "failed1179",
    "from_sha256": "dc0a4f85caad0271c40399476ee1863f083e31ba4dff5b8570343f63c9e9931a",
    "to_sha256": "0b18ed3a958619b820aeaa48f1ee4348ec49e74d4e58d4ef39f1d967c7022434",
    "patch_sha256": "75a56ab17859315f360ddb9cd637cd580ea66ebb8921ed86db8fe4c3e6b06d47",
    "replayed_exact": true
  },
  {
    "from": "failed1179",
    "to": "checked1057",
    "from_sha256": "0b18ed3a958619b820aeaa48f1ee4348ec49e74d4e58d4ef39f1d967c7022434",
    "to_sha256": "a335c974561f4e7582dbc797d3b22877013187f9a213663f67716f6297a67277",
    "patch_sha256": "982a45e7704efd600eba0ee8b7d3c676a1d4058faa33c0252705537b0c638ee4",
    "replayed_exact": true
  },
  {
    "from": "checked1057",
    "to": "checked381",
    "from_sha256": "a335c974561f4e7582dbc797d3b22877013187f9a213663f67716f6297a67277",
    "to_sha256": "988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b",
    "patch_sha256": "f43645e43b3796136f390036a585d2e702599753cddf33bc3a845b22b19eb989",
    "replayed_exact": true
  }
]
```

## Frozen artifact: eager-resource-public-target-header.txt

SHA256 `01c37c9dabf7d093edb1741efeccf5c5d39378df0f7d76cfc7cf0883ea69b2fb`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
theorem runEager_finite_complete_resources
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
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome
```

## Frozen artifact: eager-cps-fresh-inputs-baseline-note.md

SHA256 `6f31a917416014a522ed3eed57750ca84aebb76ce0724940017ffa42793b830e`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Private fresh-reference baseline

Status at 2026-11-13 01:20 CET: ROOT strict compiler PASS.
The checked source has SHA52c860fd. ROOT is the sole compiler.

Source: `eager-cps-fresh-inputs-baseline.lean`, 1273 lines.
SHA256: `52c860fd8a92ccdfbde663a02ecb9afb9f9b041275e5edb0a025815fd0922d92`.

The source uses ROOT's checked height-zero1267/8ce4041b snapshot.
It retains the explicit private `Typing := Typing` correction.
All passed snapshots remain unchanged.

ROOT approved one private invariant correction at 01:12.
`ChildInputs` and `TupleInputs` now require future variables to satisfy
`allowed` when they assert `ReferencesAllowed` at the reached state.
The actual ordinary prefix can add fresh suspended references.
`EnumerationReferences.suspended_allowed` requires this condition.
The fallback producer already proves the stronger reference statement.
Its wrapper ignores the new premise.
The tuple proof transports future allowance through actual counter growth.
Its exact new section is Beta's124-line fragment, SHA68639b22.

This correction changes private induction contracts only.
The public20-line target, arithmetic plan and executable worker are unchanged.
No new public resource law is claimed.
No Haskell defect or concrete execution counterexample is claimed.
Closing old-root clients can derive future allowance with the existing
`EnumerationReferences.fresh_separate` from current Safe and root bounds.
Positive-height closure remains unproved.

The next private tuple-induction draft has explicit `Typing` parameters
on both abstract contract heads. Its source is not part of this baseline.
```

## Frozen artifact: eager-cps-generic-tuple-stage-note.md

SHA256 `37f77261231808ae9bad845a33a02f7ede151f68c7a139e2bc6e509e711a7235`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Actual eager tuple induction

Status at 2026-11-13 01:22 CET: UNCOMPILED candidate. ROOT is the sole compiler.

Source: `eager-cps-generic-tuple-stage.lean`, 1463 lines.
SHA256: `e733903803302b70916e2340063fe893bf71e323d70bf849921a585948568269`.
The source appends189 lines to the exact checked1273 fresh-reference baseline.
It preserves the public20-line target, all planner definitions and the worker.

The new private contracts are `TupleConsumers` and `EagerTupleComplete`.
The new private proofs are `eager_tuple_nil_resources` and
`eager_tuple_complete_of_child`.
Both abstract contract heads in the latter theorem specify `Typing`.
The private7-line header SHA is ad908c76959fdc2e21278da86e6c5a469341364908510cabd8ca8b9297f58131.

The tuple proof uses a private child-height hypothesis.
It inducts on the computed tuple count and the actual ordered input list.
Each actual head success runs the actual remaining tuple immediately.
The same head Post supplies the reached caller, full Memos and query identity.
The checked ChildInputs-to-TupleInputs proof supplies the actual tail data.
The proof threads the original captured heap through actual Keeps facts.
It retains the entire Fold and OutcomeResources at the computed tuple plan.
Normal rejection uses the actual stopped callback and its completed prefix.
A completed nil tuple uses the existing padding and admission proof.
No arbitrary consumer work bound is asserted.

The private child hypothesis must still be discharged by height induction.
Positive-height row scans and outer-depth closure remain unproved.
No new public eager resource law is claimed.
```

## Frozen artifact: eager-cps-generic-tuple-padded-note.md

SHA256 `ae56a188bb136cb4c80e53ee1b9c05c612322c02284ac3c4ce5932de1da0eace`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Stopped tuple admission padding

Status at 2026-11-13 01:33 CET: ROOT strict compiler PASS, SHAe36d630f.
ROOT is the sole compiler.
The failed1463/e733 snapshot remains unchanged.
The checked1273 prefix, definitions and private7-line header remain unchanged.

The stopped head has a tail admission, rather than the original admission.
The proof derives the original admission at the computed first tail callback.
It pads the current Fits and physical guard Heap along that same advance path.
It invokes the original stopped consumer at that entry.
The checked first_callback_le_tuple_of_growth then transports the entire
OutcomeResources to the existing tailPlan.

The actual caller, Memos, observation and candidate are unchanged.
The proof does not require Packet, Safe or a mass bound for the rejected cache.
It adds no worker, admission supplier or monotonicity premise.
The positive child-height hypothesis and public eager resource target remain unproved.
```

## Frozen artifact: eager-cps-own-tuple-inputs-stage-note.md

SHA256 `2b17781d4bcb2488c5fa6aeca9b1ef3721b8b6d996da14429747b1f3fdd064a1`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Actual own-prefix and tuple completion data

Status at 2026-11-13 01:34 CET: UNCOMPILED candidate. ROOT is the sole compiler.
Source: `eager-cps-own-tuple-inputs-stage.lean`, 1560 lines.
SHA256: `292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232`.

The source appends Beta's84-line fragment/d791af15 to checked1475/e36d630f.
The exact19-line own_tuple_child_inputs header/deed0c84 is unchanged.
The lemma observes the same own prefix and successful TupleInputs.
It derives the completed node fragment and the literal SelectedEdge.finish state.
It retains full Post, Memos, query identity and the reached Packet.
The current suspension and tuple histories supply origin and root protection.
The corrected future premise supplies every actual fresh own-class reference.
There is no additional producer, current Packet gate or future provider.

Checked1475 proves the generic ordered tuple resource step under the PRIVATE
child-height hypothesis. This candidate adds only the parent data composition.
The positive-height row scan, outer-depth closure and public target remain open.
All public arithmetic declarations and executable workers stay unchanged.
```

## Frozen artifact: private-eager-tuple-induction-header-typing.txt

SHA256 `ad908c76959fdc2e21278da86e6c5a469341364908510cabd8ca8b9297f58131`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
private theorem eager_tuple_complete_of_child
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver)
    (count : Nat) :
    EagerTupleComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver
```

## Frozen artifact: private-own-tuple-child-inputs-header.txt

SHA256 `deed0c840cf117eb50792544f0f2782bc76408ac522f29b3c54f07108c9eb683`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
private theorem own_tuple_child_inputs
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (caller : Caller (bits + 2)) (metadata : Metadata Typing) (before own : Cached)
    (edge : EdgeValue Symbol Constraint) (scs : List Suspended) (tries : List EqualityTrie.Trie)
    (residual : Option Constraint)
    (ownCore : own.core = suspendedState tries.length before.core)
    (ownCounter : own.core.counter = before.core.counter + tries.length)
    (ownProtects : ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
      Avoids before.core.representatives held scs →
      EnumerationDriver.Protected held before.core own.core ∧
        ∀ incoming bucket, (incoming, bucket) ∈
          SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
          Avoids own.core.representatives held bucket)
    (fragments : List Fragment) (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
    (history : TupleInputs formulas solver caller metadata own
      (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries)
      fragments reached saved after) :
    ChildInputs formulas solver caller metadata before scs (.node edge.entry.key.symbol fragments) reached saved
      (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
```

## Frozen artifact: private-eager-selected-resources-header.txt

SHA256 `d26193afdc7068e1a50252dc2f0825b5c2bdec06ab942cd2087363a538dbe354`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
private theorem eager_selected_resources
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (child : EagerChildComplete (Typing := Typing) (bits := bits)
      checkEmpty edgesOf captured limit own height formulas solver)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (fits : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ bound)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling continuation admitted seed)
    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
    (consumers : ChildConsumers formulas solver caller metadata before scs uv continuation admitted done stopped) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
        scs edge caller before memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
```

## Frozen artifact: eager-own-tuple-child-inputs-note.md

SHA256 `184ce52d0a35b81996548c70493db5f48a982447b84123060f076dcf6131be29`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Actual own prefix and tuple: parent child input assembly

2026-11-13 01:31 CET. Private runtime append fragment only.
Source: eager-own-tuple-child-inputs-fragment.lean.txt.
Lines: 84.
SHA256: d791af15a09d123091c48016e8b05cdb3f9726d8846fe7f3622e910fca456f79.
Append inside SourcePruningEnumerationSharedEagerReservation before its final end.
No compilation was run here. The combined candidate remains unverified.

Immutable basis: eager-cps-fresh-inputs-baseline.lean1273.
Basis SHA256: 52c860fd8a92ccdfbde663a02ecb9afb9f9b041275e5edb0a025815fd0922d92.
Exact private own_tuple_child_inputs header19L SHA256:
deed0c840cf117eb50792544f0f2782bc76408ac522f29b3c54f07108c9eb683.
There is one private helper and zero public laws.
The corrected ChildInputs and TupleInputs contracts remain unchanged.

The existing successful tuple receipt supplies Post, full final Memos,
the exact query identity, full afterPacket, growth, origin, protected roots,
reference preservation and every child fragment observer.
The literal ownCore and ownCounter give suspension origin and growth.
The actual ownProtects receipt gives the same old root frame and child avoids.
No initial Packet gate is needed in this data assembly.

The proof builds the literal node fragment from those exact fragments.
Its bound and pending facts come from every child. Its avoidance fact uses
the actual own root frame and the tuple's per-fragment class observer.
finish_safe permits the literal SelectedEdge.finish residual update.
The finished Packet retains the same native caller, full Memos, metadata,
cache indexes and dependency levels. Only obligations change.

Reference preservation uses suspension_allowed on the old store.
suspended_allowed admits exactly the fresh own-class variables from the
original private future allowance. Actual children retain the inherited
and fresh descents in the literal EdgeInputs.children order.
The tuple receives its future allowance through actual own counter growth.

The proof runs no worker. It adds no raw parent slot, ChildTraversal.Trace,
captured finalizer, recordTypes callback, resource plan or capacity gate.
It consumes successful tuple data. It infers no safe stopped candidate.
```

## Frozen artifact: next-eager-program-roles.md

SHA256 `c2a75a634ec54ac5d92526e469e6ed325d2f93b43894cc1fd22d28522a27b0e6`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Actual eager Program roles: private interface

Read-only audit, 2026-11-13 01:25 CET. No proof or source change is claimed.
All repository references below are under lean/MicroCFTA/.

## Pinned inputs

SourceSynthesisProgramRolesSharedDriver.lean, 1859L:
90b7611bfe4c131f59f287ed5f2a9ce0a3bf41bcc8f0e4754ba283a1a6e8a859.
SourceSynthesisProgramRolesChildTraversal.lean, 470L:
49f67f20dd4c3bd7cb6af23f470c5a405ff7baf32d1b26f0985185c1b42f6bba.
SourceSynthesisProgramRolesCapturedEdge.lean, 366L:
5724ecdbb0ed8b7c1b7d834c83baadf9441ef1d8d925af435174dad3b0e761a1.
SourcePruningEnumerationSharedEagerChildren.lean, 207L:
029464163b7288a5ddbaae95996307fab7acec77e7f70e5a661db948757423eb.
Alpha's UNVERIFIED 1463L resource/CPS stage:
/tmp/mcfta-eager-resource-cps-20261113-0000/eager-cps-generic-tuple-stage.lean,
e733903803302b70916e2340063fe893bf71e323d70bf849921a585948568269.

## Exact private addition to the resource CPS

Use the fixed current Symbol/Constraint/literal and existing local aliases.
Append this role observation to the SAME successful ChildInputs witness:

```lean
private def ChildRolesAt (valid : Constraint → Prop) (marked : Nat → Prop)
    (wanted : Prop) (before : Cached) (fragment : Fragment)
    (reached : Caller (bits + 2)) (after : Cached) : Prop :=
  ∃ extended : Nat → Prop,
    (∀ uv, marked uv → extended uv) ∧
    ProgramSlots valid literal reached.checked.native.machine.heap after.core extended ∧
    (wanted → FragmentRoles literal extended fragment) ∧
    (∀ retained : List Suspended,
      (∀ sc ∈ retained, sc.var < before.core.counter) →
      (∀ uv, marked uv → Avoids before.core.representatives uv retained) →
      ∀ uv, extended uv → Avoids after.core.representatives uv retained)
```

This groups role facts; it creates no new semantic/resource producer.
Current child inputs add ProgramSlots, all-mark bucket Avoids, and
`wanted → ValueFields valid literal incoming` plus valid annotation-only bucket paths.
The outer proof DERIVES these from current selected fields and actual child indices.
Type children use wanted=False. Never identify Program children by symbol alone.
In Alpha's ChildConsumers:1188, strengthen the successful ChildInputs:912 observation
with ChildRolesAt; retain its SAME Post/final Memos/query/Packet and all old fields.
Append per-output extending marks/ProgramSlots to the SAME returned OutcomeResources.
The done consumer remains PRIVATE; height/tuple/depth induction must discharge it.
Failure consumers keep their existing raw=[]/Post receipt: no Safe, Packet, or roles
are asserted for a rejected candidate. Only their emitted outputs need role receipts.
For TupleInputs:1063/TupleConsumers:1276, carry exact output length, one extended mark
set, and indexed fragment roles for the actual demanded child positions. Tail demand
is shifted by one. Transport completed fragment roles through later mark extensions.
The retained-bucket clause above is needed to establish the tail's CURRENT Avoids;
ProgramSlots alone does not establish this for external, unstored tail buckets.

## Existing local facts and two precise adapters

SourceSynthesisHereditaryProgramFields.lean:22 defines ValueFields/EdgeFields.
Program values are empty or ordinary nodes with full source layouts. They do not
license opaque whole-Program values. Component-name collisions retain their arity.
SourceSynthesisProgramChildScope.lean:92 derives child ValueFields, inherited empty
descent, exact own bucket and annotation paths from actual project/index operations.
SourceSynthesisProgramChildSources.lean:18 adds exact raw variable ranges.
SourceSynthesisProgramRolesClassAllocation.lean:57 observes actual suspendMany;
it preserves old marks/Protected roots. Fresh equality-class slots remain unmarked.
SourceSynthesisProgramRolesChildRetained.lean:23 supplies actual shallow allocation
roles, fresh Program marking and the retained-bucket clause for that exact success.
ChildTraversal.lean:43 has fragment monotonicity; :70 extracts actual shallow action.

Adapter 1: OwnInputs.lean:25 requires parentStored at :44-46. A direct eager child
need not occupy a raw slot. Observe SAME CachedOwn.prepare/EdgeInputs receipt using
CURRENT all-mark bucket Avoids instead. Reuse literal class allocation, not a
fabricated stored parent, desired after-role premise, or second own-input producer.
Adapter 2: ParentCallbackRoles.lean:115 requires shallow ChildTraversal.Trace.
Its use at :189-193 supplies fragment length. Do not invent that trace for eager
children. Its private assembled_roles:53 already proves the required static layout
fact from full EdgeFields, actual ordered length and child roles. Internal eager
consumeSelected only assembles a fragment: it does not finalize a captured target
or run recordTypes. Factor/copy that small assembly proof for the actual eager tuple.
At the actual outer captured parent, derive the SAME finalizer/callback receipt from
current post-child Packet/roles and actual ordered fragments. Existing FragmentWrite,
UnmarkedFinalize and computed_callback_complete (SharedDriver:110) cover those steps;
the current ParentCallback producer cannot be applied with a false shallow trace.

## Remaining induction and smallest next implementation

EagerChildren.lean:134 is literal eagerChild; :57/:184 prove actual prepared child
height decrease from SAME selected row/prepare receipt. No new height function.
The height IH must cover exact current endpoints and preserve the literal shallow
fallback, including the syntactic nondecreasing branch. Use the actual receipt to
discharge lower where applicable; do not assume every arbitrary child is lower.
The tuple IH must thread reached Caller/full Memos/Packet, index order, extended
marks, completed fragment roles and future tail avoidance. Beta owns future-reference
tuple bounds; pair that receipt with roles instead of producing another endpoint.
The sibling scan IH must use actual reached caller/query and captured-cache reset.
Depth IH must consume actual prefix/preparation/callback/restart receipts in
SharedPreparedRecursiveChildPolicy.lean:39/88. No shallow-run equality applies.

Smallest independent implementation: a private CURRENT bucket-Avoids observer for
SAME own allocation (adapter 1), preserving its full receipt and old ProgramSlots,
Protected roots and each actual child bucket Avoids. Then add ChildRolesAt inside
Alpha's existing CPS, followed by ordered tuple assembly; do not begin a public wrapper.
After full induction, SAME OutputResources Packet plus output roles permits one
PartialCompletion.complete_program_root call. SharedEagerOutputControl.lean:454
supplies finishedness for stop=None. It supplies no resources or role invariant.
No complete eager role theorem, output existence, model existence, adequate depth,
default Haskell correspondence, or whole enumeration completeness is claimed here.
```

## Frozen artifact: own-inputs-avoids-note.md

SHA256 `e376cb0989b0dc4f665fa01ab5ee2d6ab987f844268848a82f487d7efea2abdb`. The text describes its stated stage.
The selected-row header remains an unproved PRIVATE next target.
The 01:18 role audit predates the stopped-head repair and checked1560.

```text
# Current bucket avoidance through own-class preparation

Frozen unverified source, 2026-11-13 01:30 CET.
Source: SourceSynthesisProgramRolesOwnInputsAvoids.lean, 102 lines.
SHA256: b71aacf3fe300866849e3aecb52457f5f183b1512b25684f1bd4bb1146299ac2.
Public law: MicroCFTA.SourceSynthesisProgramRolesOwnInputsAvoids.complete_program_slots.

The 52-line public header is own-inputs-avoids-header.txt.
Header SHA256: 74a280974713d7a00754aded9994bd3366323ab9e06025910a826b6a472d3f2b.
The original OwnInputs header SHA256 is
3843362f5d9ced49548e2cc32f9c8e7446b6882ec6c9faeb486da3452684137c.
The complete conclusion is byte-identical. The sole input replacement is:

```lean
(avoids : ∀ held, marked held → Avoids before.core.representatives held scs)
```

It replaces parentSlot, parentNode and parentStored. This is the current fact that
the old proof obtained from ProgramSlots.incoming and its stored-parent witness.
The new primitive does not require the direct child to occupy a raw slot.

The proof invokes EdgeInputs.complete exactly once. It retains its full action,
cached preparation, raw singleton, exact core, counter, representatives, Safe,
roots, PendingRealized, waiting, candidate flags, combined pending inputs, actual
child availability/closedness/bounds/pending, and conditional protection receipt.
It observes the SAME cached preparation to obtain its literal suspendMany event.
ClassAllocation.suspendMany_program_slots then derives ProgramSlots for that
same allocation. Its _fresh component also derives that each fresh equality slot
is unmarked. The mark set stays unchanged. No new slot receives a Program mark.
The final protection and actual child-bucket separation use current avoids.

The source uses the same imports and instances as the checked old producer.
Only the namespace, module comment, replacement input and final proof step differ.
No old source was changed. No compiler, Git or runtime worker was run.
This is one current-input primitive. It does not establish eager roles, tuple or
sibling induction, finished output, a satisfying model, or whole completion.
```

## Reproduce

The registered Lean source contains every checked1560 declaration.
The portable checks validate the source and every public law. To reconstruct
a prior stage, apply the reverse patches and check its declared expected result.
Use the existing serial 4 GiB cap and the project Nix shell:

```sh
nix-shell ../shell.nix --run "lake env lean -j1 -DwarningAsError=true /tmp/checked1475.lean"
```
