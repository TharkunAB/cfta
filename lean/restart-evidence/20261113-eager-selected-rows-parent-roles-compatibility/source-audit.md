# Actual eager selected rows and captured row scan

Base: c3dcb344f20090b628c33a426a143d8907d9e431.
Main: e53852064d3ef5a2eafec47d754c27504b11de5f, fetched unchanged at 2026-11-13 01:55 CET.
Two modules contain 2147 lines and five public laws. One law is new.
The three old reservation arithmetic laws and old parent callback law remain.
All old public statements, proofs and execution definitions remain unchanged.
The new public law exposes the existing exact private parent fragment constructor.
The resource target runEager_finite_complete_resources remains UNPROVED and undeclared.
The private additions register ZERO new public resource laws.

The actual selected-row resource proof uses one own-prefix receipt, the actual
ordered child tuple under its PRIVATE lower-height hypothesis, and the same
successful parent fragment receipt. It calls the actual done continuation once.
The result retains the entire processed/output Fold and OutcomeResources.
A normal rejected tuple produces no output. Its resource proof uses the same
Post/query receipt. It assumes no Safe or Packet for a rejected candidate.
Unsupported projections and false arity retain their literal operational results.

The ordered row scan completes each row's callback before the suffix. It resets
the captured logical cache and metadata for each sibling. The actual native
Caller and complete Memos/Queries carry forward. Every processed/output prefix
survives. A stopped head skips the suffix. The remaining mathematical plan still
bounds the stopped prefix. The proof derives post-consumer transport, profile
padding and head/tail resource composition. It assumes the PRIVATE lower-height
child induction hypothesis. The actual guarded visitor equality, positive height
and outer-depth inductions remain open. It supplies no public future provider.

The public fragment_roles_of_children law is an insertion-only wrapper around
SAME private assembled_roles in its defining module. Its instance-free statement
keeps the same edge fields, actual ordered fragments, length and current child
roles. It adds no shallow Trace, finalizer, recordTypes, native operation, worker,
model or future role supplier. Eager tuple induction must derive its current inputs.
The old 17179-byte prefix and 56-byte suffix remain around its 12-line insertion.

The raw selected proof left a dependent match equality after consume_complete.
A case split of the same Fold closes it. One unused simp argument is removed.
The first scan draft lacked scoped iterate/iterate_ge names. One local open fixes
those names. The remaining scan rewrite needs the completed head match reduced
before rewriting the exact actual suffix. No statement, plan, operational code,
global option, heartbeat or linter setting is changed by these proof repairs.
They do not identify Haskell defects. All failed drafts remain reconstructible.

The strongest whole-path contracts remain cold SHALLOW current-input Program
outputs and the exact original-source language at its completed nodeCall endpoint.
Eager full resources and roles, shared backward source history, finite Type
solvability, output/depth adequacy, total work/host capacity, streams, both inverses
and Haskell correspondence remain open. The independent shared backward callback
branch is a PRIVATE next composition. It proves no satisfying assignment exists.
No Haskell source changed. The external Liquid repeated-name/refinement repair
remains with its owner. No Haskell tests are repeated for this Lean-only change.

## Exact public declarations

### SourceSynthesisProgramParentCallbackRoles

Source SHA256 `bef02ace96c7aa8364d19812bef2c00656de8ce66988dcfd29e065d7174b8914`. 259 lines.

```lean
theorem parent_callback_roles
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (target : Nat) (selected : marked target)
    (node : Option Nat) (targetScs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (checkEmpty : Bool) (r n p h k start : Nat) (scs : List Suspended)
    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (initialCaller caller : Caller width) (initial childrenAfter : Cached)
    (initialQueries : Queries) (memos : Memos) (fragments : List Fragment)
    (traversed : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.Trace checkEmpty r n p h k
      (SourcePruningEnumerationEdgeInputs.children edge scs start tries)
      initialCaller initial initialQueries fragments caller childrenAfter memos.query)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap childrenAfter.core marked)
    (stored : childrenAfter.core.values[target]? = some (.unenumerated node targetScs))
    (history : ∀ child ∈ fragments, PendingFragment childrenAfter.core child ∧
      FragmentAvoid childrenAfter.core.representatives target child)
    (seed : Seed) (packet : Packet formulas solver inventory caller memos metadata childrenAfter)
    (allocated : FragmentBound childrenAfter.core.counter (.node edge.entry.key.symbol fragments))
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
    ∃ (roots : Nat → Nat) (finalizeFuel : Nat) (before : Cached)
      (fuel : Nat) (result : Bool × Metadata Typing) (after : Core),
      ((∀ extra, SourcePruningEnumerationFinalize.run caller.checked.native.machine.heap
        (finalizeFuel + extra) target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter) = some before) ∧
      ExceptT.run (SourcePruningEnumerationFinalize.finish target (.node edge.entry.key.symbol fragments)
        (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core) =
        [.ok ((.node edge.entry.key.symbol fragments), before.core)] ∧
      before.core = {(SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core with
        values := childrenAfter.core.values.set target (.enumerated (.node edge.entry.key.symbol fragments)),
        expansionAncestry := []} ∧
      before.core.values[target]? = some (.enumerated (.node edge.entry.key.symbol fragments)) ∧
      before.expandable = (fun slot => if slot = target then false else childrenAfter.expandable slot) ∧
      before.waiting = EnumerationCanonicalWaiting.count roots (-1) (EnumerationSchedule.references
        (.unenumerated node targetScs : EnumerationState.UVarValue Symbol)) childrenAfter.waiting ∧
      Roots before.core.representatives roots ∧
      EnumerationCanonicalWaiting.Correct roots before.core.values before.waiting ∧
      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
        ((before.core.values[slot]?).getD .eliminated) = some (before.expandable slot)) ∧
      StorageValid before.core ∧ SourcePruningEnumerationObservation.PendingRealized caller.checked.native.machine.heap before.core ∧
      (Safe (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) childrenAfter).core →
        IsRoot childrenAfter.core.representatives target → Safe before.core)) ∧
      Packet formulas solver inventory caller memos metadata before ∧
      (Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata target (.inl (.node edge.entry.key.symbol fragments)) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments))) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata target
          (.inl (.node edge.entry.key.symbol fragments)) before.core) = [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → HookResult)
            stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (fuel + extra) metadata target (.node edge.entry.key.symbol fragments) caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      FragmentRoles literal marked (.node edge.entry.key.symbol fragments) ∧
      ProgramSlots valid literal caller.checked.native.machine.heap before.core marked ∧
      ProgramSlots valid literal caller.checked.native.machine.heap after marked
```

```lean
theorem fragment_roles_of_children (valid : Constraint → Prop) (marked : Nat → Prop)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (fragments : List Fragment) (length : fragments.length = edge.children.length)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child) :
    FragmentRoles literal marked (.node edge.entry.key.symbol fragments)
```

### SourcePruningEnumerationSharedEagerReservation

Source SHA256 `189d72cbd7d6d346d6a85355f50acf1c160e958a4ddd5e4c819c962c6c7ba6d7`. 1888 lines.

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

## Replayed source history

Start from registered checked1888. Apply the following reverse patches in order.
Every patch was applied with GNU patch --output and matched exact target bytes.
The previous1560 and all earlier proof stages remain in the preceding checkpoint.

```json
[
  {
    "stage": "checked1560",
    "lines": 1560,
    "source_sha256": "292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1715",
    "lines": 1715,
    "source_sha256": "0c92fd01ced50d425353271e3b76d53a6c651c6144da6dc2cc5e2a70395eceea",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1716",
    "lines": 1716,
    "source_sha256": "5986b7d73a746d57aa9020bc14d084a929be329a41444af451980d7a5a23d607",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1885",
    "lines": 1885,
    "source_sha256": "d6840247acb29d86a490fd70e976541db6e3f595a90701bd658313a3d77640ab",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "failed1886",
    "lines": 1886,
    "source_sha256": "f6439c492f5651e836ae0e7e8ca7dab37c23cfbe15ba41a07d4a25ebf18d28f6",
    "compiler_exit": 1,
    "new_public_resource_laws": 0
  },
  {
    "stage": "checked1888",
    "lines": 1888,
    "source_sha256": "189d72cbd7d6d346d6a85355f50acf1c160e958a4ddd5e4c819c962c6c7ba6d7",
    "compiler_exit": 0,
    "new_public_resource_laws": 0
  }
]
```

### checked1888 to failed1886

```diff
--- checked1888.lean
+++ failed1886.lean
@@ -1865,3 +1865 @@
-                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
-                dsimp only
-                rw [tailAt]
+                rw [SourcePruningEnumerationSharedBranching.scan, headAt, tailAt]
```

### failed1886 to failed1885

```diff
--- failed1886.lean
+++ failed1885.lean
@@ -1741 +1740,0 @@
-open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
```

### failed1885 to checked1716

```diff
--- failed1885.lean
+++ checked1716.lean
@@ -1716,169 +1715,0 @@
-section ActualRowsConsumers
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem child_consumers_post
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original middle : Caller (bits + 2)) (next : Inventory) (final : Memos)
-    (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (earlier : Post formulas solver next original middle final)
-    (consumers : ChildConsumers formulas solver original metadata before bucket uv continuation admitted done stopped) :
-    ChildConsumers formulas solver middle metadata before bucket uv continuation admitted done stopped := by
-  constructor
-  · intro fragment reached saved after data current retained fitted supported mass accepted
-    obtain ⟨next, final, post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩ := data
-    exact consumers.1 fragment reached saved after
-      ⟨next, final, earlier.trans post, query, packet, growth, origin, protects, references, bounded, pending, separate⟩
-      current retained fitted supported mass accepted
-  · intro reached saved after outer waiting next final post query current retained fitted supported accepted
-    exact consumers.2 reached saved after outer waiting next final (earlier.trans post) query
-      current retained fitted supported accepted
-end ActualRowsConsumers
-
-section ActualRowsResources
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private def EagerRowsComplete (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height count : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) : Prop :=
-  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
-    Packet formulas solver inventory caller memos metadata before → Fits seed.2 caller.checked →
-    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
-    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
-    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
-    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
-      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
-    Available captured (.node parentEntry rows depth free) → free = [] →
-    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
-    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
-    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
-    (∀ edge ∈ alternatives, edge ∈ rows) →
-    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
-      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
-        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
-          tries.length ≤ own) →
-    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
-    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
-    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      limit (bound + own) ceiling continuation admitted
-        (iterate (fun current => tuplePlan (nodePlan limit own height)
-          limit (bound + own) ceiling continuation current) seed index)) →
-    (∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1) →
-    ChildConsumers formulas solver caller metadata before scs uv continuation admitted done stopped →
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedBranching.scan
-        (fun edge reached saved cached => SourcePruningEnumerationSharedChildVisitors.visitSelected
-          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-          (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) reached saved)
-          scs edge reached cached saved) before alternatives caller memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (iterate (fun current => tuplePlan (nodePlan limit own height)
-          limit (bound + own) ceiling continuation current) seed count) (finish uv outcome)
-
-private theorem eager_rows_complete_of_child
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (child : EagerChildComplete (Typing := Typing) (bits := bits)
-      checkEmpty edgesOf captured limit own height formulas solver)
-    (count : Nat) :
-    EagerRowsComplete (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height count formulas solver := by
-  induction count with
-  | zero =>
-      intro inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
-        packet fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
-        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved growth _consumers
-      cases alternatives with
-      | cons edge rest => simp only [List.length_cons] at length; omega
-      | nil =>
-          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
-          exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
-  | succ count ih =>
-      intro inventory caller memos metadata before seed bound ceiling scs uv continuation admitted done stopped
-        packet fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
-        alternatives length selected shapes selectionMembers selectionLength reserved growth consumers
-      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
-      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
-        intro current
-        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
-          limit (bound + own) ceiling continuation growth current
-      cases alternatives with
-      | nil =>
-          have enlarged := iterate_ge row rowGrowth seed (count + 1)
-          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
-              caller.checked.native.machine.heap := by
-            intro key edge found
-            exact enlarged.2 (known key edge found)
-          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
-          exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
-            supported, rfl, rfl, fun _ member => by cases member⟩
-      | cons edge rest =>
-          have firstReserved := reserved 0 (by omega)
-          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_selected_resources
-            checkEmpty edgesOf captured limit own height formulas solver child inventory caller memos metadata before seed
-            bound ceiling scs uv continuation admitted done stopped packet fits known kept mass bucketBound
-            parentEntry rows depth free available closed ranked edge (selected edge (by simp)) bounded pending
-            shapes selectionMembers selectionLength firstReserved growth consumers
-          have farther := iterate_ge row rowGrowth (row seed) count
-          cases headOutcome with
-          | stopped processed outputs current =>
-              refine ⟨headFuel, .stopped processed outputs current, ?_, headResources.mono farther.1 farther.2⟩
-              intro extra
-              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
-          | complete processed outputs reached saved =>
-              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, outputResources⟩ :=
-                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
-                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources
-              have laterReserved : ∀ index, index < count →
-                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
-                intro index inside
-                exact reserved (index + 1) (by omega)
-              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
-              have reachedConsumers := child_consumers_post formulas solver caller reached next final metadata before scs uv
-                continuation admitted done stopped post consumers
-              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
-                bound ceiling scs uv continuation admitted done stopped reachedPacket reachedFits reachedKnown
-                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
-                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
-                selectionMembers selectionLength laterReserved growth reachedConsumers
-              let result : Fold := match tailOutcome with
-                | .complete later remaining finalCaller finalQueries =>
-                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
-                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
-              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
-              · intro extra
-                have headAt := headRunning (tailFuel + extra)
-                have tailAt := tailRunning (headFuel + extra)
-                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
-                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
-                rw [hs] at headAt
-                rw [ts, query] at tailAt
-                rw [SourcePruningEnumerationSharedBranching.scan, headAt, tailAt]
-                cases tailOutcome <;> rfl
-              · obtain ⟨lastCaller, lastInventory, lastMemos, lastPost, lastFits, lastKnown, shape⟩ := tailResources
-                refine ⟨lastCaller, lastInventory, lastMemos, post.trans lastPost, lastFits, lastKnown, ?_⟩
-                cases tailOutcome with
-                | complete later remaining finalCaller finalQueries =>
-                    obtain ⟨sameCaller, sameQueries, retained⟩ := shape
-                    refine ⟨sameCaller, sameQueries, ?_⟩
-                    intro output member
-                    rcases List.mem_append.mp member with old | fresh
-                    · exact (outputResources output old).mono farther.1 farther.2
-                    · exact (retained output fresh).post post
-                | stopped later remaining current =>
-                    obtain ⟨sameEndpoint, retained⟩ := shape
-                    refine ⟨sameEndpoint, ?_⟩
-                    intro output member
-                    rcases List.mem_append.mp member with old | fresh
-                    · exact (outputResources output old).mono farther.1 farther.2
-                    · exact (retained output fresh).post post
-end ActualRowsResources
-
```

### checked1716 to failed1715

```diff
--- checked1716.lean
+++ failed1715.lean
@@ -1684 +1683,0 @@
-              cases outcome <;> rfl
@@ -1709 +1708 @@
-        SourcePruningEnumerationCachedOwn.prepare, allowed]
+        SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte]
```

### failed1715 to checked1560

```diff
--- failed1715.lean
+++ checked1560.lean
@@ -1 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationCostBounds
@@ -1561,154 +1559,0 @@
-section ActualSelectedResources
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_selected_resources
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (child : EagerChildComplete (Typing := Typing) (bits := bits)
-      checkEmpty edgesOf captured limit own height formulas solver)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv : Nat)
-    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
-    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
-    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (fits : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (kept : SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (bucketBound : scs.length ≤ bound)
-    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
-    (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
-    (available : Available captured (.node parentEntry rows depth free)) (closed : free = [])
-    (ranked : MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1)
-    (edge : EdgeValue Symbol Constraint) (selected : edge ∈ rows)
-    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
-    (shapes : ∀ entry rows depth free, Available captured (.node entry rows depth free) →
-      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
-        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
-          tries.length ≤ own)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
-      limit (bound + own) ceiling continuation admitted seed)
-    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧ current.1 ⊆ (continuation retained current).1)
-    (consumers : ChildConsumers formulas solver caller metadata before scs uv continuation admitted done stopped) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitSelected
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        (SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query)
-        scs edge caller before memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
-  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
-    limit (bound + own) ceiling continuation growth seed
-  have planFits := fits.mono planGrowth.1
-  have planKnown : Heap
-      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
-      caller.checked.native.machine.heap := by
-    intro key edge found
-    exact planGrowth.2 (known key edge found)
-  by_cases allowed : arityAllows edge.children.length scs = true
-  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
-    | none =>
-        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
-        refine ⟨0, outcome, ?_, ?_⟩
-        · intro extra
-          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
-            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
-          rfl
-        · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
-          intro output member
-          cases member
-    | some fields =>
-        rcases fields with ⟨tries, residual⟩
-        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
-          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
-            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
-        obtain ⟨_prepared, _middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
-          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
-        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
-        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
-        have triesBound := edgeBounds.2 tries residual projected
-        have inputLength : inputs.length ≤ limit := by
-          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
-        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
-            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
-              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
-          intro value bucket member
-          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
-          have childRank := lower value bucket member
-          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
-          cases same
-          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
-          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
-            (suspendedVars before.core.counter tries)
-          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
-          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
-            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
-          simp only [List.length_append]
-          omega
-        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
-          rw [middleMass]
-          exact mass
-        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
-          fun fuel fragments reached saved after =>
-            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
-              (.complete (.node edge.entry.key.symbol fragments) reached saved
-                (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after))
-        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
-          fun fuel completed observation candidate =>
-            SourcePruningEnumerationSharedEagerChildren.consumeSelected (done fuel) caller memos.query
-              (.stopped completed observation candidate)
-        have tupleConsumers : TupleConsumers formulas solver caller metadata middle inputs uv continuation admitted yes no := by
-          constructor
-          · intro fragments reached saved after history current retained fitted supported afterMass accepted
-            have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
-              middleCore middleCounter middleProtects fragments reached saved after history
-            obtain ⟨fuel, outcome, running, resources⟩ := consumers.1 (.node edge.entry.key.symbol fragments)
-              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
-              data current retained fitted supported afterMass accepted
-            let receipt : SelectedEdge.Result (bits + 2) := .complete (.node edge.entry.key.symbol fragments)
-              reached saved (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)
-            let result : Fold := match outcome with
-              | .complete processed outputs finalCaller finalQueries => .complete (receipt :: processed) outputs finalCaller finalQueries
-              | .stopped processed outputs stop => .stopped (receipt :: processed) outputs stop
-            refine ⟨fuel, result, ?_, ?_⟩
-            · intro extra
-              change SourcePruningEnumerationSharedEagerChildren.consumeSelected (done (fuel + extra)) caller memos.query
-                (.complete (.node edge.entry.key.symbol fragments) reached saved
-                  (SelectedEdge.finish residual (.node edge.entry.key.symbol fragments) after)) = result
-              rw [SourcePruningEnumerationSharedEagerChildren.consume_complete, running extra]
-            · cases outcome <;> exact resources
-          · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
-            let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
-              ((.ok (some []), reached, saved, outer, waiting)) (some after)
-            let outcome : Fold := .complete [receipt] [] reached saved
-            have resources : OutcomeResources formulas solver reached current (finish uv outcome) := by
-              refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
-              intro output member
-              cases member
-            have enlarged := growth retained current
-            exact ⟨0, outcome, fun _ => rfl, resources.mono enlarged.1 enlarged.2⟩
-        have tuple := eager_tuple_complete_of_child (Typing := Typing) (bits := bits)
-          checkEmpty edgesOf captured limit own height formulas solver child limit
-        obtain ⟨fuel, outcome, running, resources⟩ := tuple inventory caller memos metadata middle seed
-          (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
-          inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
-        refine ⟨fuel, outcome, ?_, resources⟩
-        intro extra
-        rw [reducing]
-        exact running extra
-  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
-    refine ⟨0, outcome, ?_, ?_⟩
-    · intro extra
-      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
-        SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte]
-      rfl
-    · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
-      intro output member
-      cases member
-end ActualSelectedResources
-
```

### parent259 to parent247

```diff
--- parent259.lean
+++ parent247.lean
@@ -247,12 +246,0 @@
-omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
-/-- Ordered child roles determine the same assembled Program fragment. -/
-theorem fragment_roles_of_children (valid : Constraint → Prop) (marked : Nat → Prop)
-    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
-    (fragments : List Fragment) (length : fragments.length = edge.children.length)
-    (childrenRoles : ∀ index child,
-      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
-        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
-      fragments[index]? = some child → FragmentRoles literal marked child) :
-    FragmentRoles literal marked (.node edge.entry.key.symbol fragments) := by
-  exact assembled_roles valid marked edge fields fragments length childrenRoles
-
```

```json
[
  {
    "from": "checked1888",
    "to": "failed1886",
    "from_sha256": "189d72cbd7d6d346d6a85355f50acf1c160e958a4ddd5e4c819c962c6c7ba6d7",
    "to_sha256": "f6439c492f5651e836ae0e7e8ca7dab37c23cfbe15ba41a07d4a25ebf18d28f6",
    "patch_sha256": "702e8c8902832b6e93cbeb2cea5143799d528924e32fde48bc211fec66e6a36f",
    "replayed_exact": true
  },
  {
    "from": "failed1886",
    "to": "failed1885",
    "from_sha256": "f6439c492f5651e836ae0e7e8ca7dab37c23cfbe15ba41a07d4a25ebf18d28f6",
    "to_sha256": "d6840247acb29d86a490fd70e976541db6e3f595a90701bd658313a3d77640ab",
    "patch_sha256": "114e091f54f60bd52d28f0ac556e3f6b18322faa915a09471932151a0eb1422c",
    "replayed_exact": true
  },
  {
    "from": "failed1885",
    "to": "checked1716",
    "from_sha256": "d6840247acb29d86a490fd70e976541db6e3f595a90701bd658313a3d77640ab",
    "to_sha256": "5986b7d73a746d57aa9020bc14d084a929be329a41444af451980d7a5a23d607",
    "patch_sha256": "afb1e8a24df565e5c57c50d3a78d1a7d0194c033d66f5df7fb5b738eb702cee6",
    "replayed_exact": true
  },
  {
    "from": "checked1716",
    "to": "failed1715",
    "from_sha256": "5986b7d73a746d57aa9020bc14d084a929be329a41444af451980d7a5a23d607",
    "to_sha256": "0c92fd01ced50d425353271e3b76d53a6c651c6144da6dc2cc5e2a70395eceea",
    "patch_sha256": "c92f6482e9189a9b28cade3c6cf5fc3d71298646c22e0375170fdb279f5fdeba",
    "replayed_exact": true
  },
  {
    "from": "failed1715",
    "to": "checked1560",
    "from_sha256": "0c92fd01ced50d425353271e3b76d53a6c651c6144da6dc2cc5e2a70395eceea",
    "to_sha256": "292d2bf695c43d7fe2df06346c5a14deaf2bb0a8f943c041d67d27e8496fe232",
    "patch_sha256": "9b4b12d583659e442c767e8ab41cdeeae8b8a7ab31ca2caf2cea29f7c44f9a86",
    "replayed_exact": true
  },
  {
    "from": "parent259",
    "to": "parent247",
    "from_sha256": "bef02ace96c7aa8364d19812bef2c00656de8ce66988dcfd29e065d7174b8914",
    "to_sha256": "ebd3ad2cfdfa37119e861851a8ec4948673f8b26e40e0b98ae9a19454328a1c6",
    "patch_sha256": "cf66d1eb857c18227c914dccec2a8c230b4dc58a1a1020c60ed7a8b3ebb9d78b",
    "replayed_exact": true
  }
]
```

## Frozen artifact: eager-cps-selected-resources-stage-note.md

SHA256 `182d1dd8baf5965bc47059c75eb37dc2eb7977400499b89d02e8fcadd29d1f71`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
# Actual selected eager row resources

Status at 2026-11-13 01:53 CET: ROOT strict compiler PASS after two local proof repairs.
Checked1716 SHA5986b7d7. ROOT is the sole compiler.
Source: `eager-cps-selected-resources-stage.lean`, 1715 lines.
SHA256: `0c92fd01ced50d425353271e3b76d53a6c651c6144da6dc2cc5e2a70395eceea`.
The exact41-line private header has SHAd26193af.

The source appends153 lines to checked1560/292d2bf6.
It adds one pure operational dependency, SourcePruningEnumerationCostBounds.
It retains the entire checked arithmetic body and worker definitions.
The old and new source snapshots remain separate.

The private row theorem invokes the actual own prefix once.
It derives captured child availability, strict child height, arity and bucket widths.
The actual ordered eager tuple uses the checked lower-height hypothesis.
The same successful tuple yields the parent fragment and residual state.
The actual done continuation runs once at that state.
The completed parent receipt is prepended to its entire complete or stopped Fold.
The resource proof preserves this full operation and its actual caller and Memos.
Normal child rejection keeps the reached Post and query state.
It does not require Safe or Packet for the rejected candidate.
Unsupported projection and rejected arity retain the literal old result.

This theorem is private and conditional on the lower-height hypothesis.
The actual eagerChild scan still needs its prepared-child guard rewrite,
ordered sibling composition, positive-height closure and outer-depth closure.
No new public eager resource law is claimed.
```

## Frozen artifact: eager-cps-row-scan-resources-stage-note.md

SHA256 `c6d51f4c63ec1621dc3b3b91cbc75fcacf6b4b7e2fdea10c0baf89f9d3969956`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
# Actual ordered eager row scan resources

Status at 2026-11-13 02:06 CET: ROOT strict compiler PASS after scoped names
and one match reduction. Checked1888 SHA189d72cb. ROOT is the sole compiler.
Source: `eager-cps-row-scan-resources-stage.lean`, 1885 lines.
SHA256: `d6840247acb29d86a490fd70e976541db6e3f595a90701bd658313a3d77640ab`.

The source appends168 lines to ROOT's exact checked1716/5986b7d7.
The new private EagerRowsComplete contract has41 lines, SHA3e341651.
The private8-line induction header has SHA4a41cef8.
The new private child_consumers_post composes the actual prior Post.
It changes no actual worker or arithmetic definition.

The scan proof invokes each actual eager selected-row producer once.
A completed row supplies the actual next caller and full Memos.
The next row receives the original captured enumeration cache and metadata.
The original captured heap remains available through the composed Keeps.
The proof invokes the same continuation family at each actual row success.
It retains all ordered processed receipts, outputs and stopped prefixes.
It appends head and tail resource receipts at their exact endpoints.
It pads only along the same iterate schedule.
The empty actual suffix uses that same schedule's growth.
No rejected candidate is assumed to satisfy Packet or Safe.

The private lower child-height hypothesis remains an input to this lemma.
The actual eagerChild worker still needs its prepared-child guard equality,
positive-height closure and outer-depth closure.
No new public eager resource law is claimed.
```

## Frozen artifact: private-eager-selected-resources-header.txt

SHA256 `d26193afdc7068e1a50252dc2f0825b5c2bdec06ab942cd2087363a538dbe354`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

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

## Frozen artifact: eager-parent-role-assembly.md

SHA256 `52031310528721420f613e9f67983e9377751eacbc0af77ad0fe8673aa05673e`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
# Eager parent fragment roles after the actual tuple

Read-only audit, 2026-11-13 01:41 CET. No source or proof was changed.
Repository references below are under lean/MicroCFTA/.

## Exact result

The pure parent assembly proof already exists at
SourceSynthesisProgramParentCallbackRoles.lean:53, private assembled_roles.
Its entire statement is the proposed public primitive in
program-fragment-assembly-header.txt. Only private and its enclosing namespace
change. This header has no instances, native heap, cache, Packet, worker, callback,
model, guard evaluation or future-provider argument.

Its CURRENT inputs are full EdgeFields, the actual ordered fragment list, equality
with the original child count, and roles for app positions 2/3 or filter position 1.
It concludes FragmentRoles of the literal node over that SAME fragment list.
It does not construct children or assert that a successful tuple exists.

## Existing proof and named dependencies

ProgramEnumerationRoles.lean:24 defines FragmentRoles.
The proof cases on HereditaryProgramFields.EdgeFields:33, not symbol alone:
annotated uses FragmentRoles.component; application uses .application; filter
uses .filter. Type annotation and marker fragments need no Program-role proof.
Component names can equal app/filter: the annotated case still has one child.
Full field layouts keep it separate from app4 and filter2.
The existing private cons_of_length:46 uses cases/List.length_cons/omega.
Other list facts are List.length_eq_one_iff and List.length_eq_zero_iff.
The source proof at ParentCallbackRoles:53-85 already closes every assembly case.
It is not accessible by a normal name outside its module. Do not use a mangled name.
A later visibility change or additive pure primitive can make that proof reusable.

## Exact replacement for shallow Trace

ParentCallbackRoles.parent_callback_roles:115 takes ChildTraversal.Trace at :127.
Its only operational use is :189-192: traversal_length derives the fragment count.
Replace that use with a count field DERIVED in the actual eager tuple CPS receipt.
The tuple success observation must retain the SAME Post/full Memos/query/Packet,
extended marks and ProgramSlots at its reached Caller/cache, plus:

```lean
fragments.length = inputs.length
```

It also retains indexed FragmentRoles under the final mark set for exactly the
Program-demanded positions. The old mark set is included in the final one.
The nil tuple proves length by rfl. The cons tuple adds the SAME actual head
fragment; congrArg Nat.succ transports the tail equality, with List.length_cons.
Shift the tail's demanded index by one. Transport prior fragment roles through
later mark extensions; ChildTraversal.lean:43 contains private fragment_mono.
That mark transport and tail bucket avoidance remain tuple IH obligations.
Do not infer length or child origins from a bare equality of CPS result values.

At actual selected completion, CachedOwn.prepare's SAME receipt identifies staged
with EdgeInputs.children.map. SharedChildVisitors.visitSelected:49 maps staged in
the original order. Simplification with SourcePruningEnumerationEdgeInputs.children,
List.length_map and List.length_zipIdx gives fragments.length=edge.children.length.
The pure assembly law then yields parent roles using the final extended mark set.

## Actual action boundary

SharedChildVisitors.visitChildren:35 calls the tail INSIDE the actual head success.
The proof must retain that reached Caller/cache/query; it cannot use the initial
caller for later children. A stopped tuple has only a completed prefix. Do not
give that prefix the full length or assemble it as a complete parent node.
visitSelected:49 builds the node, records its residual and calls consume.
SelectedEdge.finish:33 changes obligations only. ProgramSlots transports through
that literal update because counter, representatives and values are unchanged.
EagerChildren.consumeSelected:42 invokes done with the same assembled fragment.
It does not finalize a raw target or record types for an internal eager child.
Actual captured-target finalization/callback occurs outside this pure child step.
Keep the existing full resource receipt when reaching that later boundary.

## Pins and remaining boundary

ParentCallbackRoles247 SHA256:
ebd3ad2cfdfa37119e861851a8ec4948673f8b26e40e0b98ae9a19454328a1c6.
ProgramEnumerationRoles87 SHA256:
e31274ac2cb247cb8d20267c4253ecaf1de8520886ed8f003b267d59bd3f5c84.
SharedChildVisitors SHA256:
fd0ae3de1e211fe36d06a4bfd1908145a4990dc6ae92a6be89c772e759e35339.
The primitive is pure syntax. Height, tuple, sibling and outer restart induction
must derive its inputs at actual endpoints. No eager role theorem, satisfying
assignment, output existence or whole completion follows from assembly alone.
```

## Frozen artifact: program-fragment-assembly-header.txt

SHA256 `c04221cf6f2ababfc7766343a6861be6dd7ae7bd94e2dc6372b6063a993dad6e`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles

namespace MicroCFTA.SourceSynthesisProgramFragmentAssembly
open InternedConstructorTemplates
open SourceSynthesisHereditaryProgramFields (EdgeFields)
open SourceSynthesisProgramEnumerationRoles (FragmentRoles)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

theorem assembled_roles (valid : Constraint → Prop) (marked : Nat → Prop)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (fragments : List Fragment) (length : fragments.length = edge.children.length)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child) :
    FragmentRoles literal marked (.node edge.entry.key.symbol fragments)
```

## Frozen artifact: parent-fragment-api-note.md

SHA256 `ebd1e59ecb475811133e47ee70a73caff4ef62858c5a4469f8536ed01c6e0c77`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
# Public access to the existing parent fragment constructor

Frozen runtime snapshot, 2026-11-13 01:46 CET. The snapshot is unverified.
The existing repository module was not changed.

Original: SourceSynthesisProgramParentCallbackRoles-original-ebd3ad2c.lean, 247L.
SHA256: ebd3ad2cfdfa37119e861851a8ec4948673f8b26e40e0b98ae9a19454328a1c6.
New snapshot: SourceSynthesisProgramParentCallbackRoles.lean, 259L.
SHA256: bef02ace96c7aa8364d19812bef2c00656de8ce66988dcfd29e065d7174b8914.

One additive public law is inserted before the existing final namespace end:
MicroCFTA.SourceSynthesisProgramParentCallbackRoles.fragment_roles_of_children.
Its 8-line statement is the old private assembled_roles statement, with only the
declaration name and private modifier changed. The earlier 20-line proposal also
included its 12-line standalone import/namespace/notation prelude. This snapshot
reuses the original module prelude and adds no import or namespace.

Header file: fragment-roles-of-children-header.txt.
SHA256: f60bdcb5ba3a2fd02584ab7d87b296cd8b10b83c69e4b097e0b6f94a2b015b4b.
Insertion file: fragment-roles-of-children-insertion.txt, 12L.
SHA256: fae475899526e3e25a596ec93bb2fe2aa18115ec6473e069058f4fc6e91690f6.

The proof applies SAME private assembled_roles exactly once. No old declaration,
header, proof, definition, import or namespace end was changed. The original
17179-byte prefix and 56-byte suffix are byte-identical. Removing the insertion
reconstructs the complete original source with its recorded SHA256.
The insertion narrowly omits the three current section DecidableEq instances.
The original private constructor precedes those instances and needs none of them.
This preserves its exact instance-free public domain and avoids unused parameters.

This law only constructs FragmentRoles from complete source fields, the same
ordered fragment list/count and current child roles. It adds no Trace, Finalize,
recordTypes, native effects, worker, model or role-provider premise. Actual eager
tuple induction must still derive those current fragment facts at its endpoint.
No compiler, Git, Haskell, repository, root documentation or evidence edit was run.
```

## Frozen artifact: fragment-roles-of-children-header.txt

SHA256 `f60bdcb5ba3a2fd02584ab7d87b296cd8b10b83c69e4b097e0b6f94a2b015b4b`. The note describes its stated stage.
Later strict results and local repairs are recorded above.

```text
theorem fragment_roles_of_children (valid : Constraint → Prop) (marked : Nat → Prop)
    (edge : EdgeValue Symbol Constraint) (fields : EdgeFields valid literal edge)
    (fragments : List Fragment) (length : fragments.length = edge.children.length)
    (childrenRoles : ∀ index child,
      ((edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
        (edge.entry.key.symbol = literal "filter" ∧ index = 1)) →
      fragments[index]? = some child → FragmentRoles literal marked child) :
    FragmentRoles literal marked (.node edge.entry.key.symbol fragments)
```

## Reproduce

Both current modules are regular Lean source. Run their portable packets and
the compatibility check under the existing serial Nix 4 GiB cap. The reverse
patches reconstruct every failed intermediate draft without an execution archive.
