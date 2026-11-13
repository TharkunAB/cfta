# Actual eager captured finalization and ordered rows

Base: d0ba3af8bbce22ad09ecca2040499db001f2719e.
Main: e53852064d3ef5a2eafec47d754c27504b11de5f, fetched unchanged at 2026-11-13 02:30 CET.
One existing module contains 2487 lines and three inherited public arithmetic laws.
ZERO new public resource or role laws are added. All old public statements,
proofs and execution definitions remain. The full public eager resource target
remains UNPROVED and undeclared. Preparation and outer depth remain open.

The private finalization observer uses CURRENT Ready/stored/IncomingAvoid and
SAME observed ChildInputs. ONE actual Finalize.complete supplies SAME extracted
inventory, complete Memos, Post/query, all-larger-fuel run, exact written core,
whole afterPacket, fragment bound, mass bound, stored target and root. Corrected
reference preservation plus current future-variable separation derive incoming
avoidance at the actual middle. No future Packet or model is supplied.

The captured-row CPS proof uses the public actual visitCapturedWith equation.
The SAME own preparation and ordered tuple feed ONE checked finalizer and ONE
actual continuation callback. It retains the FINALIZED receipt or stopped hook
endpoint, complete Memos and entire Fold/OutcomeResources. It does not insert
an extra unfinalized receipt from internal consumeSelected. The actual closed
child-height proof discharges child/consumer hypotheses inside this composition.
Only the PRIVATE concrete lower-depth resume hypothesis remains. Unsupported
projection, false arity and normal empty raw result keep their literal outcomes.

The captured ordered scan calls that actual row producer. Each sibling clones
the captured logical cache/metadata while the actual native Caller and complete
Memos/Queries carry forward. Full processed/output prefixes append. A stopped
head skips its suffix. Post and deterministic profile padding compose all
resources. There is no remaining private child or consumer provider at this
scan boundary; it uses only the private actual lower-depth resume hypothesis.
The full preparation/terminal/opaque and outer-depth closure still must be proved.

The first captured draft used reserved Lean token matches as a private bound
name. It failed parsing. Rename that binder and its five uses to keyMatches;
this changes only a private bound-variable name. The public20-line header stays
unchanged. The next draft failed a large change conversion of the local hook
under its receipt match. Rewrite via the SAME explicit callback equality at
that local hook, then split the SAME complete/stopped hook outcome. This keeps
all finalized receipts/endpoints/resources. No statement premise or operational
code, plan, global option, heartbeat or linter setting changes.

A PRIVATE51-line tuple-count congruence also passes. Success callbacks only need
to agree on fragment lists whose length is the SAME actual input count, at the
SAME reached caller/query/cache. Literal visitChildren nil/cons congruence proves
the entire fold equality. The visitor and stopped callback stay unchanged. No
visitor behavior, resource, Native or model assumption is added. This is a
private role-proof primitive; it creates no public role theorem or shallow Trace.

The strongest whole-path Program contract remains cold SHALLOW current-input
execution. The exact original-source language proof has its distinct completed
nodeCall endpoint. Full eager resources/roles, shared original-source history,
finite satisfying Type assignments, output/depth adequacy, total work/host word
capacity, streams, both inverses and Haskell correspondence remain separate.
No Haskell source changed or Haskell test repeated. External Liquid repair
ownership stays unchanged. These local Lean repairs are not Haskell defects.

## Exact inherited public declarations

Source SHA256 `e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e`.

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

## Replayed captured source history

Start from live checked2487. Apply these reverse patches in order.
Every patch was applied with GNU patch --output and matched exact target bytes.
Every earlier stage remains in the preceding checkpoint.

```json
[
  {
    "stage": "checked2053",
    "lines": 2053,
    "source_sha256": "c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "checked2121",
    "lines": 2121,
    "source_sha256": "56fe353ada3be3aa0d8339e66e3730ac061815bebb5c12201c1c0c2bccd327d8",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "failed2339",
    "lines": 2339,
    "source_sha256": "f11dfbcb1923491469f96169db77973d74d62413bae0783076bddc605f8e20ea",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "failed2339Key",
    "lines": 2339,
    "source_sha256": "ba55fc2d55454b9171079a792ce7642a08eac7d9b2d2833cb0790cffebf98652",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "checked2333",
    "lines": 2333,
    "source_sha256": "ba3bb2d3ef2ea93db6e3cb4bd91ad405f7c61936fe0cb8a5f3dcc57fa67ede74",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "checked2487",
    "lines": 2487,
    "source_sha256": "e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e",
    "compiler_exit": 0,
    "new_public_laws": 0
  }
]
```

### checked2487 to checked2333

```diff
--- checked2487.lean
+++ checked2333.lean
@@ -2333,154 +2332,0 @@
-section ActualCapturedRowsResources
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)
-
-private theorem eager_captured_rows_resources
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat)
-    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
-      stop order formulas solver recursiveDepth)
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
-  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
-    Packet formulas solver inventory caller memos metadata before →
-    EnumerationDriver.Ready uv before.core →
-    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
-    EnumerationReferences.IncomingAvoid uv before.core →
-    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
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
-      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
-        (fun retained current => eagerReserved bits recursiveDepth current retained)
-        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
-          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedBranching.scan
-        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
-          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
-            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-            graph templates stop order (fuel + extra) metadata uv)
-          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
-      OutcomeResources formulas solver caller
-        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
-          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
- := by
-  induction count with
-  | zero =>
-      intro inventory caller memos metadata before seed bound ceiling scs uv handle
-        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending
-        alternatives length _selected _shapes _selectionMembers _selectionLength _reserved
-      cases alternatives with
-      | cons edge rest => simp only [List.length_cons] at length; omega
-      | nil =>
-          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
-          exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
-  | succ count ih =>
-      intro inventory caller memos metadata before seed bound ceiling scs uv handle
-        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending
-        alternatives length selected shapes selectionMembers selectionLength reserved
-      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
-      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
-      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
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
-          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_captured_resources
-            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
-            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
-            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
-            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
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
-              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
-                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
-                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending
-                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member)) shapes
-                selectionMembers selectionLength laterReserved
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
-                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
-                dsimp only
-                rw [tailAt]
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
-end ActualCapturedRowsResources
-
```

### checked2333 to failed2339Key

```diff
--- checked2333.lean
+++ failed2339Key.lean
@@ -2295,4 +2295,10 @@
-              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
-                simpa only [hook] using continued
-              rw [hookStep]
-              cases hookOutcome <;> rfl
+              change (match SourcePruningEnumerationSharedPreparedRecursive.continueWith
+                (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
+                  (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
+                    (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra)
+                    (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra) edgesOf)
+                  holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (finalFuel + hookFuel + extra) recursiveDepth)
+                graph templates stop order (finalFuel + hookFuel + extra) metadata uv fragment reached saved finished with
+                | .complete outputs actual returned => .complete [receipt] outputs actual returned
+                | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)) = outcome
+              rw [continued]
```

### failed2339Key to failed2339

```diff
--- failed2339Key.lean
+++ failed2339.lean
@@ -2126 +2126 @@
-    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
+    (holeKey : Typing → Nat → Key) (matches : Key → Symbol → Bool) (admits : Key → Node → Bool)
@@ -2132 +2132 @@
-    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
+    (recursive : EagerResumeComplete (bits := bits) holeKey matches admits graph templates checkEmpty edgesOf
@@ -2169 +2169 @@
-            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
+            holeKey matches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
@@ -2180 +2180 @@
-      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
+      holeKey matches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
@@ -2270 +2270 @@
-              callback_eager_induction_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
+              callback_eager_induction_resources holeKey matches admits formulas solver next graph templates metadata uv
@@ -2300 +2300 @@
-                  holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (finalFuel + hookFuel + extra) recursiveDepth)
+                  holeKey matches admits graph templates checkEmpty edgesOf stop order (finalFuel + hookFuel + extra) recursiveDepth)
```

### failed2339 to checked2121

```diff
--- failed2339.lean
+++ checked2121.lean
@@ -2121,218 +2120,0 @@
-section ActualCapturedResources
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_captured_resources
-    (holeKey : Typing → Nat → Key) (matches : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (recursiveDepth : Nat)
-    (recursive : EagerResumeComplete (bits := bits) holeKey matches admits graph templates checkEmpty edgesOf
-      stop order formulas solver recursiveDepth)
-    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
-    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
-    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (ready : EnumerationDriver.Ready uv before.core)
-    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
-    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
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
-      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
-        (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
-        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
-          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-            holeKey matches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-          graph templates stop order (fuel + extra) metadata uv)
-        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
-      OutcomeResources formulas solver caller
-        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
-          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
-  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
-  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
-  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
-    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
-      holeKey matches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
-    graph templates stop order work metadata uv
-  change ∃ fuel outcome,
-    (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
-      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-      (hook (fuel + extra)) (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
-    OutcomeResources formulas solver caller
-      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
-  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
-      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
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
-          rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
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
-          fun work fragments reached saved after =>
-            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
-            let middle := SelectedEdge.finish residual fragment after
-            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
-            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
-                (some (.complete fragment reached saved finished))
-            | none => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
-                (some (.finalizeStopped fragment reached saved middle))
-        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
-          fun work completed observation candidate =>
-            SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
-              (some (.stopped completed observation candidate))
-        have tupleConsumers : TupleConsumers formulas solver caller metadata middle inputs uv continuation admitted yes no := by
-          constructor
-          · intro fragments reached saved after history current retained fitted supported afterMass accepted
-            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
-            let childAfter := SelectedEdge.finish residual fragment after
-            have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
-              middleCore middleCounter middleProtects fragments reached saved after history
-            obtain ⟨next, final, finalFuel, finished, _post, querySame, finalAt, finishedPacket,
-              fragmentBound, _core, finalMass, _stored, _root⟩ :=
-              finalize_child_inputs_packet formulas solver caller reached metadata before childAfter uv handle scs
-                fragment saved ready stored incoming data
-            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
-              Nat.le_trans finalMass afterMass
-            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
-              callback_eager_induction_resources holeKey matches admits formulas solver next graph templates metadata uv
-                fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current retained
-                finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
-            rw [querySame] at hookAt
-            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
-            let outcome : Fold := match hookOutcome with
-              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
-              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
-            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
-            · intro extra
-              have finalizeAt := finalAt (hookFuel + extra)
-              rw [← Nat.add_assoc] at finalizeAt
-              have continued := hookAt (finalFuel + extra)
-              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
-              rw [same] at continued
-              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
-                (finalFuel + hookFuel + extra) uv fragment childAfter with
-                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
-                    (hook (finalFuel + hookFuel + extra)) caller memos.query
-                    (some (.complete fragment reached saved finished))
-                | none => SourcePruningEnumerationSharedReceiptContinuation.run
-                    (hook (finalFuel + hookFuel + extra)) caller memos.query
-                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
-              rw [finalizeAt]
-              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
-              change (match SourcePruningEnumerationSharedPreparedRecursive.continueWith
-                (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-                  (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
-                    (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra)
-                    (finalFuel + hookFuel + extra) (finalFuel + hookFuel + extra) edgesOf)
-                  holeKey matches admits graph templates checkEmpty edgesOf stop order (finalFuel + hookFuel + extra) recursiveDepth)
-                graph templates stop order (finalFuel + hookFuel + extra) metadata uv fragment reached saved finished with
-                | .complete outputs actual returned => .complete [receipt] outputs actual returned
-                | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)) = outcome
-              rw [continued]
-            · cases hookOutcome <;> exact resources
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
-        have child := eager_child_height_complete (Typing := Typing) (bits := bits)
-          checkEmpty edgesOf captured limit own height formulas solver
-        have tuple := eager_tuple_complete_of_child (Typing := Typing) (bits := bits)
-          checkEmpty edgesOf captured limit own height formulas solver child limit
-        obtain ⟨fuel, outcome, running, resources⟩ := tuple inventory caller memos metadata middle seed
-          (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
-          inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
-        refine ⟨fuel, outcome, ?_, resources⟩
-        intro extra
-        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing]
-        exact running extra
-  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
-    refine ⟨0, outcome, ?_, ?_⟩
-    · intro extra
-      rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
-      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
-        SourcePruningEnumerationCachedOwn.prepare, allowed]
-      rfl
-    · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
-      intro output member
-      cases member
-end ActualCapturedResources
-
```

### checked2121 to checked2053

```diff
--- checked2121.lean
+++ checked2053.lean
@@ -2053,68 +2052,0 @@
-section ActualFinalizeChildInputs
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem finalize_child_inputs_packet
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
-    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
-    (ready : EnumerationDriver.Ready uv before.core)
-    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
-    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
-    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle) :
-    ∃ (next : Inventory) (final : Memos) (fuel : Nat) (after : Cached),
-      Post formulas solver next original reached final ∧ final.query = saved ∧
-      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
-        (fuel + extra) uv fragment middle = some after) ∧
-      Packet formulas solver next reached final metadata after ∧
-      FragmentBound after.core.counter fragment ∧
-      after.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
-      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤
-        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
-      after.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot after.core.representatives uv
-    := by
-  obtain ⟨next, final, post, querySame, middlePacket, _growth, _origin,
-    protects, references, fragmentBound, fragmentPending, fragmentAvoid⟩ := data
-  have avoids := ready.avoids handle scs stored
-  have frame := protects uv ready.inside ready.root avoids
-  have middleStored : middle.core.values[uv]? = some (.unenumerated (some handle) scs) :=
-    frame.value.trans stored
-  have separate := fragmentAvoid uv ready.inside ready.root avoids
-  have incomingAtMiddle : EnumerationReferences.IncomingAvoid uv middle.core := by
-    have allowed := references
-      (fun slot => ¬UnionFind.SameClass before.core.representatives uv slot)
-      incoming avoids (EnumerationReferences.fresh_separate before.core ready.safe uv ready.inside)
-    intro value member sc listed related
-    exact allowed value member sc listed ((frame.classes sc.var).mp related)
-  obtain ⟨roots, paths, storage, realized, counts, flags⟩ := middlePacket.valid
-  obtain ⟨fuel, after, finishRun, _raw, core, afterStored, _afterFlag, _afterWaiting,
-    afterPaths, afterCounts, afterFlags, afterStorage, afterRealized, safeFinish⟩ :=
-    SourcePruningEnumerationFinalize.complete reached.checked.native.machine.heap middle uv fragment
-      (.unenumerated (some handle) scs) middleStored roots paths counts flags storage fragmentBound realized
-  have afterSafe := safeFinish middlePacket.safe frame.root
-  have afterPending : EnumerationReferences.PendingReferences after.core := by
-    have written := EnumerationReferences.setValue_pending uv fragment middle.core
-      {middle.core with values := middle.core.values.set uv (.enumerated fragment)}
-      middlePacket.pending incomingAtMiddle ((EnumerationDriver.modify_success _ _ _).mpr rfl)
-    rw [core]
-    exact written
-  have afterPacket : Packet formulas solver next reached final metadata after := by
-    refine ⟨middlePacket.context, afterSafe, afterPending,
-      ⟨roots, afterPaths, afterStorage, afterRealized, afterCounts, afterFlags⟩, ?_, ?_⟩
-    · obtain ⟨level, frontier, ordered⟩ := middlePacket.ordered
-      obtain ⟨nextLevel, writtenOrder⟩ := EnumerationOrder.write_stratified middle.core middlePacket.safe
-        level frontier uv ordered (some handle) scs middleStored fragment fragmentPending separate
-      refine ⟨nextLevel, frontier + 1, ?_⟩
-      rw [core]
-      exact EnumerationOrder.stratified_ancestry _ [] nextLevel (frontier + 1) writtenOrder
-    · rw [core]
-      exact middlePacket.bounded
-  have mass := (SourcePruningEnumerationFinalize.run_scalars reached.checked.native.machine.heap
-    (fuel + 0) uv fragment middle after (finishRun 0)).2
-  refine ⟨next, final, fuel, after, post, querySame, finishRun, afterPacket, ?_, core, mass, afterStored, ?_⟩
-  · rw [core]
-    exact fragmentBound
-  · rw [core]
-    exact frame.root
-
-end ActualFinalizeChildInputs
-
```

```json
[
  {
    "from": "checked2487",
    "to": "checked2333",
    "from_sha256": "e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e",
    "to_sha256": "ba3bb2d3ef2ea93db6e3cb4bd91ad405f7c61936fe0cb8a5f3dcc57fa67ede74",
    "patch_sha256": "cad6191497ba7136aa2c51e4a821026db2045670a11b282ec991fbc472b7aac3",
    "replayed_exact": true
  },
  {
    "from": "checked2333",
    "to": "failed2339Key",
    "from_sha256": "ba3bb2d3ef2ea93db6e3cb4bd91ad405f7c61936fe0cb8a5f3dcc57fa67ede74",
    "to_sha256": "ba55fc2d55454b9171079a792ce7642a08eac7d9b2d2833cb0790cffebf98652",
    "patch_sha256": "3d7d00bdd12880b91f32c9acf762166e5c77d77dbed957593f2b73bf1299fa96",
    "replayed_exact": true
  },
  {
    "from": "failed2339Key",
    "to": "failed2339",
    "from_sha256": "ba55fc2d55454b9171079a792ce7642a08eac7d9b2d2833cb0790cffebf98652",
    "to_sha256": "f11dfbcb1923491469f96169db77973d74d62413bae0783076bddc605f8e20ea",
    "patch_sha256": "fea24b75787d6523be06dae7866f864e999c2ad535e5ceb0063379b3e9918145",
    "replayed_exact": true
  },
  {
    "from": "failed2339",
    "to": "checked2121",
    "from_sha256": "f11dfbcb1923491469f96169db77973d74d62413bae0783076bddc605f8e20ea",
    "to_sha256": "56fe353ada3be3aa0d8339e66e3730ac061815bebb5c12201c1c0c2bccd327d8",
    "patch_sha256": "f9d5881df61048993c809fc54992e5f3a9fdc8d0737e98e1a6caf42e0ceff10e",
    "replayed_exact": true
  },
  {
    "from": "checked2121",
    "to": "checked2053",
    "from_sha256": "56fe353ada3be3aa0d8339e66e3730ac061815bebb5c12201c1c0c2bccd327d8",
    "to_sha256": "c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165",
    "patch_sha256": "e99f040a72ec891ddcf5e3f0eda4a2578f73ab89a47a210f12ee870c2bcfe20a",
    "replayed_exact": true
  }
]
```

## Checked private tuple count source

Zero public laws. Copy this exact source to reproduce the strict kernel check.
SHA256 `6f7856c3266cc04f92dd63c52440634df15509fec6df49a694600af47e886495`.

```lean
import MicroCFTA.SourcePruningEnumerationSharedChildVisitors

/-!
# Success callback congruence at the actual ordered tuple length

The proof uses the existing visitChildren definition.
The visitor and failure callback stay unchanged.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedChildVisitors
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Fold" => Result Output Reason width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold

private theorem visitChildren_done_congr_length
    (visit : Visitor)
    (doneA doneB : List Fragment → Caller width → Queries → Cached → Fold)
    (stopped : List Fragment → Observation width → Option Cached → Fold)
    (inputs : List (Node × List Suspended))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (same : ∀ fragments reached saved after, fragments.length = inputs.length →
      doneA fragments reached saved after = doneB fragments reached saved after) :
    visitChildren visit doneA stopped inputs caller before queries =
      visitChildren visit doneB stopped inputs caller before queries := by
  induction inputs generalizing caller before queries doneA doneB stopped with
  | nil => exact same [] caller queries before rfl
  | cons input rest ih =>
      rcases input with ⟨value, bucket⟩
      simp only [visitChildren]
      apply congrArg (fun yes : Fragment → Caller width → Queries → Cached → Fold =>
        visit bucket value caller before queries yes
          (fun observation candidate => stopped [] observation candidate))
      funext fragment reached saved after
      apply ih
      intro fragments current retained final count
      exact same (fragment :: fragments) current retained final (congrArg Nat.succ count)

end MicroCFTA.SourcePruningEnumerationSharedChildVisitors
```

## Frozen artifact: eager-finalize-child-inputs-note.md

SHA256 `f1c1c778fec09f3c117c0643399cedd52fa3776bee430d703b05946f056d99b9`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
# Eager child finalization observer

Status: uncompiled private draft. Root is the sole compiler.
Date: 2026-11-13 02:22 CET.

## Frozen inputs

- Checked owner basis: eager-cps-height-resources-2053-boolean.lean.
  SHA c5f579fdc9099ebfb25e20ae06ccf1193d7ec6610717285a2fd3bbcc0308a165.
- Exact private finalize_child_inputs_packet header: 18 lines.
  SHA 0950ed081184de378e8a3424d57aabc174577b9ab85fcdf8e3a8fc3bed7c9e2a.
- New append fragment: eager-finalize-child-inputs-fragment.lean.txt, 67 lines.
  SHA 5bbd12c362f802062ae4eece132ba39a1984305295fb29260de758335acb94d9.

The fragment enters the existing SharedEagerReservation namespace and aliases.
It adds one private theorem. It adds no public law or operation.
The 18-line header is unchanged, including its current-data premises and full conclusion.

## Proof

1. Extract next, full final Memos, Post, query identity and the middle Packet
   from the SAME checked ChildInputs.
2. Apply Ready.avoids to the original stored target. Apply ChildInputs.protected
   to retain its SAME handle, bucket and root at middle.
3. Instantiate the corrected ChildInputs reference effect with the predicate
   that excludes the original target class. EnumerationReferences.fresh_separate
   supplies its fresh-variable premise. Protected.classes transports IncomingAvoid
   to the middle representative state.
4. Call SourcePruningEnumerationFinalize.complete ONCE at that middle state.
   Retain its SAME actual after cache and all-larger-fuel successful run.
5. Derive pending references with EnumerationReferences.setValue_pending.
   Derive dependency order with EnumerationOrder.write_stratified and
   stratified_ancestry. Retain native Context, template bounds, cache indexes,
   storage, realization and safety in the SAME after Packet.
6. Apply Finalize.run_scalars from SourcePruningEnumerationEdgeScalarBounds
   to the actual finishRun 0 observation. It gives mass(after) <= mass(middle).
   The exact write also retains fragment bounds and the captured root.

Reference implementation: SourcePruningEnumerationCapturedPreparedResources.lean
complete_with_history_resources_prepared, lines 114-195. The new fragment uses
ChildInputs rather than the shallow selected-edge producer or its Trace.

## Boundary

This theorem performs finalization only after a successful child computation.
It does not construct the child result or replay any native producer.
It does not add a parent slot, a shallow traversal Trace, a callback or recordTypes.
It retains the extracted original-to-reached Post and full Memos without a
second chosen endpoint. It supplies no model, source acceptance or assignment.
It does not prove the outer eager CPS induction, fuel adequacy or termination.
No repository, Haskell, evidence, compiler or Git command was used.
```

## Frozen artifact: eager-cps-finalize-child-inputs-stage-note.md

SHA256 `833e635ed4b062029234c29769080f901afe27e96e1270ce66f7cb0a5ccc63cd`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
# Actual captured-target finalization from eager child data

Status at 2026-11-13 02:28 CET: ROOT strict compiler PASS first try.
Terminal1404, compiler0, memory.max/high4GiB and swap0.
ROOT is the sole compiler.
Source: `eager-cps-finalize-child-inputs-stage.lean`, 2121 lines.
SHA256: `56fe353ada3be3aa0d8339e66e3730ac061815bebb5c12201c1c0c2bccd327d8`.

The source appends Beta's67-line fragment/5bbd12c3 to the exact
checked2053-boolean/c5f579fd height source.
The exact18-line private header0950ed08 is unchanged.
The source changes no arithmetic definition, import or executable worker.
All prior source snapshots remain unchanged.

One actual Finalize.complete supplies the stable captured-target write.
The proof retains the same extracted full Memos, Post and query identity.
Current Ready and protected input data retain the pending target.
The corrected reference effect and fresh_separate derive the same
middle IncomingAvoid fact.
The actual write supplies the full afterPacket, bounded fragment,
nonincreasing mass, exact core equation and stored root.
There is no new after-state or semantic supplier.

Checked2053 proves the child-height induction without a child-resource provider.
Its private consumer certificate must still be discharged by outer recursion.
The public20-line runEager resource target remains unproved.
No new public eager resource law is claimed.
```

## Frozen artifact: eager-cps-captured-resources-stage-note.md

SHA256 `0945533c0bdfbabc104e1dfe82c33a8aa955cb531e90f098674fd203d474b726`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
# Actual eager captured receipt and lower-depth continuation

Status at 2026-11-13 02:35 CET: UNCOMPILED. ROOT is the sole compiler.
Frozen source: `eager-cps-captured-resources-2339-f11dfbcb.lean`.
Lines:2339. SHA256:`f11dfbcb1923491469f96169db77973d74d62413bae0783076bddc605f8e20ea`.
The exact50-line private header e9965efc is unchanged.
The source appends217 lines to the checked2121/56fe353a prefix.
It adds no import, worker or arithmetic definition.

The proof uses the actual visitCapturedWith_eq_receipts equation.
The same own-prefix receipt gives actual child inputs and strict rank.
The unconditional checked child-height theorem supplies each eager child.
The checked generic tuple proof retains all actual ordered alternatives.
Successful tuple data supplies the same selected fragment and packet.
One checked finalizer writes the captured target.
One actual continueWith uses the PRIVATE lower-depth resume IH.
Both actions use a common sufficient fuel at the same native endpoint.
The complete result keeps the finalized captured receipt.
The stopped result keeps the exact continuation receipt, reason and endpoint.
No extra unfinalized parent receipt is inserted by consumeSelected.
The rejected and unsupported branches retain their literal old result.
Normal empty raw results retain the actual receipt and continue.
There is no packet or mass claim for a rejected candidate.

The PRIVATE outer-depth IH remains open until the actual preparation,
ordered captured-row scan and selected-prefix/depth proof discharge it.
The public20-line eager resource target remains undeclared and unproved.
There is no new public eager resource law or general model claim.

ROOT strict PASS at 2026-11-13 02:43 CET: corrected2333-hook SHAba3bb2d3.
The lexical matches binder was renamed to keyMatches.
The hook conversion uses a typed local hookStep equation.
The checked50-line header has SHA7feb588a.
The original2339 draft remains unchanged and failed these local issues.
```

## Frozen artifact: eager-cps-captured-rows-stage-note.md

SHA256 `877a50222d6ee9661810d79393c15bcf44e4044ab95aa44343f90e9b4a09afa2`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
# Ordered actual captured rows with eager children

Status at 2026-11-13 02:44 CET: ROOT strict compiler PASS first try at 2026-11-13 02:48 CET.
Terminal38724, compiler0, max/high4GiB and swap0. ROOT is the sole compiler.
Frozen source: `eager-cps-captured-rows-2487-e1f26f5a.lean`.
SHA256:`e1f26f5a64b7d91af08065a837509e56d9d274c6eef849b10cc296631248055e`. Lines:2487.
The exact52-line private header1cce9e88 is unchanged.
The153-line fragment appends to checked2333-hook/ba3bb2d3.
All old snapshots remain unchanged.

The count induction calls the actual captured-row resource theorem once
at each reached head. That theorem uses the proved child-height induction.
The only remaining recursive certificate is PRIVATE lower-depth resume.
A completed head supplies the same full Post, Memos and Queries.
The actual endpoint supplies the next row's native heap.
The next sibling uses the same captured Core and metadata.
The same Post retains current captured-node availability.
The result appends complete processed receipts and ordered outputs.
A stopped head retains its exact prefix and skips the suffix.
Within-plan growth pads unused rows. No cross-seed monotonicity is used.

The source adds no public declaration, operational worker or plan definition.
The public20-line general eager resource target remains unproved.
Common preparation and selected-prefix/outer-depth closure remain open.
```

## Frozen artifact: private-eager-captured-resources-header.txt

SHA256 `e9965efc036107c17a7be4a265e57f45395c68298e60f011c0e3a66bb9375f5c`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
private theorem eager_captured_resources
    (holeKey : Typing → Nat → Key) (matches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey matches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
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
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey matches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
```

## Frozen artifact: private-eager-captured-rows-header.txt

SHA256 `1cce9e885f2a4518b4261fd30eb6a529b9ec455b4ba04af382f7545d82d569c8`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
private theorem eager_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat) :
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat),
    Packet formulas solver inventory caller memos metadata before →
    EnumerationDriver.Ready uv before.core →
    before.core.values[uv]? = some (.unenumerated (some handle) scs) →
    EnumerationReferences.IncomingAvoid uv before.core →
    Fits seed.2 caller.checked → Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    SourceEqualityRequiredCache.Keeps captured caller.checked.native.machine.heap →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling → scs.length ≤ bound →
    ∀ (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
      (rows : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference),
    Available captured (.node parentEntry rows depth free) → free = [] →
    MergedOrdinaryHeight.height (.node parentEntry rows depth free) ≤ height + 1 →
    (∀ sc ∈ scs, sc.var < before.core.counter) → InputsPending before.core scs →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (∀ entry rows depth free, Available captured (.node entry rows depth free) →
      rows.length ≤ limit ∧ ∀ edge ∈ rows, edge.children.length ≤ limit ∧
        ∀ tries residual, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) →
          tries.length ≤ own) →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    (∀ index, index < count → tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained)
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed index)) →
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedBranching.scan
        (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
            (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          (SourcePruningEnumerationSharedPreparedRecursive.continueWith
            (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
            graph templates stop order (fuel + extra) metadata uv)
          (fuel + extra) uv scs) before alternatives caller memos.query = outcome) ∧
      OutcomeResources formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
```

## Frozen artifact: private-eager-captured-header-keyMatches.txt

SHA256 `7feb588a728efb1d24b4c61f4c50488f9119ebb9668dca86fd65f1eee27d4080`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
private theorem eager_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling : Nat) (scs : List Suspended) (uv handle : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
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
      limit (bound + own) ceiling (fun retained current => eagerFinal recursiveDepth current retained)
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
```

## Frozen artifact: visit-children-done-congr-note.md

SHA256 `cdfb559f9a0823677839c4a9218ecfba43f3319ddc96f17b19a138320216044c`. The artifact describes its stated stage.
The reserved-name draft is retained; the checked private binder is keyMatches.
Later strict results and local repairs appear above.

```text
# Private count-restricted success callback congruence

Frozen unverified fragment, 2026-11-13 02:37 CET.
Source: VisitChildrenDoneCongr.lean, 51L.
SHA256: 6f7856c3266cc04f92dd63c52440634df15509fec6df49a694600af47e886495.
Private law: visitChildren_done_congr_length. There is no new public API.
Import: MicroCFTA.SourcePruningEnumerationSharedChildVisitors.
Namespace: MicroCFTA.SourcePruningEnumerationSharedChildVisitors.

Header: visit-children-done-congr-length-header.txt, 10L.
SHA256: 01a0f42ad8a9781c38bca1fb728505bb937425884ab1cb0a594b6662e121023f.
The header stayed unchanged when the proof was added.
The visitor, caller, cache, query, inputs and failure callback stay the same.
The successful callbacks need equality only when the fragment count equals the
input count, at identical reached caller/query/cache arguments on both sides.
The result equality retains the entire actual fold, including failure outcomes.

No existing public generic count law was found in the focal shared visitor,
reservation or scalar observer modules. visitChildren_shallow is policy-specific.
The private ScalarObservers.tuple_bounds requires child cache observers.
Reservation's private visitor congruence changes visitors rather than restricting
success equality by count. Those laws do not supply this assumption-free result.

The nil case applies the equality premise to the empty list and initial endpoint.
The cons case unfolds literal visitChildren. congrArg and funext reduce equality
to the two actual head-success functions. The tail IH preserves the same stopped
callback with its completed-prefix argument. congrArg Nat.succ supplies the
original count equality after the SAME head fragment is added.
No condition on the visitor or its behavior is required. There is no resource,
model, worker, type assignment, Native effect, consumer-supplier or replay premise.

This permits an internal success callback to branch on exact tuple length and
carry that proof to the existing parent-fragment constructor. Equality ignores
its unreachable wrong-length arm. It does not infer shallow Trace or successful
callback invocation from a bare equality of result values. It proves no output
existence, eager role invariant, model existence, adequate depth or termination.

The imported repository visitor module was read at 223L, SHA256:
fd0ae3de1e211fe36d06a4bfd1908145a4990dc6ae92a6be89c772e759e35339.
No repository, old source, documentation, evidence, Haskell or Git changes were
made. No compiler was run. Root owns strict checking and any later integration.
```

## Reproduce

Current2487 is regular Lean source. Its own and compatibility portable packets
check all inherited public laws, exact snapshots and standard axioms. Reverse
patches reconstruct all failed drafts. Check the private51 source under the
same serial4GiB cap and project Nix shell. No execution archive is required.
