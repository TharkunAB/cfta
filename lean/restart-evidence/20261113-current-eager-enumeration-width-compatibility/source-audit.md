# Current-input eager width and actual eager output control

Base: c84541a27e09acea198e51a50157d6bc003bd07e. Main: e53852064d3ef5a2eafec47d754c27504b11de5f.
All three own-source checks pass with explicit public #check and axiom reports.
Only propext, Classical.choice and Quot.sound occur in those reports.
Three modules contain 758 lines and eight public laws. Four laws are new.
The old four child-visitor laws, their proofs and all execution definitions remain unchanged.

The public captured equation exposes the exact actual Finalize.run and receipt continuation.
The client proof had failed to convert the imported private helper even with local all-transparency.
The new equation is proved in the defining module. Three unused instance binders are omitted.
The final eager control proof uses the public equation and existing receipt observer.
Its exact original public header remains unchanged across all five source versions.

Actual runEager output control covers all work/depth fuels and emitted stopped prefixes.
metadata=None implies the default no-stop chooser returns done. stop=None implies metadata=None.
There is no public Packet, Room, Fits, availability, height, model or consumer premise.
The private strong-height proof handles the actual decreasing eager branch and nondecreasing shallow fallback.
This result proves no output existence, resource bound, Program role or Type assignment.

The mathematical eager width uses only original lib/query/signed-size/chosen-depth and the SAME
current source/build equations. It applies roomBits to the ORIGINAL eagerFinal profile, then
derives eagerReserved for every numeric stage. It supplies no initializer or future caller.
It does not reuse the shallow enumBits and does not establish actual execution or fixed host-word capacity.

The existing current-input Program-output theorem remains the cold SHALLOW one-initializer/one-worker result.
Resource/role completion for eager execution, shared backward source history, finite Type solvability,
adequate depth, total work, stream order/multiplicity, both inverses and Haskell correspondence remain open.
No Haskell source changed. The external Liquid LAST repeated-name/refinement issue remains recorded in FINDINGS.

## Exact public declarations

### SourceSynthesisCurrentProgramEagerEnumerationWidth

Source SHA256 `42ee9e2bbc149ed4eabbc3c18f427131c9b05dc5600d6c97a8ba96273003c953`. 64 lines.

```lean
theorem enumProfile_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    enumProfile lib query signed depth =
      (SourcePruningEnumerationSharedEagerReservation.eagerFinal depth (seed heap) 0).2
```

```lean
theorem eager_reserved_of_build
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (depth : Nat) (value : Node) (heap : State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value heap) :
    SourcePruningEnumerationSharedEagerReservation.eagerReserved
      (enumBits lib query signed depth) depth (seed heap) 0
```

### SourcePruningEnumerationSharedChildVisitors

Source SHA256 `fd0ae3de1e211fe36d06a4bfd1908145a4990dc6ae92a6be89c772e759e35339`. 223 lines.

```lean
theorem visitChildren_shallow
    (checkEmpty : Bool) (r n p h k : Nat)
    (done : List Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : List Fragment → Observation width → Option Cached → Result Output Reason width)
    (inputs : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries) :
    visitChildren (shallowVisit checkEmpty r n p h k) done stopped inputs caller before queries =
      match ChildTraversal.run checkEmpty r n p h k inputs caller before queries with
      | .complete fragments reached saved after => done fragments reached saved after
      | .stopped completed observation candidate => stopped completed observation candidate
```

```lean
theorem visitSelected_shallow
    (checkEmpty : Bool) (r n p h k : Nat)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries) :
    visitSelected (shallowVisit checkEmpty r n p h k) consume scs edge caller before queries =
      consume (SelectedEdge.run checkEmpty r n p h k scs edge caller before queries)
```

```lean
theorem visitCapturedWith_shallow
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : Edge) (caller : Caller width) (queries : Queries) (before : Cached) :
    visitCapturedWith (shallowVisit checkEmpty r n p h k) hook k target scs edge caller queries before =
      visitCaptured hook checkEmpty r n p h k target scs edge caller queries before
```

```lean
theorem run_eq_scan_shallow
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List Edge) (caller : Caller width) (queries : Queries) :
    NativeContinuations.run hook checkEmpty r n p h k target scs before edges caller queries =
      scan (visitCapturedWith (shallowVisit checkEmpty r n p h k) hook k target scs)
        before edges caller queries
```

```lean
theorem visitCapturedWith_eq_receipts
    (visit : Visitor)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    visitCapturedWith visit hook k target scs edge caller queries before =
      visitSelected visit (fun receipt =>
        match receipt with
        | .complete fragment reached saved after =>
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
                (some (.finalizeStopped fragment reached saved after))
        | other => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some other))
        scs edge caller before queries
```

### SourceSynthesisSharedEagerOutputControl

Source SHA256 `7fa435fcdb3f742f5f4d3eb5e18599e249e609bcab7893ad1e53a7ab46bea3a9`. 471 lines.

```lean
theorem runEager_output_control
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) (output : Output width Typing)
    (member : output ∈ emitted (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before)) :
    (output.metadata = none → EnumerationPureSelection.next (fun _ => none) output.cache = .done) ∧
      (stop = none → output.metadata = none)
```

## Public proof source history

The final source is registered. Apply these reverse patches in order to retain every failed draft.
Each patch was replayed with GNU patch --output and matched its exact target SHA256.
Control450,479,481,482 failed strict compilation. Control471 passes via the public equation.
Captured222 built but failed the strict unused-instance check. Captured223 passes.

### control471 to control482

```diff
--- control471.lean
+++ control482.lean
@@ -211 +211 @@
-  rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
+  unfold SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
@@ -214,0 +215 @@
+  | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ => intro output member; cases member
@@ -218,4 +219 @@
-    | none =>
-      dsimp only
-      exact control_receipt stop hook hookControlled caller queries
-        (some (.finalizeStopped fragment reached saved after))
+    | none => intro output member; cases member
@@ -224,4 +222,17 @@
-      exact control_receipt stop hook hookControlled caller queries
-        (some (.complete fragment reached saved finished))
-  | unhandled | rejected _ _ _ | finalizeStopped _ _ _ _ | stopped _ _ _ =>
-    exact control_receipt stop hook hookControlled caller queries _
+      with_unfolding_all
+        change FoldControlled stop (match hook fragment reached saved finished with
+          | .stopped outputs reason endpoint => .stopped [] outputs
+            (.continuation (.complete fragment reached saved finished) reason endpoint)
+          | .complete outputs actual current => .complete [.complete fragment reached saved finished] outputs actual current)
+      cases called : hook fragment reached saved finished <;> intro output member
+      all_goals exact hookControlled fragment reached saved finished output (by
+        simpa only [called, controlFoldEmitted, emitted] using member)
+  | stopped fragments observation candidate =>
+    change FoldControlled stop (match advance (.stopped fragments observation candidate) with
+      | none => .stopped [] [] (.edge (some (.stopped fragments observation candidate))
+          (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.endpoint
+            (.stopped fragments observation candidate) caller queries))
+      | some (reached, saved) => .complete [.stopped fragments observation candidate] [] reached saved)
+    cases advanced : advance (.stopped fragments observation candidate) with
+    | none => intro output member; cases member
+    | some endpoint => obtain ⟨reached, saved⟩ := endpoint; intro output member; cases member
```

### control482 to control481

```diff
--- control482.lean
+++ control481.lean
@@ -222,5 +222,4 @@
-      with_unfolding_all
-        change FoldControlled stop (match hook fragment reached saved finished with
-          | .stopped outputs reason endpoint => .stopped [] outputs
-            (.continuation (.complete fragment reached saved finished) reason endpoint)
-          | .complete outputs actual current => .complete [.complete fragment reached saved finished] outputs actual current)
+      change FoldControlled stop (match hook fragment reached saved finished with
+        | .stopped outputs reason endpoint => .stopped [] outputs
+          (.continuation (.complete fragment reached saved finished) reason endpoint)
+        | .complete outputs actual current => .complete [.complete fragment reached saved finished] outputs actual current)
```

### control481 to control479

```diff
--- control481.lean
+++ control479.lean
@@ -221 +220,0 @@
-      dsimp only
@@ -342 +340,0 @@
-        dsimp only
```

### control479 to control450

```diff
--- control479.lean
+++ control450.lean
@@ -217 +216,0 @@
-    dsimp only
@@ -280 +279 @@
-    ChildControlled (width := width) stop (SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k) := by
+    ChildControlled stop (SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k) := by
@@ -282,32 +281,4 @@
-  cases dispatched : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run
-      checkEmpty r n p h k scs incoming caller before queries with
-  | mk observation candidate =>
-    have rejected := no observation candidate
-    rcases observation with ⟨outcome, reached, saved, _outer, _waiting⟩
-    cases outcome with
-    | error _fault =>
-      simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-    | ok returned =>
-      cases returned with
-      | none =>
-        simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-      | some raw =>
-        cases raw with
-        | nil =>
-          simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-        | cons row rows =>
-          cases row with
-          | error _fault =>
-            simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-          | ok child =>
-            rcases child with ⟨fragment, _returnedCore⟩
-            cases rows with
-            | cons _row _rows =>
-              simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-            | nil =>
-              cases candidate with
-              | none =>
-                simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using rejected
-              | some after =>
-                simpa only [SourcePruningEnumerationSharedChildVisitors.shallowVisit, dispatched] using
-                  yes fragment reached saved after
+  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
+  split
+  · exact yes _ _ _ _
+  · exact no _ _
@@ -326,2 +297,2 @@
-  induction height using Nat.strongRecOn with
-  | ind height ih =>
+  induction height using Nat.strong_induction_on with
+  | h height ih =>
@@ -333 +304 @@
-      have children : ChildControlled (width := width) stop
+      have children : ChildControlled stop
@@ -335 +306 @@
-            if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
+            if lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
@@ -353 +324 @@
-    ChildControlled (width := width) stop (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf) := by
+    ChildControlled stop (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf) := by
```

### captured223 to captured222

```diff
--- captured223.lean
+++ captured222.lean
@@ -194 +193,0 @@
-omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
```

### captured222 to captured193

```diff
--- captured222.lean
+++ captured193.lean
@@ -1 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation
@@ -194,28 +192,0 @@
-/-- Expose captured finalization through the public receipt continuation. -/
-theorem visitCapturedWith_eq_receipts
-    (visit : Visitor)
-    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
-    (k target : Nat) (scs : List Suspended) (edge : Edge)
-    (caller : Caller width) (queries : Queries) (before : Cached) :
-    visitCapturedWith visit hook k target scs edge caller queries before =
-      visitSelected visit (fun receipt =>
-        match receipt with
-        | .complete fragment reached saved after =>
-            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
-            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
-                (some (.complete fragment reached saved finished))
-            | none => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
-                (some (.finalizeStopped fragment reached saved after))
-        | other => SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some other))
-        scs edge caller before queries := by
-  have same (receipt : Receipt width) :
-      finishReceipt hook caller queries receipt =
-        SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some receipt) := by
-    cases receipt with
-    | complete fragment reached saved after =>
-        cases called : hook fragment reached saved after <;>
-          simp only [finishReceipt, SourcePruningEnumerationSharedReceiptContinuation.run, called]
-    | unhandled | rejected _ _ _ | stopped _ _ _ | finalizeStopped _ _ _ _ => rfl
-  unfold visitCapturedWith
-  simp only [same]
-
```

```json
[
  {
    "from": "control471",
    "to": "control482",
    "from_sha256": "7fa435fcdb3f742f5f4d3eb5e18599e249e609bcab7893ad1e53a7ab46bea3a9",
    "to_sha256": "c44f4404e0c58e6316298f8228a8042bcc377d27eff45fc58ea4890aaf821ef1",
    "patch_sha256": "a0d0f9fb51ec589ad6310c0f5bab81fa27a69cc3207fa15348d2abb3fb12d990",
    "replayed_exact": true
  },
  {
    "from": "control482",
    "to": "control481",
    "from_sha256": "c44f4404e0c58e6316298f8228a8042bcc377d27eff45fc58ea4890aaf821ef1",
    "to_sha256": "10c58d72858b224e4c3a5106cb4c1c7648399a1c60e227dc55e7741cb92dbeb9",
    "patch_sha256": "4d40b168b47f91d92ecc0178f9fbe9f8e9796e0b4827ebd21324e30318f1df3b",
    "replayed_exact": true
  },
  {
    "from": "control481",
    "to": "control479",
    "from_sha256": "10c58d72858b224e4c3a5106cb4c1c7648399a1c60e227dc55e7741cb92dbeb9",
    "to_sha256": "3bd83190a1f93c2e970fb0aa0a0026a07d7619a1ee664e971ad57049cd16cebc",
    "patch_sha256": "a50d5a1c95867f9d833e7c433b2b71a9121365c2530a1b46732078f7c7c98671",
    "replayed_exact": true
  },
  {
    "from": "control479",
    "to": "control450",
    "from_sha256": "3bd83190a1f93c2e970fb0aa0a0026a07d7619a1ee664e971ad57049cd16cebc",
    "to_sha256": "2d5bddfe455e4e423115fc8df265d3252fbcdedb496451169a0d26dd326fbde7",
    "patch_sha256": "774193815fa28517c494d0a2441ef05c6b8e31ddd3d0a8e42da815ada2c132d0",
    "replayed_exact": true
  },
  {
    "from": "captured223",
    "to": "captured222",
    "from_sha256": "fd0ae3de1e211fe36d06a4bfd1908145a4990dc6ae92a6be89c772e759e35339",
    "to_sha256": "af464cb635c2f0f5cf35f32db327182ee7423d6034930f8b84004817433c600d",
    "patch_sha256": "113c78d4107898e8c43a82ac4ddc9d26e5169663242813e95766ccb6c0da3103",
    "replayed_exact": true
  },
  {
    "from": "captured222",
    "to": "captured193",
    "from_sha256": "af464cb635c2f0f5cf35f32db327182ee7423d6034930f8b84004817433c600d",
    "to_sha256": "0c785c6944b8c9e8c9486e3653e1fa1f4b2ae0c8c4f9dd5aa19a61b07e035edd",
    "patch_sha256": "cb75d0ba5bb73b6af5356e81ff25c9cdddda07309139e0b812419fbab1115dae",
    "replayed_exact": true
  }
]
```

## Preserved control note: eager-output-control-note.md

SHA256 `9c66b16de4d4f413d0e3fca5e8d46231397d817633b610f68f7346fa2689dd4f`. This is the verbatim artifact at its stated stage.

```text
# Actual eager output control: frozen initial draft

2026-11-13 00:25 CET. Runtime-only source. No compilation was run here.
Source: SourceSynthesisSharedEagerOutputControl.lean.
Lines: 450.
SHA256: 2d5bddfe455e4e423115fc8df265d3252fbcdedb496451169a0d26dd326fbde7.
ONE public law: RecursiveChildPolicy.runEager_output_control.
Frozen header SHA256 excluding final newline:
a5b63e4bb211113a72ea63876dd2116137976ca061900a24832aa60fe3fbcba2.
The declaration remains byte-identical to the frozen target.

The two imports are the actual RecursiveChildPolicy and PreparedLiveRoot.
The proof reuses source definitions and the checked shallow control proof
structure. Pure receipt/scan/restart facts remain private. No published
source or initializer/worker/resource producer was changed or replayed.

Private visitChildren induction handles exact remaining tuple consumers.
visitSelected forwards only its actual receipt consumer's outputs.
consumeSelected only prepends receipts. Captured finalization forwards
actual hook outputs or emits none. It compares emitted prefixes only;
it imposes no equality on an unrelated full outcome or native endpoint.

Strong induction on actual incoming height controls eagerChild. Its true
child-decrease branch applies the smaller-height IH. Its false branch
uses the actual shallow visitor. This handles arbitrary input values and
selectors without adding Availability, Packet, height or selector gates.
The actual done/stopped consumers are controlled by tuple induction.

Outer resumeWithChild depth induction keeps exact restart decision/cache
identity, including actual parked restarts and callback recordTypes.
The concrete public runEager installs the internally proved eagerChild
property. No abstract visitor or consumer property is public or assumed.

The public law retains every work/depth fuel, arbitrary stop/order and
actual membership in BOTH complete and stopped emitted prefixes.
metadata none implies next default done at THAT output cache; stop none
implies THAT output metadata none. No Room/Fits, current-state, model,
height/rank, output-existence or adequate-depth hypothesis is added.
It establishes control only; actual eager resource completion remains
the independent unproved operational target. Status: unverified draft.
```

## Preserved control note: eager-output-control-receipts-note.md

SHA256 `7ff7aa6963b7c7c2c23333ffa709e6d6c6210c0388f391251d6d5972cf17a724`. This is the verbatim artifact at its stated stage.

```text
# Actual eager output control: public receipt equation adaptation

2026-11-13 00:44 CET. Runtime-only proof adaptation. No compilation was run here.
Source: SourceSynthesisSharedEagerOutputControl.lean.
Lines: 471.
SHA256: 7fa435fcdb3f742f5f4d3eb5e18599e249e609bcab7893ad1e53a7ab46bea3a9.
Previous 482-line source: c44f4404e0c58e6316298f8228a8042bcc377d27eff45fc58ea4890aaf821ef1.
All earlier immutable snapshots and failures remain preserved.

ONE public law: RecursiveChildPolicy.runEager_output_control.
Frozen public header SHA256 excluding final newline:
a5b63e4bb211113a72ea63876dd2116137976ca061900a24832aa60fe3fbcba2.
The public header remains byte-identical.

Only the private control_captured proof body changed.
It uses Root's new SharedChildVisitors.visitCapturedWith_eq_receipts equation.
That equation is expected to expose the SAME literal visitSelected action,
actual Finalize.run cases, and PUBLIC ReceiptContinuation.run on each receipt.
The complete and finalizeStopped cases invoke existing control_receipt.
Every other receipt uses the same existing observer directly.
The source drops manual private finishReceipt conversion and local all.
No generated private name, operation change or new hypothesis is added.

The helper equation is Root-owned and pending its own strict verification.
The all-fuel/stopped-prefix control claim remains unchanged.
No output existence, adequate depth, Packet, Room/Fits or model is assumed.
Actual eager resource completion remains separate.
Status: adapted candidate, awaiting the public equation and strict check.
```

## Preserved control note: eager-output-control-repair1-note.md

SHA256 `bbc4d33fef62d9828c2d87e5216ecb84deb560577ef7f0c3e86eaec5c063b118`. This is the verbatim artifact at its stated stage.

```text
# Actual eager output control: first focused repair

2026-11-13 00:30 CET. Runtime source only. No compilation was run here.
Source: SourceSynthesisSharedEagerOutputControl.lean.
Lines: 479.
SHA256: 3bd83190a1f93c2e970fb0aa0a0026a07d7619a1ee664e971ad57049cd16cebc.
Original 450-line snapshot: 2d5bddfe455e4e423115fc8df265d3252fbcdedb496451169a0d26dd326fbde7.
The original source and normal strict failure remain preserved.

ONE public law: RecursiveChildPolicy.runEager_output_control.
Frozen public header SHA256 excluding final newline:
a5b63e4bb211113a72ea63876dd2116137976ca061900a24832aa60fe3fbcba2.
The public header remains byte-identical. No premise or operation changed.

The complete receipt case now reduces its literal outer match before the
actual Finalize.run observation. This exposes the same finalization call
for named case reduction. No private implementation constant is named.

Private shallow and eager child-control headers and the local recursive
visitor specify width explicitly. Unused observation binders use underscores.
The shallow proof decomposes the actual observation and cache candidate.
It then uses exactly the done or stopped consumer selected by shallowVisit.
The induction uses the pinned Nat.strongRecOn API and its ind case.
The unused dependent-if binder has an underscore name.

The private visitor and tuple properties remain internal proof predicates.
The public law uses only actual runEager membership and original inputs.
It covers all fuels and both complete and stopped emitted prefixes.
It adds no selector, Packet, Room/Fits, model, rank or capacity gate.
It asserts no output existence or adequate execution depth.
Actual eager resource completion remains an independent unproved target.
Status: repaired draft, awaiting normal strict verification by Root.
```

## Preserved control note: eager-output-control-repair2-note.md

SHA256 `e699598d9d9e74c83fd35d1bd595c769b989afb4e049dcacef6b8b8a5eabe708`. This is the verbatim artifact at its stated stage.

```text
# Actual eager output control: second focused repair

2026-11-13 00:35 CET. Runtime-only proof repair. No compilation was run here.
Source: SourceSynthesisSharedEagerOutputControl.lean.
Lines: 481.
SHA256: 10c58d72858b224e4c3a5106cb4c1c7648399a1c60e227dc55e7741cb92dbeb9.
Previous 479-line source: 3bd83190a1f93c2e970fb0aa0a0026a07d7619a1ee664e971ad57049cd16cebc.
The original 450-line and first 479-line snapshots remain preserved.

ONE public law: RecursiveChildPolicy.runEager_output_control.
Frozen header SHA256 excluding final newline:
a5b63e4bb211113a72ea63876dd2116137976ca061900a24832aa60fe3fbcba2.
The public header is byte-identical. All original inputs remain.

The last strict check reported two private proof errors.
This repair adds exactly two dsimp only steps.
The first reduces the concrete Option match after Finalize.run cases.
The second beta-reduces the applied child visitor before its height split.
No worker, definition, premise, linter or heartbeat setting changed.
The actual emitted-prefix proof and all-fuel scope remain unchanged.
There is no output-existence, model, Packet, Room/Fits or capacity claim.
Status: repaired draft, awaiting normal strict verification by Root.
```

## Preserved control note: eager-output-control-repair3-note.md

SHA256 `d89b528466ddb0f0efe78567b0fbbcfb9238338bbfba07654b0499a8f783600d`. This is the verbatim artifact at its stated stage.

```text
# Actual eager output control: private conversion repair

2026-11-13 00:39 CET. Runtime proof only. No compilation was run here.
Source: SourceSynthesisSharedEagerOutputControl.lean.
Lines: 482.
SHA256: c44f4404e0c58e6316298f8228a8042bcc377d27eff45fc58ea4890aaf821ef1.
Previous 481-line source: 10c58d72858b224e4c3a5106cb4c1c7648399a1c60e227dc55e7741cb92dbeb9.
Every previous immutable source and failure remains preserved.

ONE public law: RecursiveChildPolicy.runEager_output_control.
Frozen header SHA256 excluding final newline:
a5b63e4bb211113a72ea63876dd2116137976ca061900a24832aa60fe3fbcba2.
The exact public proposition, inputs and actual worker remain unchanged.

Only the last private change tactic is wrapped in with_unfolding_all.
Pinned Init/Tactics.lean:374-377 defines this local tactic.
Pinned Lean/Elab/Tactic/ElabTerm.lean:320-321 runs that tactic with
TransparencyMode.all. It changes no global attribute or option.
The requested explicit match is the literal finishReceipt complete body
at SourcePruningEnumerationSharedChildVisitors.lean:64-76.
The proof names no generated private declaration.

All other proof steps remain byte-identical to the previous source.
All-fuel and stopped-prefix control scope remains unchanged.
No future consumer, Packet, Room/Fits, model or output existence is assumed.
Actual eager resource completion remains separate.
Status: repaired draft, awaiting normal strict verification by Root.
```

## Independent source audit: eager-output-control-header-review.md

SHA256 `fd27fa079b4b49c328201c1f62a07244a84e3ca8ff1e7bbcd4e6685fc4ec33bb`. Verbatim preserved review follows.

```text
# Frozen eager output-control header and branch review

Read-only review of the 450-line frozen draft, before ROOT's strict result.
No source, compiler, repository, docs, evidence, Git or Haskell changes.
Frozen source SHA256:
2d5bddfe455e4e423115fc8df265d3252fbcdedb496451169a0d26dd326fbde7
Exact 11-line public header SHA256:
4a439070a5381b5f87e2d5b07d0fc8df08dabd4c74b239fa7fbff85a0e993103
Published shallow317 source SHA256:
e6cb60f9fdec07a8dce2d3ce3e88558e5602d21983388c3d63a234e3c641967c

Mechanical exact header comparison PASSED. The ONLY substitutions are:
- theorem run_output_control -> theorem runEager_output_control;
- run -> fully qualified SharedPreparedRecursiveChildPolicy.runEager.
Every argument, actual emitted-list membership premise and both conclusions
remain identical. There is no new public resource, height, availability,
consumer-control, future-state, satisfying-model or completion supplier.
The current section instances match the existing worker's equality instances.

Exact supported statement: at ANY workFuel and recursiveFuel, an ACTUAL emitted
output with metadata=None has next(noStop)=done. With stop=None, every ACTUAL
emitted output has metadata=None and therefore is finished. This is an observer
of literal runEager, not a resource or output producer.

Private proof coupling follows the actual operations:
- control_scan:103 observes first/suffix results. Suffix induction receives
  the actual reached Caller and saved queries. Both complete and stopped-prefix
  outputs are retained by the exact emitted-list append membership split.
- control_continue:128 observes the actual recordTypes callback. A false result
  passes its returned metadata/compressed cache and actual restart decision to
  the smaller-depth IH. True/failure callback branches emit no outputs.
- control_tuple:146 threads actual reached Caller/cache/queries from each child
  into the ordered tail. Done and stopped consumers preserve their actual prefixes.
- control_selected:169 and control_captured:203 cover actual selection rejection,
  child traversal, captured finalization failure/success and callback outputs.
  No invented callback or replacement finalization receipt is introduced.
- control_shallow:277 covers BOTH actual shallowVisit outcomes by the internally
  supplied done/stopped continuation proofs. It assumes no native success.
- control_eager_height:286 unfolds the actual eagerChild:134 definition. Its
  ordinary branch uses the real ordered scan and selected traversal. Each child
  takes EITHER the actual strict-height recursive branch OR the literal
  nondecreasing shallowVisit fallback (316). No hypothesis removes that fallback.
  The top ordinary/terminal/opaque/empty fallback also uses control_shallow (319).
  The private height parameter is instantiated to height incoming with rfl (326);
  no prepared-child height or availability theorem is a public input.
- control_prepared:329 observes actual runWithChild preparation. The entry target,
  prepared value/heap, ordinary eager scan and terminal/opaque receipt continuation
  are those of that SAME returned branch, including impossible/failure cases.
- control_prefix:245 derives parked decision/cache consistency from the SAME
  runPrefix observation using actual adapt_core and Restart.run. No decision
  consistency provider appears in the public header.
- control_resume:364 inducts on actual bounded outer recursion. Done emits the
  existing finished output. Explicit stop keeps metadata; noStop rules that branch
  out. Stuck/exhausted/failed paths emit none. Parked/prepared paths instantiate
  the private continuation IHs with actual returned decisions and endpoints.
- public:433 supplies actual eagerChild and its PROVED control_eager property to
  control_resume. ChildControlled/private consumer hypotheses are fully discharged.

No native producer, resource completion or second worker is invoked by this proof.
No output/model/resource existence, adequate depth, whole search termination,
Satisfies, finite Type solvability, source typing, Program roles/readback, capacity
bound, eager resource completion or Haskell/default correspondence is concluded.
No substantive header or branch-coupling concern was found. This review concerns
ONLY frozen450 source2d5bddfe and the unchanged public header4a439070. If ROOT
later repairs proofs only, the header/scope review still applies; the changed
proof bytes need ROOT's separate strict check. This review itself is not a build.
```

## Independent source audit: current-output-typing-next.md

SHA256 `38e031710f757cfd448366e8bf678310a6949bd3f5e2a73dc5ccaecfdcc43dee`. Verbatim preserved review follows.

```text
# From current actual Program outputs to original-input typing

Bounded read-only audit. ROOT reports CurrentProgramOutputs187 published c84541a2.
No source/proof/compiler/Git change and no runtime probe was performed.
The checked receipt is a real one-initializer/one-worker cold-cache result for
successful current front-end input, chosen depth and current configuration.
Width is mathematical; it does not establish fixed-machine or eager completion.

What the SAME output already supplies (CurrentProgramOutputs:50-144):
full native Post/Memos/Packet/Fits/Heap, extended ProgramSlots, metadata=None,
next(noStop)=done, and actual stable partialRoot. There is one Program p with
Projection(openProgram true partialRoot,p). EVERY actual Completes sigma partialRoot
full has Projection(full,p). The model field is ONLY Satisfies(output,sigma) ->
Completes sigma partialRoot (sigma 0), never an existential sigma.
ProgramRoleCompletions:31 and PartialProgramDecoder:99 preserve that SAME p;
completions cannot change Program names/layout, but their existence is not proved.

Exact missing facts in the current invariants:
- Packet (RecursivePacket:21-36) stores Context, Safe, pending references,
  CacheValid, finite dependency order and allocated template IDs. It contains
  no satisfying assignment, residual truth, ground Type witness or source history.
- ProgramSlots (ProgramEnumerationRoles:48) stores bounds, roots, IncomingAvoid
  and actual typed-position layout. FragmentRoles leaves Type subtrees unrestricted.
  It does not record ordinary Typed/Eligible or per-use source origins.
- done implies flags false. DefaultFinishedRendering:279-300 derives that remaining
  native pending values decode to recursive boundaries with EMPTY buckets. This
  permits graph-bearing Type holes; it does not erase their native restrictions.
- WHOLE Discharged (Rendering:23-25) requires EVERY pending slot in the whole array
  to have node=None AND bucket=[]. It includes unreachable slots, not only Type
  annotations or the root. done/roles do NOT establish it.
- Rendering.render_assignment:143-155 constructs sigma only from Safe/order,
  WHOLE Discharged, an actual concrete render and CHECKED rendered residuals.
  Finished-render/marker agreement does not check those residuals or produce SAT.
- SharedPreparedMarkerOutput.default_finished_render_partial_models:136 keeps
  term=openProgram true partialRoot and all concrete/tagged observations. Its
  completion/model observer is still conditional on an input satisfying sigma.

Why existing source typing cannot simply be applied:
CurrentRenderedTyping139, ResourceHistory.render_current_typed:63 requires actual
NONSHARED PreparedRecursive.ResourceHistory, canonical initial state, final
ArityOrigins Heap, WHOLE Discharged, actual render and checked residuals. It
restores the SAME initial native root before invoking CurrentRootTyping.
CurrentProgramOutputs uses SHARED PreparedRecursive.run/OutcomeResources and
retains no corresponding backward resource history. The native backend, Seed,
receipts and run constants differ. An endpoint equality is not a history cast.
No Shared ResourceHistory.sound with this full original-root conclusion was found.

ExactProgramLanguage205.accepted_exact:70 is pinned to its own completed nodeCall
result and NodeLaw. Its backward implication needs native meaning at THAT result;
its converse uses empty inherited payload and avoid=[]. It is not an acceptance
certificate for these enumeration outputs. Do not call another completed worker
or identify its independent result by Program name or matching native endpoints.
RootEligibility.root_eligible:45 needs actual current mapped-source acceptance;
once that is derived, it gives original-token Perm, Eligible, decoding and count.
RootTyping.firstOrderRaw_typed:29 gives Typed and exact goal annotation from the
same source acceptance. These soundness directions do not require avoid=[].
Projection.toProgram_eq then aligns their Program with the SAME partial-root p.

Concrete NEXT semantic cut (not yet proved; preserve the entire187 receipt):
  accepted_source_sound (EXACT current187 inputs) :
    SAME initializer/startup/worker/per-output receipt, additionally for each output,
      ArityOrigins.Heap output.caller.heap ->
      Rendering.Discharged output.cache.core ->
      forall ambient sigma,
        Satisfies (handles holds ambient output.caller.heap) residual sigma output.cache.core ->
        Satisfies (handles holds ambient INITIAL.caller.heap) residual sigma startup.core
  where holds=PCSGuard.holds formulas solver and residual g t=(holds g t=true).
The output, initial caller, startup and stable run are those of ONE existing run;
no public history, source-membership, future assignment or producer supplier is added.
Current output model/arity/discharge are explicit conditional observer assumptions,
not derived existential facts. History must be derived INTERNALLY from the SAME
actual shared prefix/preparation/children/finalizer/callback/sibling execution.
The new field cannot be deduced from the existing187 resource predicate alone.
Use local actual shared semantic laws; SharedPreparedOpaqueLanguage:172 requires
actual preparation meaning and its explicit retained-bucket condition. Do not
silently drop a nonempty nonterminal opaque bucket or import the old history type.

With that observer, a separately checked discharged render constructs ONE sigma.
Its existing output-root completion field yields Projection(sigma0,p). The observer
restores native meaning at the INITIAL stored handle; SAME literal built plus
closed_language then yields source acceptance, Eligible/Typed/count for that p.
This is conditional discharged soundness. It still does not cover recursive Type
markers, arbitrary non-discharged outputs or prove their finite Type solvability.
Known marker-versus-ground examples remain that established boundary, not new
untypable-Program defects. FINDINGS:5942-5964 records the old f f/erase probes and
explicitly separates valid marker-containing Programs from ground nonemptiness.
No unconditional typing theorem or fresh counterexample is claimed here.

Exact unchanged source hashes used in this audit:
SourceSynthesisCurrentProgramOutputs:
b8985a4833b09135d069c361a7423d677311f504d6402fb104b3b36a5edbb197
SourceSynthesisCurrentRenderedTyping:
fabc6f02aa14b7224a739379029732bcdbbeb3098c17fcf3399ae24b0e9013ed
SourceSynthesisCurrentComputedWidthExactProgramLanguage:
9b8aeaa728e2e2917e41052c73a0c0fe7971897c4f8f798d990512c27259f5a0
```

## Independent source audit: current-source-final-note.md

SHA256 `33b982c73027a213dc3e8de74efdeae93afc8c5f43d8ed34bcd6894f0cdb5b3b`. Verbatim preserved review follows.

```text
# Current source Program output checkpoint

ROOT reports CurrentProgramOutputs187 passed strict compiler, public axiom,
full Audit and every portable check. Publication c84541a2 is remote-verified.
The exact 96-line header and b8985a48 source remain unchanged.
One successful current front-end input chooses a mathematical width for its
explicit recursive depth. One cold empty-cache initializer and one no-stop
SHALLOW shared prepared worker retain their complete SAME-endpoint receipts.
Current metadata has pending=[]; current driver configuration remains explicit.
Every emitted output has metadata=None, finished selection, Program roles and
one partial root with a common Program projection across all completions.
No output/model/completion existence, adequate depth, fixed-machine capacity,
eager completeness/termination or Haskell correspondence is asserted.
```

# Private eager CPS proof stages

The public eager resource target remains unproved. These stages add zero new public laws.
The three inherited arithmetic laws remain. Nix and Lean checked every declaration in each passed stage.
Each check used one thread, memory.max=memory.high=4 GiB and swap=0.
The checked1057 stage retains the exact checked381 source after its leading operational imports.
It proves fallback resources and CPS equality, tuple composition, zero-depth resources,
the actual ordinary own-prefix, callback composition with a private lower-depth hypothesis,
and numeric padding for an empty actual tuple. Positive height/head/depth closure is open.

The final stage composes ONE actual full fallback receipt with PRIVATE certified consumers
at the computed fallbackPlan. It derives after-Packet, mass, padding, admission and common fuel.
The raw1057 repair targets one advance_add rewrite. Headers and plan definitions remain unchanged.

The earlier arbitrary-Next plan was stronger than the actual entry requires. The checked callback
uses the literal Restart.decision. The public runEager and continueWith entries use that decision.
The parked case still needs its actual Restart.run and decision_frame receipt in the positive-depth proof.

```json
[
  {
    "stage": "checked381",
    "lines": 381,
    "source_sha256": "988794e6954f4e8e7e7594237f4655ad3f48017dd0d2d11be6eb8066efc9c75b",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "checked568",
    "lines": 568,
    "source_sha256": "1c6a340128cfc85270ab7890b67ca723cfa7cfcb3d5d5e836adfa2ec805fcd32",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "failed692",
    "lines": 692,
    "source_sha256": "345fe8854299ea7a995b66c367dc4f3849d41b3f261f7e1137ce725811d65809",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "checked693",
    "lines": 693,
    "source_sha256": "aad066b7065f5a85c22e04d541ed41da4e042e80e8f2e5e557f9e09e853d32be",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "failed805",
    "lines": 805,
    "source_sha256": "bb7481e09c30f739ff0b629058fa6070e82f7c22b75f5947f838f2117274199e",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "checked805",
    "lines": 805,
    "source_sha256": "4e87f60fa99e1d43cf28210cce7148d256836999f7976a65d9bd5ee2baa239ba",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "checked908",
    "lines": 908,
    "source_sha256": "ebe1a70bcc8b511d2ae658985071101afeb9ea34d6cb4660fc6cc8e0a0c4822b",
    "compiler_exit": 0,
    "new_public_laws": 0
  },
  {
    "stage": "failed1057",
    "lines": 1057,
    "source_sha256": "59c7c78ddece14455cb6c4b85525265766c40ec096855febf4f6e934d70bc538",
    "compiler_exit": 1,
    "new_public_laws": 0
  },
  {
    "stage": "checked1057",
    "lines": 1057,
    "source_sha256": "a335c974561f4e7582dbc797d3b22877013187f9a213663f67716f6297a67277",
    "compiler_exit": 0,
    "new_public_laws": 0
  }
]
```

Start from the exact registered source at c84541a27e09acea198e51a50157d6bc003bd07e:

```sh
git show c84541a27e09acea198e51a50157d6bc003bd07e:lean/MicroCFTA/SourcePruningEnumerationSharedEagerReservation.lean > checked381.lean
```

Apply the forward patch to reconstruct checked1057. Apply the reverse patches in order
to reconstruct every intermediate source, including failed drafts. Each patch was replayed
with GNU patch --output. The result matched the target bytes and SHA256.

### checked381 to checked1057

```diff
--- checked381.lean
+++ checked1057.lean
@@ -0,0 +1,7 @@
+import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
+import MicroCFTA.EnumerationStratifiedTransport
+import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds
+import MicroCFTA.SourcePruningEnumerationSharedPreparedZeroOutcomeResources
+import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
+import MicroCFTA.SourcePruningEnumerationSharedChildResources
+import MicroCFTA.SourcePruningEnumerationSharedPreparedOutcomeResources
@@ -381,0 +389,669 @@
+
+namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
+open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
+open InternedConstructorTemplates InternedProbeProvenance
+open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
+open SourceCurrentAllocatedNativeInventoryState (Inventory)
+open SourceCurrentAllocatedPartialInvariant (Post)
+open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
+open SourcePruningEnumerationSharedIncomingReservation (Seed advance)
+open SourcePruningEnumerationRecursive (Packet)
+open SourcePruningEnumerationSharedPreparedRecursive (OutcomeResources Output Failure finish)
+open SourcePruningEnumerationSharedSelectedContinuations
+local notation "Symbol" => SourcePruningTemplates.Symbol
+local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
+local notation "Node" => Value Symbol Constraint
+local notation "Caller" => SourceCurrentAllocatedPartialState.State
+local notation "Memos" => EndpointMemoGateTrace.Memos
+local notation "Queries" => SourceEndpointMemo.Memos
+local notation "Metadata" => SourcePruningRecordTypes.Metadata
+local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
+local notation "Fragment" => Fragments.Fragment Symbol
+local notation "Heap" => SourceEqualityAnnotationHeap.Heap
+local notation "Raw" => List (Except EnumerationState.Error (Fragment × EnumerationState.State Symbol Constraint))
+variable {Typing : Type} {bits : Nat}
+local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
+local notation "Visitor" => List Suspended → Node → Caller (bits + 2) → Cached → Queries →
+  (Fragment → Caller (bits + 2) → Queries → Cached → Fold) →
+  (ChildDispatch.Observation (bits + 2) → Option Cached → Fold) → Fold
+
+section ActualFallback
+variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
+
+private theorem fallback_complete_resources_cps
+    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
+    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
+    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
+    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (bucket : List Suspended) (incoming : Node)
+    (packet : Packet formulas solver inventory caller memos metadata before)
+    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
+    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
+    (fits : Fits seed.2 caller.checked)
+    (reserved : SourcePruningEnumerationSharedIncomingReservation.Reserved bits seed (bucket.length + 1))
+    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
+    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false) :
+    ∃ (r n p h k : Nat) (raw : Raw) (afterCaller : Caller (bits + 2)) (after : Cached)
+      (savedQueries : Queries) (final : Memos) (next : Inventory) (afterRoots : Nat → Nat)
+      (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
+      ((∀ extraRepresentative extraNative P H extraIndex, p ≤ P → h ≤ H →
+        SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty (r + extraRepresentative) (n + extraNative)
+          P H (k + extraIndex) bucket incoming caller before memos.query =
+          ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after)) ∧
+      Post formulas solver next caller afterCaller final ∧ final.query = savedQueries ∧
+      before.core.counter ≤ after.core.counter ∧ Roots after.core.representatives afterRoots ∧
+      StorageValid after.core ∧ PendingRealized afterCaller.checked.native.machine.heap after.core ∧
+      EnumerationCanonicalWaiting.Correct afterRoots after.core.values after.waiting ∧
+      (∀ slot, SourcePruningEnumerationNativeIndex.candidate afterCaller.checked.native.machine.heap
+        ((after.core.values[slot]?).getD .eliminated) = some (after.expandable slot)) ∧
+      EnumeratedOrigin before.core after.core ∧
+      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
+        Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
+      (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
+        EnumerationReferences.InputsAllowed allowed bucket →
+        EnumerationReferences.ReferencesAllowed allowed after.core) ∧
+      (EnumerationReferences.PendingReferences before.core → EnumerationReferences.PendingReferences after.core) ∧
+      (raw = [] ∨ ∃ fragment, raw = [.ok (fragment, after.core)] ∧
+        Safe after.core ∧ FragmentBound after.core.counter fragment ∧
+        PendingFragment after.core fragment ∧
+        ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
+          Avoids before.core.representatives held bucket →
+          FragmentAvoid after.core.representatives held fragment) ∧
+      Fits (advance seed (bucket.length + 1)).2 afterCaller.checked ∧
+      Heap (fun guard => guard ∈ (advance seed (bucket.length + 1)).1) afterCaller.checked.native.machine.heap) ∧
+      (∀ er en P H ek, p ≤ P → h ≤ H →
+        ∀ (done : Fragment → Caller (bits + 2) → Queries → Cached → Fold)
+          (stopped : ChildDispatch.Observation (bits + 2) → Option Cached → Fold),
+        SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (r + er) (n + en) P H (k + ek)
+          edgesOf bucket incoming caller before memos.query done stopped =
+          match raw with
+          | [.ok (fragment, _returned)] => done fragment afterCaller savedQueries after
+          | _ => stopped ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) := by
+  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
+  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained⟩ :=
+    ChildDispatch.complete_with_fragments_resources seed formulas solver inventory caller before checkEmpty bucket
+      incoming roots memos packet.context packet.safe paths counts flags realized bounded pending available closed
+      fits reserved known
+  refine ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots, outer, waiting, retained, ?_⟩
+  intro er en P H ek representative native done stopped
+  rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback checkEmpty (r + er) (n + en) P H (k + ek)
+    edgesOf bucket incoming caller before memos.query done stopped fallback]
+  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
+  rw [retained.1 er en P H ek representative native]
+  cases raw with
+  | nil => rfl
+  | cons first rest =>
+      cases first with
+      | error fault => rfl
+      | ok returned =>
+          rcases returned with ⟨fragment, core⟩
+          cases rest <;> rfl
+end ActualFallback
+
+section ActualTuple
+variable [DecidableEq (EdgeKey Symbol Constraint)]
+
+private theorem visitChildren_nil_resources
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
+    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
+    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
+    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
+    (actual : OutcomeResources formulas solver original seed (finish uv (done [] caller queries before))) :
+    OutcomeResources formulas solver original seed (finish uv
+      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped [] caller before queries)) := actual
+
+private theorem visitChildren_cons_resources
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (original : Caller (bits + 2)) (seed : Seed) (uv : Nat) (visit : Visitor)
+    (done : List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
+    (stopped : List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
+    (incoming : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
+    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
+    (good : Fragment → Caller (bits + 2) → Queries → Cached → Prop)
+    (bad : ChildDispatch.Observation (bits + 2) → Option Cached → Prop)
+    (head : ∀ yes no,
+      (∀ fragment reached saved after, good fragment reached saved after →
+        OutcomeResources formulas solver original seed (finish uv (yes fragment reached saved after))) →
+      (∀ observation candidate, bad observation candidate →
+        OutcomeResources formulas solver original seed (finish uv (no observation candidate))) →
+      OutcomeResources formulas solver original seed (finish uv
+        (visit bucket incoming caller before queries yes no)))
+    (tail : ∀ fragment reached saved after, good fragment reached saved after →
+      OutcomeResources formulas solver original seed (finish uv
+        (SourcePruningEnumerationSharedChildVisitors.visitChildren visit
+          (fun fragments => done (fragment :: fragments))
+          (fun completed => stopped (fragment :: completed)) rest reached after saved)))
+    (failed : ∀ observation candidate, bad observation candidate →
+      OutcomeResources formulas solver original seed (finish uv (stopped [] observation candidate))) :
+    OutcomeResources formulas solver original seed (finish uv
+      (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped
+        ((incoming, bucket) :: rest) caller before queries)) := by
+  exact head
+    (fun fragment reached saved after => SourcePruningEnumerationSharedChildVisitors.visitChildren visit
+      (fun fragments => done (fragment :: fragments))
+      (fun completed => stopped (fragment :: completed)) rest reached after saved)
+    (fun observation candidate => stopped [] observation candidate) tail failed
+end ActualTuple
+
+
+section ActualZero
+variable {Key : Type}
+variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
+
+private theorem resume_eager_zero_resources
+    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
+    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
+    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
+    (metadata : Metadata Typing) (decision : Option Next) (seed : Seed)
+    (packet : Packet formulas solver inventory caller memos metadata before)
+    (bounded : Fits seed.2 caller.checked)
+    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap) :
+    ∃ outcome,
+      (∀ workFuel, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
+        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
+        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
+        metadata caller memos.query before decision = outcome) ∧
+      OutcomeResources formulas solver caller seed outcome := by
+  obtain ⟨outcome, running, resources⟩ :=
+    SourcePruningEnumerationSharedPreparedRecursive.resume_zero_outcome_resources holeKey fits admits graph templates
+      checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata decision seed packet bounded known
+  refine ⟨outcome, ?_, resources⟩
+  intro workFuel
+  rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_zero]
+  cases decision with
+  | none => simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
+  | some selected =>
+      cases selected <;> simpa only [SourcePruningEnumerationSharedPreparedRecursive.resume] using running workFuel
+end ActualZero
+
+section ActualOrdinaryPrefix
+variable [DecidableEq (EdgeKey Symbol Constraint)]
+
+private theorem ordinary_prefix_packet
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing) (before : Cached)
+    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
+    (edges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
+    (edge : EdgeValue Symbol Constraint) (scs : List Suspended)
+    (packet : Packet formulas solver inventory caller memos metadata before)
+    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry edges depth free))
+    (parentClosed : free = []) (selected : edge ∈ edges)
+    (bounded : ∀ sc ∈ scs, sc.var < before.core.counter) (pending : InputsPending before.core scs)
+    (allowed : arityAllows edge.children.length scs = true)
+    (tries : List EqualityTrie.Trie) (residual : Option Constraint)
+    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual)) :
+    ∃ (roots : Nat → Nat) (action : EnumerateM Symbol Constraint
+        (Symbol × List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)) × Option Constraint))
+      (own : Cached),
+      Roots before.core.representatives roots ∧
+      (SourcePruningEnumerationEdgePrefix.prepare scs edge = some action ∧
+      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
+        some [((edge.entry.key.symbol,
+          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
+            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own)] ∧
+      ExceptT.run (action before.core) =
+        [.ok ((edge.entry.key.symbol,
+          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
+            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own.core)] ∧
+      own.core = suspendedState tries.length before.core ∧
+      own.core.counter = before.core.counter + tries.length ∧
+      own.core.representatives = before.core.representatives ∧
+      Safe own.core ∧ Roots own.core.representatives roots ∧ PendingRealized caller.checked.native.machine.heap own.core ∧
+      EnumerationCanonicalWaiting.Correct roots own.core.values own.waiting ∧
+      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
+        ((own.core.values[slot]?).getD .eliminated) = some (own.expandable slot)) ∧
+      InputsPending own.core (scs ++ suspendedVars before.core.counter tries) ∧
+      (∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
+        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
+        (∀ sc ∈ bucket, sc.var < own.core.counter) ∧ InputsPending own.core bucket) ∧
+      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
+        Avoids before.core.representatives held scs →
+        EnumerationDriver.Protected held before.core own.core ∧
+          ∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
+            Avoids own.core.representatives held bucket)) ∧
+      Packet formulas solver inventory caller memos metadata own ∧
+      SourcePruningEnumerationPrefixAdmission.suspendedBound own.core =
+        SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ∧
+      (∀ child bucket, (child, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
+        MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node parentEntry edges depth free)) ∧
+      ∀ (visit : Visitor) (consume : SelectedEdge.Result (bits + 2) → Fold),
+        SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before memos.query =
+          SourcePruningEnumerationSharedChildVisitors.visitChildren visit
+            (fun fragments reached saved after =>
+              let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
+              consume (.complete fragment reached saved (SelectedEdge.finish residual fragment after)))
+            (fun completed observation candidate => consume (.stopped completed observation candidate))
+            (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries) caller own memos.query := by
+  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := packet.valid
+  obtain ⟨action, own, retained⟩ := SourcePruningEnumerationEdgeInputs.complete
+    caller.checked.native.machine.heap parentEntry edges depth free edge scs roots
+    packet.context.ready.semantic.ready parentAvailable parentClosed selected before packet.safe realized
+    paths counts flags bounded pending allowed tries residual projected
+  refine ⟨roots, action, own, paths, retained, ?_⟩
+  obtain ⟨_prepared, ownRun, _raw, ownCore, ownCounter, _ownForest, ownSafe,
+    ownPaths, ownRealized, ownCounts, ownFlags, _combinedPending, _genuine, _ownProtects⟩ := retained
+  have origin : EnumeratedOrigin before.core own.core := by
+    rw [ownCore]
+    exact suspension_origin tries.length before.core
+  have protects (held : Nat) (inside : held < before.core.counter)
+      (root : IsRoot before.core.representatives held) :
+      EnumerationDriver.Protected held before.core own.core := by
+    rw [ownCore]
+    exact EnumerationDriver.suspension_protected held tries.length before.core packet.safe inside root
+  have protectsEnumerated (held : Nat) (fragment : Fragment)
+      (stored : before.core.values[held]? = some (.enumerated fragment)) :
+      EnumerationDriver.Protected held before.core own.core := by
+    obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held fragment stored
+    exact protects held inside root
+  have afterPending : EnumerationReferences.PendingReferences own.core := by
+    intro held fragment stored
+    have previous := origin held fragment stored
+    have incoming : EnumerationReferences.ReferencesAllowed
+        (fun uv => ¬UnionFind.SameClass before.core.representatives held uv) own.core := by
+      rw [ownCore]
+      exact EnumerationReferences.suspension_allowed _ tries.length before.core
+        (packet.pending held fragment previous)
+    intro value member sc listed related
+    exact incoming value member sc listed (((protectsEnumerated held fragment previous).classes sc.var).mp related)
+  have growth : before.core.counter ≤ own.core.counter := by rw [ownCounter]; omega
+  have ownPacket : Packet formulas solver inventory caller memos metadata own := by
+    refine ⟨packet.context, ownSafe, afterPending,
+      ⟨roots, ownPaths, ownSafe.1, ownRealized, ownCounts, ownFlags⟩, ?_, ?_⟩
+    · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
+      obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core own.core
+        ownSafe level frontier oldOrder origin protectsEnumerated
+      exact ⟨nextLevel, frontier, afterOrder⟩
+    · intro group member entry listed
+      exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
+  let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
+  let staged := inputs.map (fun input =>
+    (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild (EnumGuard := Constraint) input.2 input.1))
+  have actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
+      some [((edge.entry.key.symbol, staged, residual), own)] := ownRun
+  have readback : staged.map (fun input => (input.1, input.2.1)) = inputs := by
+    dsimp only [staged]
+    simp only [List.map_map]
+    exact List.map_id _
+  refine ⟨ownPacket, ?_, ?_, ?_⟩
+  · rw [ownCore]
+    exact (SourcePruningEnumerationCachedOwn.suspendedState_scalars tries.length before.core).2
+  · intro child bucket member
+    obtain ⟨_tries, _projected, _inputs, lower⟩ := SourcePruningEnumerationSharedEagerChildren.prepared_child_lt
+      caller.checked.native.machine.heap parentEntry edges depth free edge selected scs before own
+      edge.entry.key.symbol staged residual actual child bucket (by rw [readback]; exact member)
+    exact lower
+  · intro visit consume
+    unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
+    rw [actual]
+    simp only []
+    rw [readback]
+end ActualOrdinaryPrefix
+
+section ActualEagerCallback
+variable {Key : Type}
+variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
+
+private def EagerResumeComplete
+    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
+    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
+    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (recursiveDepth : Nat) : Prop :=
+  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
+    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
+    Packet formulas solver inventory caller memos metadata before →
+    Fits seed.2 caller.checked →
+    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
+    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
+    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
+    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
+    eagerReserved bits recursiveDepth seed ceiling →
+    ∃ bound outcome,
+      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
+        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
+          (bound + extra) (bound + extra) (bound + extra) edgesOf)
+        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
+        metadata caller memos.query before
+        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
+      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
+
+private theorem eager_resume_zero_complete
+    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
+    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
+    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
+    EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
+      formulas solver 0 := by
+  intro inventory caller memos before metadata seed ceiling packet bounded known
+    _selectionMembers _selectionLength _mass _reserved
+  obtain ⟨outcome, running, resources⟩ := resume_eager_zero_resources holeKey fits admits graph templates
+    checkEmpty edgesOf stop order formulas solver inventory caller memos before metadata
+    (SourcePruningEnumerationRestart.decision stop order metadata before) seed packet bounded known
+  exact ⟨0, outcome, fun extra => running (0 + extra), resources⟩
+
+private theorem callback_eager_induction_resources
+    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
+    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
+    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
+    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
+    (recursiveDepth : Nat)
+    (recursive : EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
+      stop order formulas solver recursiveDepth)
+    (seed : Seed) (ceiling : Nat)
+    (packet : Packet formulas solver inventory caller memos metadata before)
+    (allocated : FragmentBound before.core.counter fragment)
+    (bounded : Fits seed.2 caller.checked)
+    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
+    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
+    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
+    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
+    (reserved : eagerReserved bits recursiveDepth seed ceiling) :
+    ∃ fuel outcome,
+      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
+        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
+          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
+            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
+          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
+        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
+      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
+  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
+    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
+    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
+  change ∃ fuel outcome,
+    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
+      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
+    OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
+  obtain ⟨callbackFuel, result, after, returned, _stable, frame, _types, _holes, _typing,
+    _currentFits, _currentKnown, callback⟩ :=
+    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver inventory graph templates
+      metadata uv fragment caller memos before seed packet allocated bounded known
+  by_cases rejected : result.1 = true
+  · have resources : OutcomeResources (Typing := Typing) formulas solver caller seed
+        (.complete [] caller memos.query) := by
+      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
+      intro output member
+      exact (List.not_mem_nil member).elim
+    have growth := eagerFinal_ge recursiveDepth seed ceiling
+    refine ⟨callbackFuel, .complete [] caller memos.query, ?_, resources.mono growth.1 growth.2⟩
+    intro extra
+    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
+  · have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
+        (EnumerationExpandableIndex.frame after before).core ≤ ceiling := by
+      change SourcePruningEnumerationPrefixAdmission.suspendedBound after ≤ ceiling
+      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core after frame.values]
+      exact mass
+    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
+      inventory caller memos (EnumerationExpandableIndex.frame after before) result.2 seed ceiling
+      returned bounded known selectionMembers selectionLength massAfter reserved
+    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
+    intro extra
+    have actual := callback (resumeFuel + extra)
+    rw [← Nat.add_assoc] at actual
+    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
+    have observed := running (callbackFuel + extra)
+    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
+    rw [common] at observed
+    exact observed
+end ActualEagerCallback
+
+open SourceCurrentAllocatedNativeResourceForecast (Le)
+open SourcePruningEnumerationSharedIncomingReservation (advance_add)
+
+private theorem nodeReserved_fallback (bits limit own height bound ceiling : Nat)
+    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
+    (reserved : nodeReserved bits limit own height bound ceiling continuation admitted seed) :
+    fallbackReserved bits bound ceiling admitted seed := by
+  cases height with
+  | zero => exact reserved
+  | succ height => exact reserved.1
+
+private theorem tupleReserved_first_callback (bits limit own height count bound ceiling : Nat)
+    (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop) (seed : Seed)
+    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
+      count bound ceiling continuation admitted seed) :
+    admitted (ceiling + count * bound) (advance seed (count * (bound + 1))) := by
+  induction count generalizing ceiling seed with
+  | zero => simpa only [tupleReserved, Nat.zero_mul, Nat.add_zero, advance] using reserved
+  | succ count ih =>
+      let tail := fun retained current => tuplePlan (nodePlan limit own height) count bound retained continuation current
+      let covered := fun retained current => tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
+        count bound retained continuation admitted current
+      have child : nodeReserved bits limit own height bound ceiling tail covered seed := reserved
+      have later := ih (ceiling + bound) (advance seed (bound + 1))
+        (nodeReserved_fallback bits limit own height bound ceiling tail covered seed child).2
+      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
+      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
+      rw [counts, advance_add, masses]
+      exact later
+
+private theorem first_callback_le_tuple_of_growth (limit own height count bound ceiling : Nat)
+    (continuation : Nat → Seed → Seed)
+    (growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
+      current.1 ⊆ (continuation retained current).1) (seed : Seed) :
+    Le (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).2
+      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).2 ∧
+    (continuation (ceiling + count * bound) (advance seed (count * (bound + 1)))).1 ⊆
+      (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed).1 := by
+  induction count generalizing ceiling seed with
+  | zero =>
+      simp only [Nat.zero_mul, Nat.add_zero, advance, tuplePlan]
+      exact ⟨Le.refl _, fun _ member => member⟩
+  | succ count ih =>
+      let child := nodePlan limit own height
+      let tail := fun retained current => tuplePlan child count bound retained continuation current
+      have tailGrowth : ∀ retained current, Le current.2 (tail retained current).2 ∧
+          current.1 ⊆ (tail retained current).1 := by
+        intro retained current
+        exact tuplePlan_ge child (nodePlan_ge limit own height) count bound retained continuation growth current
+      have first := ih (ceiling + bound) (advance seed (bound + 1))
+      have later := fallbackPlan_le_nodePlan limit own height bound ceiling tail tailGrowth seed
+      have counts : (count + 1) * (bound + 1) = (bound + 1) + count * (bound + 1) := by rw [Nat.succ_mul]; omega
+      have masses : ceiling + (count + 1) * bound = (ceiling + bound) + count * bound := by rw [Nat.succ_mul]; omega
+      rw [counts, advance_add, masses]
+      exact ⟨first.1.trans later.1, fun _ member => later.2 (first.2 member)⟩
+
+section ActualTuplePadding
+variable [DecidableEq (EdgeKey Symbol Constraint)]
+
+private theorem tuple_nil_reserved_resources
+    (limit own height count bound ceiling : Nat) (continuation : Nat → Seed → Seed)
+    (admitted : Nat → Seed → Prop)
+    (growth : ∀ retained current, SourceCurrentAllocatedNativeResourceForecast.Le current.2 (continuation retained current).2 ∧
+      current.1 ⊆ (continuation retained current).1)
+    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
+    (solver : SourceGuards.Entailment FullSyntax.Formula) (caller : Caller (bits + 2))
+    (memos : Memos) (before : Cached) (uv : Nat)
+    (visit : Nat → Visitor)
+    (done : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold)
+    (stopped : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
+    (fits : Fits seed.2 caller.checked)
+    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
+    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
+    (reserved : tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
+      count bound ceiling continuation admitted seed)
+    (consumer : ∀ retained current,
+      Fits current.2 caller.checked →
+      Heap (fun guard => guard ∈ current.1) caller.checked.native.machine.heap →
+      SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ retained → admitted retained current →
+      ∃ fuel outcome, (∀ extra, done (fuel + extra) [] caller memos.query before = outcome) ∧
+        OutcomeResources formulas solver caller (continuation retained current) (finish uv outcome)) :
+    ∃ fuel outcome,
+      (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren (visit (fuel + extra))
+        (done (fuel + extra)) (stopped (fuel + extra)) [] caller before memos.query = outcome) ∧
+      OutcomeResources formulas solver caller
+        (tuplePlan (nodePlan limit own height) count bound ceiling continuation seed) (finish uv outcome) := by
+  let entry := advance seed (count * (bound + 1))
+  have entryFits : Fits entry.2 caller.checked := fits.mono
+    (SourcePruningEnumerationSharedIncomingReservation.advance_profile_ge seed (count * (bound + 1)))
+  have entryKnown : Heap (fun guard => guard ∈ entry.1) caller.checked.native.machine.heap := by
+    intro key edge found
+    exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge seed
+      (count * (bound + 1)) (known key edge found)
+  have entryMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling + count * bound :=
+    Nat.le_trans mass (Nat.le_add_right _ _)
+  have entryAdmitted : admitted (ceiling + count * bound) entry :=
+    tupleReserved_first_callback bits limit own height count bound ceiling continuation admitted seed reserved
+  obtain ⟨fuel, outcome, running, resources⟩ := consumer (ceiling + count * bound) entry
+    entryFits entryKnown entryMass entryAdmitted
+  have included := first_callback_le_tuple_of_growth limit own height count bound ceiling continuation growth seed
+  exact ⟨fuel, outcome, running, resources.mono included.1 included.2⟩
+end ActualTuplePadding
+
+section ActualChildInputs
+variable [DecidableEq (EdgeKey Symbol Constraint)]
+
+private def ChildInputs
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (original : Caller (bits + 2)) (metadata : Metadata Typing) (before : Cached) (bucket : List Suspended)
+    (fragment : Fragment) (reached : Caller (bits + 2)) (queries : Queries) (after : Cached) : Prop :=
+  ∃ (next : Inventory) (final : Memos),
+    Post formulas solver next original reached final ∧ final.query = queries ∧
+    Packet formulas solver next reached final metadata after ∧ before.core.counter ≤ after.core.counter ∧
+    EnumeratedOrigin before.core after.core ∧
+    (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
+      Avoids before.core.representatives held bucket → EnumerationDriver.Protected held before.core after.core) ∧
+    (∀ allowed, EnumerationReferences.ReferencesAllowed allowed before.core →
+      EnumerationReferences.InputsAllowed allowed bucket → EnumerationReferences.ReferencesAllowed allowed after.core) ∧
+    FragmentBound after.core.counter fragment ∧ PendingFragment after.core fragment ∧
+    ∀ held, held < before.core.counter → IsRoot before.core.representatives held →
+      Avoids before.core.representatives held bucket → FragmentAvoid after.core.representatives held fragment
+end ActualChildInputs
+
+section ActualFallbackResources
+variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
+
+private theorem eager_fallback_resources
+    (seed : Seed) (bound ceiling : Nat) (continuation : Nat → Seed → Seed) (admitted : Nat → Seed → Prop)
+    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
+    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
+    (before : Cached) (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
+    (bucket : List Suspended) (incoming : Node) (uv : Nat)
+    (done : Nat → Fragment → Caller (bits + 2) → Queries → Cached → Fold)
+    (stopped : Nat → ChildDispatch.Observation (bits + 2) → Option Cached → Fold)
+    (packet : Packet formulas solver inventory caller memos metadata before)
+    (bounded : ∀ sc ∈ bucket, sc.var < before.core.counter) (pending : InputsPending before.core bucket)
+    (available : Available caller.checked.native.machine.heap incoming) (closed : incoming.free = [])
+    (fits : Fits seed.2 caller.checked)
+    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
+    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
+    (bucketBound : bucket.length ≤ bound)
+    (reserved : fallbackReserved bits bound ceiling admitted seed)
+    (fallback : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal bucket incoming = false)
+    (yes : ∀ fragment reached saved after,
+      ChildInputs formulas solver caller metadata before bucket fragment reached saved after →
+      Fits (advance seed (bound + 1)).2 reached.checked →
+      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
+      SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound →
+      admitted (ceiling + bound) (advance seed (bound + 1)) →
+      ∃ fuel outcome, (∀ extra, done (fuel + extra) fragment reached saved after = outcome) ∧
+        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
+          (finish uv outcome))
+    (no : ∀ (reached : Caller (bits + 2)) (saved : Queries) (after : Cached)
+        (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting)
+        (next : Inventory) (final : Memos),
+      Post formulas solver next caller reached final → final.query = saved →
+      Fits (advance seed (bound + 1)).2 reached.checked →
+      Heap (fun guard => guard ∈ (advance seed (bound + 1)).1) reached.checked.native.machine.heap →
+      admitted (ceiling + bound) (advance seed (bound + 1)) →
+      ∃ fuel outcome,
+        (∀ extra, stopped (fuel + extra) ((.ok (some []), reached, saved, outer, waiting)) (some after) = outcome) ∧
+        OutcomeResources formulas solver reached (continuation (ceiling + bound) (advance seed (bound + 1)))
+          (finish uv outcome)) :
+    ∃ fuel outcome,
+      (∀ extra, SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
+        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
+        edgesOf bucket incoming caller before memos.query (done (fuel + extra)) (stopped (fuel + extra)) = outcome) ∧
+      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
+  have countLe : bucket.length + 1 ≤ bound + 1 := by omega
+  obtain ⟨r, n, p, h, k, raw, afterCaller, after, savedQueries, final, next, afterRoots,
+    outer, waiting, retained, eagerExact⟩ := fallback_complete_resources_cps seed formulas solver inventory caller memos
+      metadata before checkEmpty edgesOf bucket incoming packet bounded pending available closed fits
+      (reserved.1.prefix countLe) known fallback
+  obtain ⟨headRun, post, query, growth, paths, storage, realized, counts, flags,
+    origin, protects, references, pendingAfter, shape, actualFits, actualKnown⟩ := retained
+  have paddedFits : Fits (advance seed (bound + 1)).2 afterCaller.checked :=
+    actualFits.mono (SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed countLe)
+  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
+      afterCaller.checked.native.machine.heap := by
+    have included : (advance seed (bucket.length + 1)).1 ⊆ (advance seed (bound + 1)).1 := by
+      obtain ⟨extra, same⟩ := Nat.exists_eq_add_of_le countLe
+      rw [same, advance_add seed (bucket.length + 1) extra]
+      exact SourcePruningEnumerationSharedIncomingReservation.advance_alphabet_ge
+        (advance seed (bucket.length + 1)) extra
+    intro key edge found
+    exact included (actualKnown key edge found)
+  have observed : ChildDispatch.run checkEmpty r n p h k bucket incoming caller before memos.query =
+      ((.ok (some raw), afterCaller, savedQueries, outer, waiting), some after) := by
+    simpa only [Nat.add_zero] using headRun 0 0 p h 0 (Nat.le_refl _) (Nat.le_refl _)
+  have scalars := ChildDispatch.observed_scalar_bounds checkEmpty r n p h k bucket incoming
+    caller before memos.query after (congrArg Prod.snd observed)
+  have afterMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound :=
+    Nat.le_trans scalars.2 (Nat.add_le_add mass bucketBound)
+  have completed : ∃ fuel outcome,
+      (∀ extra,
+        (match raw with
+        | [.ok (fragment, _returned)] => done (fuel + extra) fragment afterCaller savedQueries after
+        | _ => stopped (fuel + extra) ((.ok (some raw), afterCaller, savedQueries, outer, waiting)) (some after)) = outcome) ∧
+      OutcomeResources formulas solver caller (fallbackPlan bound ceiling continuation seed) (finish uv outcome) := by
+    rcases shape with rejected | ⟨fragment, singleton, afterSafe, fragmentBound, fragmentPending, fragmentAvoid⟩
+    · obtain ⟨fuel, outcome, running, resources⟩ := no afterCaller savedQueries after outer waiting next final
+        post query paddedFits paddedKnown reserved.2
+      refine ⟨fuel, outcome, ?_, resources.post post⟩
+      intro extra
+      rw [rejected]
+      exact running extra
+    · have protectsEnumerated (held : Nat) (storedFragment : Fragment)
+          (stored : before.core.values[held]? = some (.enumerated storedFragment)) :
+          EnumerationDriver.Protected held before.core after.core := by
+        obtain ⟨inside, root⟩ := enumerated_root before.core packet.safe held storedFragment stored
+        exact protects held inside root (pending held storedFragment stored)
+      have afterPacket : Packet formulas solver next afterCaller final metadata after := by
+        refine ⟨post.context, afterSafe, pendingAfter packet.pending,
+          ⟨afterRoots, paths, storage, realized, counts, flags⟩, ?_, ?_⟩
+        · obtain ⟨level, frontier, oldOrder⟩ := packet.ordered
+          obtain ⟨nextLevel, afterOrder⟩ := EnumerationOrder.stratified_preserved before.core after.core
+            afterSafe level frontier oldOrder origin protectsEnumerated
+          exact ⟨nextLevel, frontier, afterOrder⟩
+        · intro group member entry listed
+          exact Nat.lt_of_lt_of_le (packet.bounded group member entry listed) growth
+      have inputs : ChildInputs formulas solver caller metadata before bucket fragment afterCaller savedQueries after :=
+        ⟨next, final, post, query, afterPacket, growth, origin, protects, references,
+          fragmentBound, fragmentPending, fragmentAvoid⟩
+      obtain ⟨fuel, outcome, running, resources⟩ := yes fragment afterCaller savedQueries after inputs
+        paddedFits paddedKnown afterMass reserved.2
+      refine ⟨fuel, outcome, ?_, resources.post post⟩
+      intro extra
+      rw [singleton]
+      exact running extra
+  obtain ⟨callbackFuel, outcome, consumeRun, resources⟩ := completed
+  let total := r + n + p + h + k + callbackFuel
+  refine ⟨total, outcome, ?_, resources⟩
+  intro extra
+  let work := total + extra
+  have rle : r ≤ work := by dsimp [work, total]; omega
+  have nle : n ≤ work := by dsimp [work, total]; omega
+  have kle : k ≤ work := by dsimp [work, total]; omega
+  have re : r + (work - r) = work := by omega
+  have ne : n + (work - n) = work := by omega
+  have ke : k + (work - k) = work := by omega
+  have head := eagerExact (work - r) (work - n) work work (work - k)
+    (by dsimp [work, total]; omega) (by dsimp [work, total]; omega) (done work) (stopped work)
+  simp only [re, ne, ke] at head
+  change SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work
+    edgesOf bucket incoming caller before memos.query (done work) (stopped work) = outcome
+  rw [head]
+  have actual := consumeRun (r + n + p + h + k + extra)
+  have same : callbackFuel + (r + n + p + h + k + extra) = work := by dsimp [work, total]; omega
+  simpa only [same] using actual
+end ActualFallbackResources
+
+end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
```

### checked1057 to failed1057

```diff
--- checked1057.lean
+++ failed1057.lean
@@ -987 +987 @@
-      rw [same, advance_add seed (bucket.length + 1) extra]
+      rw [same, advance_add]
```

### failed1057 to checked908

```diff
--- failed1057.lean
+++ checked908.lean
@@ -1 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedChildScalarBounds
@@ -909,148 +907,0 @@
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
-      rw [same, advance_add]
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
```

### checked908 to checked805

```diff
--- checked908.lean
+++ checked805.lean
@@ -805,103 +804,0 @@
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
```

### checked805 to failed805

```diff
--- checked805.lean
+++ failed805.lean
@@ -765 +765 @@
-  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
+  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
```

### failed805 to checked693

```diff
--- failed805.lean
+++ checked693.lean
@@ -693,112 +692,0 @@
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
-  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
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
```

### checked693 to failed692

```diff
--- checked693.lean
+++ failed692.lean
@@ -593 +593 @@
-          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
+          (children edge scs before.core.counter tries).map (fun input =>
@@ -597 +597 @@
-          (SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries).map (fun input =>
+          (children edge scs before.core.counter tries).map (fun input =>
@@ -607 +607 @@
-      (∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
+      (∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
@@ -613 +613 @@
-          ∀ incoming bucket, (incoming, bucket) ∈ SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries →
+          ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
@@ -689 +688,0 @@
-    simp only []
```

### failed692 to checked568

```diff
--- failed692.lean
+++ checked568.lean
@@ -1,2 +0,0 @@
-import MicroCFTA.EnumerationStratifiedTransport
-import MicroCFTA.SourcePruningEnumerationEdgeScalarBounds
@@ -570,122 +567,0 @@
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
-          (children edge scs before.core.counter tries).map (fun input =>
-            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own)] ∧
-      ExceptT.run (action before.core) =
-        [.ok ((edge.entry.key.symbol,
-          (children edge scs before.core.counter tries).map (fun input =>
-            (input.1, input.2, SourcePruningEnumerationShallowChild.prepareChild input.2 input.1)), residual), own.core)] ∧
-      own.core = suspendedState tries.length before.core ∧
-      own.core.counter = before.core.counter + tries.length ∧
-      own.core.representatives = before.core.representatives ∧
-      Safe own.core ∧ Roots own.core.representatives roots ∧ PendingRealized caller.checked.native.machine.heap own.core ∧
-      EnumerationCanonicalWaiting.Correct roots own.core.values own.waiting ∧
-      (∀ slot, SourcePruningEnumerationNativeIndex.candidate caller.checked.native.machine.heap
-        ((own.core.values[slot]?).getD .eliminated) = some (own.expandable slot)) ∧
-      InputsPending own.core (scs ++ suspendedVars before.core.counter tries) ∧
-      (∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
-        Available caller.checked.native.machine.heap incoming ∧ incoming.free = [] ∧
-        (∀ sc ∈ bucket, sc.var < own.core.counter) ∧ InputsPending own.core bucket) ∧
-      (∀ held, held < before.core.counter → IsRoot before.core.representatives held →
-        Avoids before.core.representatives held scs →
-        EnumerationDriver.Protected held before.core own.core ∧
-          ∀ incoming bucket, (incoming, bucket) ∈ children edge scs before.core.counter tries →
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
-    rw [readback]
-end ActualOrdinaryPrefix
-
```

### checked568 to checked381

```diff
--- checked568.lean
+++ checked381.lean
@@ -1,4 +0,0 @@
-import MicroCFTA.SourcePruningEnumerationSharedPreparedZeroOutcomeResources
-import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
-import MicroCFTA.SourcePruningEnumerationSharedChildResources
-import MicroCFTA.SourcePruningEnumerationSharedPreparedOutcomeResources
@@ -386,183 +381,0 @@
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
-end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
```

## Frozen artifact: eager-resource-public-target-header.txt

SHA256 `01c37c9dabf7d093edb1741efeccf5c5d39378df0f7d76cfc7cf0883ea69b2fb`. This is the preserved text at its stated stage.

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

## Frozen artifact: eager-resource-private-contracts.md

SHA256 `7e8240df5eaabc9d38200c61ad72a15a76f215b5806e40b4f6133ad8171f8795`. This is the preserved text at its stated stage.

```text
# Actual eager resource CPS contracts
Status: PUBLIC TARGET UNPROVED. New private operational segment only.
The literal public target is frozen in eager-resource-public-target-header.txt.
It preserves every old finite-resource input except replacing old shallow
Reserved by the computed eagerReserved. It retains ENTIRE OutcomeResources.
No continuation, child-resource, rank, after-heap or desired Packet supplier is public.

Private outer contract: generalize all current metadata, full Memos, caller,
inventory, cache, original Seed/mass ceiling and arbitrary current Next decision.
At each outer depth, current Packet/Fits/Heap/selector membership+length/mass and
computed eagerReserved yield one actual resumeWithChild(eagerChild) result for
all larger common workFuel. Keep exact complete/stopped endpoints and all outputs.
The arbitrary Next parameter is essential at the concrete continueWith boundary.

Private height contract: fix captured heap, current original guard alphabet,
row/arity/own ceilings and literal Available input. Derive height from checked
CapturedBounds, and actual child decrease from prepared_child_lt. Generalize
current native caller/full Memos/cache, bucket bound, and the ACTUAL consumers.
All continuation resource hypotheses stay private, are quantified over derived
current endpoint fields, and must be discharged by tuple/outer IH.

Private tuple contract: every head success runs its remaining tuple immediately.
Successful inputs carry the derived full Post/query, current Packet/validity,
protection/references/pending and fragment bounds required by that continuation.
Its stopped observation retains its actual optional candidate and native endpoint.
Do not require Safe from a rejected transient candidate. Old captured cache resets
between siblings; the entire native caller and full Memos thread after each tail.

The first new source segment preserves the exact checked381 prefix after only
required leading operational imports. It calls actual ChildDispatch resources
ONCE for fallback, keeps EVERY old returned field and appends the entire eager
CPS equality for all stable larger fuels and arbitrary consumers. It asserts no
resource preservation of an unrestricted consumer. This is the genuine terminal/
opaque/empty base for ordinary-height induction, not a new finite-depth example.
Private nil/cons tuple proofs use the EXISTING visitChildren operation and exact
OutcomeResources applied to finish; child/consumer hypotheses are private IHs.
No public resource-completion theorem will be declared until the ordinary-row
and outer-depth inductions discharge them for concrete tails/finalization/hooks.

Remaining: actual own-prefix Packet, ordinary row scan/height IH, all intermediate
planned entry reservations, parent finalization and callback composition, captured
sibling restoration, stable common workFuel, then the full outer-depth induction.
The copied381 private planner helpers remain available without exposing a new API.
```

## Frozen artifact: eager-resource-target-review.md

SHA256 `52ed28e8d6acef08384712cc2abc2f470f52b314060142434b50bdf5e56cc6f8`. This is the preserved text at its stated stage.

```text
# Actual eager resource target and private CPS scope review

2026-11-13 00:12 CET. Frozen target/contracts review only; mutable working source unread.
PUBLIC OPERATIONAL THEOREM UNPROVED. No compiler action was run.
Target: eager-resource-public-target-header.txt, SHA256
01c37c9dabf7d093edb1741efeccf5c5d39378df0f7d76cfc7cf0883ea69b2fb.
Contracts: eager-resource-private-contracts.md, SHA256
7e8240df5eaabc9d38200c61ad72a15a76f215b5806e40b4f6133ad8171f8795.

Mechanical whole-header comparison against the old public resource law
PASSED after exactly four intended changes: theorem name, concrete
run→runEager, shallow Reserved→eagerReserved and final→eagerFinal.
All other normalized header tokens match. Old comparison source:
SharedPreparedFiniteResources, SHA256
e19e37036975fa08a9ef4a25425ed65b5159abfd4080fa0c72701a8b74a6a2e4.

All current configuration and resource assumptions remain: full Memos,
caller/inventory/metadata/cache, Packet, Fits, physical guard Heap,
selector membership/length, original seed and suspended-mass ceiling.
Only the admission predicate changes to the computed eagerReserved.
No public arbitrary consumer, child execution, after-Packet, model,
future fit/heap, rank or callback-resource supplier is present.

The target retains ONE concrete runEager outcome at ALL larger common
work fuels and the ENTIRE SAME OutcomeResources constant, at eagerFinal.
That constant retains actual reached caller/inventory/full Memos, Post,
Fits and Heap; complete endpoint equalities or actual optional stopped
endpoint; and OutputResources for EVERY output, including stopped prefixes.
It does not fill an absent endpoint or discard earlier outputs.
No output existence, adequate recursive depth, noStop finishedness,
Program-role/readback or language-completeness conclusion is included.

The private contracts couple actual current caller/full Memos at depth,
height and tuple steps. Tuple tails run at the SAME successful head
endpoint; captured sibling caches reset while native endpoints thread.
The tail IH must consume the particular full Memos/Post/query witness
from that head receipt, not a separately chosen endpoint. Stopped outputs
retain their own resources even if the optional endpoint is absent.
No Safe assumption may be imposed on a rejected transient candidate.
These requirements are explicit in the frozen contracts and fit the target.

Arbitrary-consumer CPS equality alone is not consumer resource preservation.
The contracts correctly keep that distinction: only derived current-input
continuation hypotheses are private, and concrete tuple/outer IHs must
discharge them. They assert no preservation for an unrestricted consumer.
A fuel-varying concrete closure also needs its actual IH stability to
obtain the public ONE common bound/outcome; pointwise equality is insufficient.

Genuine remaining bridge: match each actual own-prefix/child/tail/callback
entry to its EXACT computed seed/mass and admission predicate. Pure
first-row inclusion or alphabet inclusion does not establish actual
Fits/Heap, all-row execution or consumer completion. Captured bounds apply
to immutable OLD payloads; later records need the current computed alphabet.
Fixed row/arity ceilings also need actual-input origin/filtering facts;
height descent alone does not bound the row count of a new value.
The frozen contracts list these as unproved operational obligations.
This review does not assert that helpers are absent from mutable work.

For later original-input instantiation, the old shallow enumBits/reservation
must not be reused as eager admission without proof. A width based on
original eagerFinal can use checked eagerReserved_of_final_room. That is
separate from the current public operational target.
No public-interface defect found. The full theorem remains unproved.
No source, repository, Git, Haskell or evidence action was run.
```

## Frozen artifact: private-eager-resume-contract.txt

SHA256 `f3256207e5e853a837de64d23d4c66b63a3376c3635566f2fe985bf8884b3a40`. This is the preserved text at its stated stage.

```text
private def EagerResumeComplete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    eagerReserved bits recursiveDepth seed ceiling →
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (bound + extra) (bound + extra)
          (bound + extra) (bound + extra) (bound + extra) edgesOf)
        holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveDepth
        metadata caller memos.query before
        (SourcePruningEnumerationRestart.decision stop order metadata before) = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
```

## Frozen artifact: private-eager-callback-header.txt

SHA256 `1a9a58517f1820dde9d09e1da5ac4c38e31d2f3d9628a896420ea2f9268733cd`. This is the preserved text at its stated stage.

```text
private theorem callback_eager_induction_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
```

## Frozen artifact: eager-tuple-padding-stage-note.md

SHA256 `a0347c3aa387f1b51de334162ea4567c1832e72a19d718f319dba6e52619fb19`. This is the preserved text at its stated stage.

```text
# Actual tuple base at its computed continuation stage
Status: ROOT STRICT PASS, 2026-11-13 00:35 CET. PRIVATE SEGMENT. Public eager resource target is UNPROVED.
Source eager-cps-tuple-padding-stage.lean, 908 lines.
SHA256: ebe1a70bcc8b511d2ae658985071101afeb9ea34d6cb4660fc6cc8e0a0c4822b.
Starts from checked805/4e87f60f (exact source except final namespace closing line).
Old381 planner/admission body remains byte-exact. Prior snapshots remain immutable.

Three new private arithmetic helpers:
- nodeReserved_fallback extracts the already computed fallback admissions.
- tupleReserved_first_callback derives admission at the SAME tuple's first
  padding-path continuation entry: cap + count*B, advance seed(count*(B+1)).
- first_callback_le_tuple_of_growth generalizes the checked concrete inclusion
  to a PRIVATE growth-certified continuation, needed for nested tuple tails.
No cross-seed monotonicity or future capacity assumption is used.

Private tuple_nil_reserved_resources then proves the literal actual tuple base
with zero remaining children, for ANY remaining padding count/height/width.
It derives Fits, guard Heap and continuation admission at the computed entry,
uses the PRIVATE concrete consumer IH once there, and transports the ENTIRE
OutcomeResources of the SAME fullFold into THAT tuple's final plan. No child
operation or native query runs for this actual empty tuple. Full actual Fold
and stopped-prefix/native/full-Memos resource fields remain unchanged.

The PRIVATE consumer premise is an IH contract, not a public provider or an
assertion that arbitrary consumers have finite work. It must later be discharged
by actual finalization/callback/tail induction. The public concrete runEager
target has no such premise and remains UNPROVED. Actual nonempty tuple/ordinary
height and positive outer-depth closure remain open. No compiler/repository/Git/
Haskell/checkpoint source was changed.
```

## Frozen artifact: eager-fallback-resources-stage-note.md

SHA256 `5b3b158b262327f675b7514e12a91915c2cda49e3f52e4d67ac5c3598d08a161`. This is the preserved text at its stated stage.

```text
# Actual fallback head resources inside the computed plan
Status: UNCOMPILED PRIVATE SEGMENT. Public eager resource target remains UNPROVED.
Source eager-cps-fallback-resources-stage.lean: 1057 lines.
SHA256 59c7c78ddece14455cb6c4b85525265766c40ec096855febf4f6e934d70bc538.
Extends checked908/ebe1a70b by149 lines, including one operational scalar import.
Old checked381 definitions/public laws remain byte-exact. All prior snapshots remain.

Private ChildInputs,15L/b774adf0, is only a conjunction alias for ACTUAL pre-consumer
Post/full-Memos/query/Packet/counter/origin/protection/reference/fragment fields.
It introduces no datatype, gate or public invariant. These facts are derived
internally from the SAME actual child producer, not assumed from a future state.

Private eager_fallback_resources, frozen42L header c83b9451:
- Calls the checked full fallback producer ONCE for the actual current bucket.
- Derives native Fits/physical guard Heap at advance seed(bound+1) by padding
  the SAME schedule from the actual bucket length. It uses no cross-seed law.
- Derives actual returned suspended mass from the SAME observed child dispatch.
- Derives SAME metadata Packet and ALL ChildInputs history for a success.
- Takes continuation admission from the computed fallbackReserved, not an oracle.
- Uses PRIVATE certified success/failure consumer IHs at that exact planned stage.
- Composes the actual Post and derives ONE common stable fuel for both native
  dispatch and actual CPS consumer. The exact full actual Fold is retained.
- Retains ENTIRE OutcomeResources at fallbackPlan, including stopped prefix,
  actual native endpoint, inventory, full Memos/Post, Fits/Heap and all outputPackets.
Rejection does not assume Safe/Packet for its intermediate candidate cache.
No arbitrary consumer finite-work/resource claim is made.

The private consumer IHs still need discharge for the actual remaining tuple and
concrete lower-depth callback. Ordinary-height rows and positive outer-depth
closure remain OPEN. The public target has NONE of those consumer premises.
No compiler/repository/Git/Haskell/checkpoint source was changed.
```


## Reproduce the private stage

Reconstruct checked1057 from the pinned checked381 Git source and its forward patch.
From the project lean directory, under the existing serial 4 GiB cap, run:

```sh
nix-shell ../shell.nix --run "lake env lean -j1 -DwarningAsError=true /tmp/checked1057.lean"
```
