# Actual eager role observations and callback reuse

Base: 15e254a046182ec6e7f8c469508e5700e18ec190.
Two existing source modules change. SharedDriver has 1862 lines; Reservation
has 5387 lines. There are eight public laws across the two modules. Three are
newly callable existing local observations. No public whole-eager output-role
law is added. Every old public name remains present. Old workers stay unchanged.

SharedDriver only exposes observed_prefix_slots, render_stable_slots and
prepared_marked_fields and adds three comments. Each header and proof body is
exact. The inverse visibility transformation restores all old1859 bytes.
These observations concern the common prefix/preparation action, not a whole
shallow execution. The 2420-module closure has no Reservation dependency.
The eager proof can therefore reuse the SAME actual observation directly.
The earlier two SelectedPrefix exports and repeated-observer draft are retained
as unused proposals in the prior subtree-return source audit.

The private unmarked callback observer derives middle roles from current entry
slots, the stored parent and the full old ChildInputs. It calls the existing
finalizer-packet producer once. Its SAME core equality and UnmarkedWrite give
finalized slots. Its one callback producer supplies full Memos/Packet/Frame,
and that SAME Frame gives callback slots. It demands no Program fragment role
of Type data. Its combined finalizer/continuation equation remains exact.

The private recorded-callback helper consumes the ENTIRE already computed
receipt. It runs no finalizer, callback or native producer. The false branch
derives current frame slots/mass and invokes lower concrete Resume once.
The true branch emits no outputs. One additive bound retains the SAME actual
outcome at every larger common fuel, with full old OutcomeResources first.
The raw53-line contract is preserved. The only header repair prefixes the
unused allocated binder with an underscore; its FragmentBound premise remains.
The only body repair fixes Typing explicitly on an empty-output annotation.
No linter, resource guard or native endpoint is weakened.

Full own Nix/Lake/strict checks, explicit exact namespaces and standard-only
axioms pass for both modules. Full Audit and three portable packets pass.
There are 5894 live modules, eight affected modules and 4891 Audit imports.
Audit checks 94824 theorem declarations. This count includes generated private
declarations. It is not a public-law count or a completion measure. Old public
statements remain present, with exact headers and proofs in the visibility edit.
Audit retains its entire old266043-byte prefix and adds three explicit checks
and axiom reports. The new file has266642 bytes.

All jobs retain the existing serial4GiB maximum/high,swap0 and one Lean thread.
There are no Haskell changes. .hypha remains protected. No large output archive
is needed. Source, exact reverse patches and frozen fragments retain the evidence.

Concrete positive-depth captured rows, preparation, expansion, outer Resume/depth
and original-input eager Program readback remain open. Private lower-depth IHs
are not new public providers. Full partial Type model pullback and finite model
existence remain separate, with the prior parked/partial100 audit and9/14 targets.
The full default/order/multiplicity/size/count/weight/training/inverse/Haskell
objective remains active. No new model witness, countermodel or Haskell defect
is established by these local observations.

## Source stages and actual reverse replay

### Reverse driver1862 to driver1859

```diff
--- driver1862.lean
+++ driver1859.lean
@@ -537,2 +537 @@
-/-- The same actual prefix observation retains the marked Program slots. -/
-theorem observed_prefix_slots
+private theorem observed_prefix_slots
@@ -719,2 +718 @@
-/-- A stable read retains the same marked Program slots. -/
-theorem render_stable_slots
+private theorem render_stable_slots
@@ -742,2 +740 @@
-/-- The same successful preparation retains the marked Program fields and bucket scope. -/
-theorem prepared_marked_fields
+private theorem prepared_marked_fields
```

### Reverse math5387-final to math5387-typing

```diff
--- math5387-final.lean
+++ math5387-typing.lean
@@ -5302 +5302 @@
-    (_allocated : FragmentBound before.core.counter fragment)
+    (allocated : FragmentBound before.core.counter fragment)
```

### Reverse math5387-typing to math5387-raw

```diff
--- math5387-typing.lean
+++ math5387-raw.lean
@@ -5357 +5357 @@
-    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked) formulas solver caller seed
+    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller seed
```

### Reverse math5387-raw to math5285

```diff
--- math5387-raw.lean
+++ math5285.lean
@@ -5285,102 +5284,0 @@
-section ActualRecordedProgramCallback
-variable {Key : Type}
-variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
-
-private theorem eager_program_callback_from_recorded_resources
-    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
-    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
-    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
-    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
-    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
-    (recursiveDepth : Nat)
-    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
-      stop order formulas solver recursiveDepth)
-    (seed : Seed) (ceiling : Nat)
-    (packet : Packet formulas solver inventory caller memos metadata before)
-    (allocated : FragmentBound before.core.counter fragment)
-    (bounded : Fits seed.2 caller.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
-    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
-    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
-    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
-    (reserved : eagerReserved bits recursiveDepth seed ceiling)
-    (valid : Constraint → Prop) (marked : Nat → Prop)
-    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
-      caller.checked.native.machine.heap before.core marked)
-    (callbackFuel : Nat) (result : Bool × Metadata Typing)
-    (afterCore : EnumerationState.State Symbol Constraint)
-    (recorded :
-      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
-      EnumerationDriver.RenderStable before.core afterCore ∧
-      EnumerationCompressionFrame.Frame before.core afterCore ∧
-      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
-      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
-      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
-      ∀ extra,
-        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
-          before.core result afterCore ∧
-        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
-          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
-        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
-            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
-          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
-            (callbackFuel + extra) metadata uv fragment caller memos.query before =
-            if result.1 then .complete [] caller memos.query
-            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
-              (SourcePruningEnumerationRestart.decision stop order result.2
-                (EnumerationExpandableIndex.frame afterCore before))) :
-    ∃ fuel outcome,
-      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
-        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
-          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
-            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
-          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
-        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
-      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
-  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
-    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
-    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
-  change ∃ fuel outcome,
-    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
-      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
-    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
-      (eagerFinal recursiveDepth seed ceiling) outcome
-  obtain ⟨returned, _stable, frame, _types, _holes, _typing, _currentFits, _currentKnown, callback⟩ := recorded
-  by_cases rejected : result.1 = true
-  · have retained : OutcomeResources (Typing := Typing) formulas solver caller seed
-        (.complete [] caller memos.query) := by
-      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
-      intro output member
-      exact (List.not_mem_nil member).elim
-    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller seed
-        (.complete [] caller memos.query) := by
-      exact ⟨retained, fun _ member => by cases member⟩
-    have growth := eagerFinal_ge recursiveDepth seed ceiling
-    refine ⟨callbackFuel, .complete [] caller memos.query, ?_,
-      resources_outputs_mono growth.1 growth.2 resources⟩
-    intro extra
-    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
-  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
-      caller.checked.native.machine.heap before.core afterCore marked frame slots
-    have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
-        (EnumerationExpandableIndex.frame afterCore before).core ≤ ceiling := by
-      change SourcePruningEnumerationPrefixAdmission.suspendedBound afterCore ≤ ceiling
-      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core afterCore frame.values]
-      exact mass
-    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
-      inventory caller memos (EnumerationExpandableIndex.frame afterCore before) result.2 seed ceiling
-      returned bounded known selectionMembers selectionLength massAfter reserved valid marked afterSlots
-    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
-    intro extra
-    have actual := callback (resumeFuel + extra)
-    rw [← Nat.add_assoc] at actual
-    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
-    have observed := running (callbackFuel + extra)
-    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
-    rw [common] at observed
-    exact observed
-
-end ActualRecordedProgramCallback
-
```

### Reverse math5285 to math5163

```diff
--- math5285.lean
+++ math5163.lean
@@ -1,2 +0,0 @@
-import MicroCFTA.SourceSynthesisProgramRolesSharedDriver
-import MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite
@@ -5165,120 +5162,0 @@
-section ActualFinalizedUnmarkedCallback
-variable [DecidableEq (EdgeKey Symbol Constraint)]
-
-private theorem finalized_unmarked_callback_observation
-    (valid : Constraint → Prop) (marked : Nat → Prop)
-    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
-    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
-    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
-    (ready : EnumerationDriver.Ready uv before.core)
-    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
-    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (unmarked : ¬marked uv)
-    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
-      original.checked.native.machine.heap before.core marked)
-    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle)
-    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (seed : Seed)
-    (bounded : Fits seed.2 reached.checked)
-    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
-    ∃ (next : Inventory) (final : Memos) (finalizeFuel : Nat) (finalized : Cached)
-      (callbackFuel : Nat) (result : Bool × Metadata Typing) (afterCore : EnumerationState.State Symbol Constraint),
-      (Post formulas solver next original reached final ∧ final.query = saved ∧
-      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
-        (finalizeFuel + extra) uv fragment middle = some finalized) ∧
-      Packet formulas solver next reached final metadata finalized ∧
-      FragmentBound finalized.core.counter fragment ∧
-      finalized.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
-      SourcePruningEnumerationPrefixAdmission.suspendedBound finalized.core ≤
-        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
-      finalized.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot finalized.core.representatives uv) ∧
-      (Packet formulas solver next reached final result.2 (EnumerationExpandableIndex.frame afterCore finalized) ∧
-      EnumerationDriver.RenderStable finalized.core afterCore ∧
-      EnumerationCompressionFrame.Frame finalized.core afterCore ∧
-      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
-      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
-      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
-      ∀ extra,
-        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
-          finalized.core result afterCore ∧
-        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
-          metadata uv (.inl fragment) finalized.core) = [.ok (result, afterCore)] ∧
-        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
-            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
-          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
-            (callbackFuel + extra) metadata uv fragment reached final.query finalized =
-            if result.1 then .complete [] reached final.query
-            else recur result.2 reached final.query (EnumerationExpandableIndex.frame afterCore finalized)
-              (SourcePruningEnumerationRestart.decision stop order result.2
-                (EnumerationExpandableIndex.frame afterCore finalized))) ∧
-      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
-        reached.checked.native.machine.heap finalized.core marked ∧
-      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
-        reached.checked.native.machine.heap (EnumerationExpandableIndex.frame afterCore finalized).core marked ∧
-      ∀ extra (initialCaller : Caller (bits + 2)) (initialQueries : Queries)
-        (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
-          NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
-        let work := finalizeFuel + callbackFuel + extra
-        let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finalized
-        let callbackResult : NativeContinuations.HookResult
-            (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
-          if result.1 then .complete [] reached saved
-          else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
-            (SourcePruningEnumerationRestart.decision stop order result.2
-              (EnumerationExpandableIndex.frame afterCore finalized))
-        (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
-        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
-            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
-            initialCaller initialQueries (some (.complete fragment reached saved finished))
-        | none => SourcePruningEnumerationSharedReceiptContinuation.run
-            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
-            initialCaller initialQueries (some (.finalizeStopped fragment reached saved middle))) =
-        match callbackResult with
-        | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
-        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
-
-    := by
-  have inherited : ∀ held, marked held → Avoids before.core.representatives held scs := by
-    intro held heldMarked
-    exact slots.incoming held heldMarked (.unenumerated (some handle) scs)
-      (List.mem_of_getElem? stored)
-  have middleSlots := child_inputs_program_slots valid SourceSynthesisLabelProgramBuildRoles.literal marked
-    formulas solver original reached metadata before middle scs fragment saved ready.safe slots inherited data
-  obtain ⟨next, final, finalizeFuel, finalized, finalReceipt⟩ :=
-    finalize_child_inputs_packet formulas solver original reached metadata before middle uv handle scs fragment saved
-      ready stored incoming data
-  have retained := finalReceipt
-  obtain ⟨_post, querySame, finalAt, finalPacket, fragmentBound, core, _mass, _stored, _root⟩ := retained
-  let resetCore := {middle.core with expansionAncestry := []}
-  have resetSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
-      SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore marked :=
-    ⟨middleSlots.bounded, middleSlots.roots, middleSlots.incoming, middleSlots.stored⟩
-  have written : Success (EnumerationState.setValue uv (.enumerated fragment)) resetCore () finalized.core :=
-    (EnumerationDriver.modify_success _ _ _).mpr core
-  have finalizedSlots := (SourceSynthesisProgramRolesUnmarkedWrite.setValue_unmarked_program_slots valid
-    SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore finalized.core
-    marked resetSlots uv unmarked (.enumerated fragment) (by intro _ _ _ member; cases member) written).2.1
-  obtain ⟨callbackFuel, result, afterCore, callback⟩ :=
-    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
-      metadata uv fragment reached final finalized seed finalPacket fragmentBound bounded known
-  have callbackFields := callback
-  obtain ⟨_callbackPacket, _stable, callbackFrame, _types, _holes, _typing, _fits, _known, callbackAt⟩ := callbackFields
-  have callbackSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
-    reached.checked.native.machine.heap finalized.core afterCore marked callbackFrame finalizedSlots
-  refine ⟨next, final, finalizeFuel, finalized, callbackFuel, result, afterCore,
-    finalReceipt, callback, finalizedSlots, callbackSlots, ?_⟩
-  intro extra initialCaller initialQueries recur stop order
-  have finalizeAt := finalAt (callbackFuel + extra)
-  rw [← Nat.add_assoc] at finalizeAt
-  have continued := (callbackAt (finalizeFuel + extra)).2.2 recur stop order
-  have same : callbackFuel + (finalizeFuel + extra) = finalizeFuel + callbackFuel + extra := by omega
-  rw [same, querySame] at continued
-  dsimp only
-  rw [finalizeAt]
-  simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
-  rw [continued]
-  cases observed : (if result.1 then NativeContinuations.HookResult.complete [] reached saved
-      else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
-        (SourcePruningEnumerationRestart.decision stop order result.2
-          (EnumerationExpandableIndex.frame afterCore finalized))) <;> rfl
-
-end ActualFinalizedUnmarkedCallback
-
```

### Stage records

```json
[
  {
    "stage": "driver1859",
    "sha256": "90b7611bfe4c131f59f287ed5f2a9ce0a3bf41bcc8f0e4754ba283a1a6e8a859",
    "lines": 1859,
    "compiler_exit": 0
  },
  {
    "stage": "driver1862",
    "sha256": "f0ac41fb137fce6ca8262ddb1bad3c9f4ab8cf7e7017048385e061a2ae0c09d8",
    "lines": 1862,
    "compiler_exit": 0
  },
  {
    "stage": "math5163",
    "sha256": "50293984554f44cf27329f5000b86fffd01a3ef00e1eb181c7067b596e3a68f4",
    "lines": 5163,
    "compiler_exit": 0
  },
  {
    "stage": "math5285",
    "sha256": "dc493a30a8cff1a496426346a70ee648b0acfe43e5dce3a1d064c7c58d890ca6",
    "lines": 5285,
    "compiler_exit": 0,
    "report": "eager-unmarked-callback-observer-current-checked.json",
    "diagnostic": "",
    "limits": {
      "memory.max": "4294967296",
      "memory.high": "4294967296",
      "memory.swap.max": "0"
    }
  },
  {
    "stage": "math5387-raw",
    "sha256": "bd832fbf6888ac84da7c2b5eac03dd3944b6d714653f5a13ea8cc405ae41ffcb",
    "lines": 5387,
    "compiler_exit": 1,
    "report": "eager-recorded-callback-current-checked.json",
    "diagnostic": "/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean:5357:21: error: don't know how to synthesize implicit argument `Typing`\n  @OutcomeResourcesWithOutputs ?m.437 bits inst\u271d\u00b9 (programOutputRoles valid marked) formulas solver caller seed\n    (NativeContinuations.HookResult.complete [] caller memos.query)\ncontext:\nTyping : Type\nbits : Nat\nKey : Type\ninst\u271d\u00b2 : DecidableEq Symbol\ninst\u271d\u00b9 : DecidableEq (EdgeKey Symbol Constraint)\ninst\u271d : DecidableEq Node\nholeKey : Typing \u2192 Nat \u2192 Key\nfits : Key \u2192 Symbol \u2192 Bool\nadmits : Key \u2192 Node \u2192 Bool\nformulas : SourceGuards.Formulas FullSyntax.Formula\nsolver : SourceGuards.Entailment FullSyntax.Formula\ninventory : Inventory\ngraph : Graph Symbol Constraint\ntemplates : List (Template.Pattern Symbol)\nmetadata : Metadata Typing\nuv : Nat\nfragment : Fragment\ncaller : Caller (bits + 2)\nmemos : Memos\nbefore : Cached\ncheckEmpty : Bool\nedgesOf : Node \u2192 List (EdgeValue Symbol Constraint)\nstop : Option (Metadata Typing \u2192 Nat \u2192 Bool)\norder : Metadata Typing \u2192 List Nat \u2192 Option Nat\nrecursiveDepth : Nat\nrecursive :\n  EagerProgramResumeComplete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n    recursiveDepth\nseed : Seed\nceiling : Nat\npacket : Packet formulas solver inventory caller memos metadata before\nallocated : FragmentBound before.core.counter fragment\nbounded : Fits seed.snd caller.checked\nknown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\nselectionMembers :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint),\n    edge \u2208 edgesOf (Value.node entry rows depth free) \u2192 edge \u2208 rows\nselectionLength :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference), (edgesOf (Value.node entry rows depth free)).length \u2264 rows.length\nmass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core \u2264 ceiling\nreserved : eagerReserved bits recursiveDepth seed ceiling\nvalid : Constraint \u2192 Prop\nmarked : Nat \u2192 Prop\nslots :\n  SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal\n    caller.checked.native.machine.heap before.core marked\ncallbackFuel : Nat\nresult : Bool \u00d7 Metadata Typing\nafterCore : EnumerationState.State Symbol Constraint\nrecur : Nat \u2192\n  Metadata Typing \u2192\n    Caller (bits + 2) \u2192\n      Queries \u2192\n        Cached \u2192\n          Option Next \u2192\n            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := \u22ef\nreturned : Packet formulas solver inventory caller memos result.snd (EnumerationExpandableIndex.frame afterCore before)\n_stable : EnumerationDriver.RenderStable before.core afterCore\nframe : EnumerationCompressionFrame.Frame before.core afterCore\n_types : result.snd.types = SourcePruningRecordTypes.updatedTypes metadata uv (Sum.inl fragment)\n_holes : result.snd.openHoles = metadata.openHoles\n_typing : result.snd.typing = metadata.typing\n_currentFits : Fits seed.snd caller.checked\n_currentKnown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\ncallback :\n  \u2200 (extra : Nat),\n    Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment))\n        before.core result afterCore \u2227\n      (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment)\n              before.core).run =\n          [Except.ok (result, afterCore)] \u2227\n        \u2200\n          (recur :\n            Metadata Typing \u2192\n              Caller (bits + 2) \u2192\n                Queries \u2192\n                  Cached \u2192\n                    Option Next \u2192\n                      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))\n          (stop : Option (Metadata Typing \u2192 Nat \u2192 Bool)) (order : Metadata Typing \u2192 List Nat \u2192 Option Nat),\n          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order\n              (callbackFuel + extra) metadata uv fragment caller memos.query before =\n            if result.fst = true then NativeContinuations.HookResult.complete [] caller memos.query\n            else\n              recur result.snd caller memos.query (EnumerationExpandableIndex.frame afterCore before)\n                (SourcePruningEnumerationRestart.decision stop order result.snd\n                  (EnumerationExpandableIndex.frame afterCore before))\nrejected : result.fst = true\nretained : OutcomeResources formulas solver caller seed (NativeContinuations.HookResult.complete [] caller memos.query)\n\u22a2 Type\n/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean:5358:9: error: don't know how to synthesize implicit argument `Reason`\n  @NativeContinuations.HookResult.complete (Output (bits + 2) ?m.437) (Failure (bits + 2) ?m.437) (bits + 2) [] caller\n    memos.query\ncontext:\nTyping : Type\nbits : Nat\nKey : Type\ninst\u271d\u00b2 : DecidableEq Symbol\ninst\u271d\u00b9 : DecidableEq (EdgeKey Symbol Constraint)\ninst\u271d : DecidableEq Node\nholeKey : Typing \u2192 Nat \u2192 Key\nfits : Key \u2192 Symbol \u2192 Bool\nadmits : Key \u2192 Node \u2192 Bool\nformulas : SourceGuards.Formulas FullSyntax.Formula\nsolver : SourceGuards.Entailment FullSyntax.Formula\ninventory : Inventory\ngraph : Graph Symbol Constraint\ntemplates : List (Template.Pattern Symbol)\nmetadata : Metadata Typing\nuv : Nat\nfragment : Fragment\ncaller : Caller (bits + 2)\nmemos : Memos\nbefore : Cached\ncheckEmpty : Bool\nedgesOf : Node \u2192 List (EdgeValue Symbol Constraint)\nstop : Option (Metadata Typing \u2192 Nat \u2192 Bool)\norder : Metadata Typing \u2192 List Nat \u2192 Option Nat\nrecursiveDepth : Nat\nrecursive :\n  EagerProgramResumeComplete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n    recursiveDepth\nseed : Seed\nceiling : Nat\npacket : Packet formulas solver inventory caller memos metadata before\nallocated : FragmentBound before.core.counter fragment\nbounded : Fits seed.snd caller.checked\nknown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\nselectionMembers :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint),\n    edge \u2208 edgesOf (Value.node entry rows depth free) \u2192 edge \u2208 rows\nselectionLength :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference), (edgesOf (Value.node entry rows depth free)).length \u2264 rows.length\nmass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core \u2264 ceiling\nreserved : eagerReserved bits recursiveDepth seed ceiling\nvalid : Constraint \u2192 Prop\nmarked : Nat \u2192 Prop\nslots :\n  SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal\n    caller.checked.native.machine.heap before.core marked\ncallbackFuel : Nat\nresult : Bool \u00d7 Metadata Typing\nafterCore : EnumerationState.State Symbol Constraint\nrecur : Nat \u2192\n  Metadata Typing \u2192\n    Caller (bits + 2) \u2192\n      Queries \u2192\n        Cached \u2192\n          Option Next \u2192\n            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := \u22ef\nreturned : Packet formulas solver inventory caller memos result.snd (EnumerationExpandableIndex.frame afterCore before)\n_stable : EnumerationDriver.RenderStable before.core afterCore\nframe : EnumerationCompressionFrame.Frame before.core afterCore\n_types : result.snd.types = SourcePruningRecordTypes.updatedTypes metadata uv (Sum.inl fragment)\n_holes : result.snd.openHoles = metadata.openHoles\n_typing : result.snd.typing = metadata.typing\n_currentFits : Fits seed.snd caller.checked\n_currentKnown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\ncallback :\n  \u2200 (extra : Nat),\n    Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment))\n        before.core result afterCore \u2227\n      (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment)\n              before.core).run =\n          [Except.ok (result, afterCore)] \u2227\n        \u2200\n          (recur :\n            Metadata Typing \u2192\n              Caller (bits + 2) \u2192\n                Queries \u2192\n                  Cached \u2192\n                    Option Next \u2192\n                      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))\n          (stop : Option (Metadata Typing \u2192 Nat \u2192 Bool)) (order : Metadata Typing \u2192 List Nat \u2192 Option Nat),\n          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order\n              (callbackFuel + extra) metadata uv fragment caller memos.query before =\n            if result.fst = true then NativeContinuations.HookResult.complete [] caller memos.query\n            else\n              recur result.snd caller memos.query (EnumerationExpandableIndex.frame afterCore before)\n                (SourcePruningEnumerationRestart.decision stop order result.snd\n                  (EnumerationExpandableIndex.frame afterCore before))\nrejected : result.fst = true\nretained : OutcomeResources formulas solver caller seed (NativeContinuations.HookResult.complete [] caller memos.query)\n\u22a2 Type 1\n/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean:5358:9: error: don't know how to synthesize implicit argument `Output`\n  @NativeContinuations.HookResult.complete (Output (bits + 2) ?m.437) (Failure (bits + 2) ?m.437) (bits + 2) [] caller\n    memos.query\ncontext:\nTyping : Type\nbits : Nat\nKey : Type\ninst\u271d\u00b2 : DecidableEq Symbol\ninst\u271d\u00b9 : DecidableEq (EdgeKey Symbol Constraint)\ninst\u271d : DecidableEq Node\nholeKey : Typing \u2192 Nat \u2192 Key\nfits : Key \u2192 Symbol \u2192 Bool\nadmits : Key \u2192 Node \u2192 Bool\nformulas : SourceGuards.Formulas FullSyntax.Formula\nsolver : SourceGuards.Entailment FullSyntax.Formula\ninventory : Inventory\ngraph : Graph Symbol Constraint\ntemplates : List (Template.Pattern Symbol)\nmetadata : Metadata Typing\nuv : Nat\nfragment : Fragment\ncaller : Caller (bits + 2)\nmemos : Memos\nbefore : Cached\ncheckEmpty : Bool\nedgesOf : Node \u2192 List (EdgeValue Symbol Constraint)\nstop : Option (Metadata Typing \u2192 Nat \u2192 Bool)\norder : Metadata Typing \u2192 List Nat \u2192 Option Nat\nrecursiveDepth : Nat\nrecursive :\n  EagerProgramResumeComplete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n    recursiveDepth\nseed : Seed\nceiling : Nat\npacket : Packet formulas solver inventory caller memos metadata before\nallocated : FragmentBound before.core.counter fragment\nbounded : Fits seed.snd caller.checked\nknown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\nselectionMembers :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint),\n    edge \u2208 edgesOf (Value.node entry rows depth free) \u2192 edge \u2208 rows\nselectionLength :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference), (edgesOf (Value.node entry rows depth free)).length \u2264 rows.length\nmass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core \u2264 ceiling\nreserved : eagerReserved bits recursiveDepth seed ceiling\nvalid : Constraint \u2192 Prop\nmarked : Nat \u2192 Prop\nslots :\n  SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal\n    caller.checked.native.machine.heap before.core marked\ncallbackFuel : Nat\nresult : Bool \u00d7 Metadata Typing\nafterCore : EnumerationState.State Symbol Constraint\nrecur : Nat \u2192\n  Metadata Typing \u2192\n    Caller (bits + 2) \u2192\n      Queries \u2192\n        Cached \u2192\n          Option Next \u2192\n            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := \u22ef\nreturned : Packet formulas solver inventory caller memos result.snd (EnumerationExpandableIndex.frame afterCore before)\n_stable : EnumerationDriver.RenderStable before.core afterCore\nframe : EnumerationCompressionFrame.Frame before.core afterCore\n_types : result.snd.types = SourcePruningRecordTypes.updatedTypes metadata uv (Sum.inl fragment)\n_holes : result.snd.openHoles = metadata.openHoles\n_typing : result.snd.typing = metadata.typing\n_currentFits : Fits seed.snd caller.checked\n_currentKnown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\ncallback :\n  \u2200 (extra : Nat),\n    Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment))\n        before.core result afterCore \u2227\n      (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment)\n              before.core).run =\n          [Except.ok (result, afterCore)] \u2227\n        \u2200\n          (recur :\n            Metadata Typing \u2192\n              Caller (bits + 2) \u2192\n                Queries \u2192\n                  Cached \u2192\n                    Option Next \u2192\n                      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))\n          (stop : Option (Metadata Typing \u2192 Nat \u2192 Bool)) (order : Metadata Typing \u2192 List Nat \u2192 Option Nat),\n          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order\n              (callbackFuel + extra) metadata uv fragment caller memos.query before =\n            if result.fst = true then NativeContinuations.HookResult.complete [] caller memos.query\n            else\n              recur result.snd caller memos.query (EnumerationExpandableIndex.frame afterCore before)\n                (SourcePruningEnumerationRestart.decision stop order result.snd\n                  (EnumerationExpandableIndex.frame afterCore before))\nrejected : result.fst = true\nretained : OutcomeResources formulas solver caller seed (NativeContinuations.HookResult.complete [] caller memos.query)\n\u22a2 Type 1\n/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean:5358:19: error: don't know how to synthesize implicit argument `\u03b1`\n  @List.nil (Output (bits + 2) ?m.437)\ncontext:\nTyping : Type\nbits : Nat\nKey : Type\ninst\u271d\u00b2 : DecidableEq Symbol\ninst\u271d\u00b9 : DecidableEq (EdgeKey Symbol Constraint)\ninst\u271d : DecidableEq Node\nholeKey : Typing \u2192 Nat \u2192 Key\nfits : Key \u2192 Symbol \u2192 Bool\nadmits : Key \u2192 Node \u2192 Bool\nformulas : SourceGuards.Formulas FullSyntax.Formula\nsolver : SourceGuards.Entailment FullSyntax.Formula\ninventory : Inventory\ngraph : Graph Symbol Constraint\ntemplates : List (Template.Pattern Symbol)\nmetadata : Metadata Typing\nuv : Nat\nfragment : Fragment\ncaller : Caller (bits + 2)\nmemos : Memos\nbefore : Cached\ncheckEmpty : Bool\nedgesOf : Node \u2192 List (EdgeValue Symbol Constraint)\nstop : Option (Metadata Typing \u2192 Nat \u2192 Bool)\norder : Metadata Typing \u2192 List Nat \u2192 Option Nat\nrecursiveDepth : Nat\nrecursive :\n  EagerProgramResumeComplete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n    recursiveDepth\nseed : Seed\nceiling : Nat\npacket : Packet formulas solver inventory caller memos metadata before\nallocated : FragmentBound before.core.counter fragment\nbounded : Fits seed.snd caller.checked\nknown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\nselectionMembers :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint),\n    edge \u2208 edgesOf (Value.node entry rows depth free) \u2192 edge \u2208 rows\nselectionLength :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference), (edgesOf (Value.node entry rows depth free)).length \u2264 rows.length\nmass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core \u2264 ceiling\nreserved : eagerReserved bits recursiveDepth seed ceiling\nvalid : Constraint \u2192 Prop\nmarked : Nat \u2192 Prop\nslots :\n  SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal\n    caller.checked.native.machine.heap before.core marked\ncallbackFuel : Nat\nresult : Bool \u00d7 Metadata Typing\nafterCore : EnumerationState.State Symbol Constraint\nrecur : Nat \u2192\n  Metadata Typing \u2192\n    Caller (bits + 2) \u2192\n      Queries \u2192\n        Cached \u2192\n          Option Next \u2192\n            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := \u22ef\nreturned : Packet formulas solver inventory caller memos result.snd (EnumerationExpandableIndex.frame afterCore before)\n_stable : EnumerationDriver.RenderStable before.core afterCore\nframe : EnumerationCompressionFrame.Frame before.core afterCore\n_types : result.snd.types = SourcePruningRecordTypes.updatedTypes metadata uv (Sum.inl fragment)\n_holes : result.snd.openHoles = metadata.openHoles\n_typing : result.snd.typing = metadata.typing\n_currentFits : Fits seed.snd caller.checked\n_currentKnown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\ncallback :\n  \u2200 (extra : Nat),\n    Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment))\n        before.core result afterCore \u2227\n      (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment)\n              before.core).run =\n          [Except.ok (result, afterCore)] \u2227\n        \u2200\n          (recur :\n            Metadata Typing \u2192\n              Caller (bits + 2) \u2192\n                Queries \u2192\n                  Cached \u2192\n                    Option Next \u2192\n                      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))\n          (stop : Option (Metadata Typing \u2192 Nat \u2192 Bool)) (order : Metadata Typing \u2192 List Nat \u2192 Option Nat),\n          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order\n              (callbackFuel + extra) metadata uv fragment caller memos.query before =\n            if result.fst = true then NativeContinuations.HookResult.complete [] caller memos.query\n            else\n              recur result.snd caller memos.query (EnumerationExpandableIndex.frame afterCore before)\n                (SourcePruningEnumerationRestart.decision stop order result.snd\n                  (EnumerationExpandableIndex.frame afterCore before))\nrejected : result.fst = true\nretained : OutcomeResources formulas solver caller seed (NativeContinuations.HookResult.complete [] caller memos.query)\n\u22a2 Type 1\n/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean:5357:50: error: don't know how to synthesize implicit argument `Typing`\n  @programOutputRoles ?m.437 bits valid marked\ncontext:\nTyping : Type\nbits : Nat\nKey : Type\ninst\u271d\u00b2 : DecidableEq Symbol\ninst\u271d\u00b9 : DecidableEq (EdgeKey Symbol Constraint)\ninst\u271d : DecidableEq Node\nholeKey : Typing \u2192 Nat \u2192 Key\nfits : Key \u2192 Symbol \u2192 Bool\nadmits : Key \u2192 Node \u2192 Bool\nformulas : SourceGuards.Formulas FullSyntax.Formula\nsolver : SourceGuards.Entailment FullSyntax.Formula\ninventory : Inventory\ngraph : Graph Symbol Constraint\ntemplates : List (Template.Pattern Symbol)\nmetadata : Metadata Typing\nuv : Nat\nfragment : Fragment\ncaller : Caller (bits + 2)\nmemos : Memos\nbefore : Cached\ncheckEmpty : Bool\nedgesOf : Node \u2192 List (EdgeValue Symbol Constraint)\nstop : Option (Metadata Typing \u2192 Nat \u2192 Bool)\norder : Metadata Typing \u2192 List Nat \u2192 Option Nat\nrecursiveDepth : Nat\nrecursive :\n  EagerProgramResumeComplete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver\n    recursiveDepth\nseed : Seed\nceiling : Nat\npacket : Packet formulas solver inventory caller memos metadata before\nallocated : FragmentBound before.core.counter fragment\nbounded : Fits seed.snd caller.checked\nknown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\nselectionMembers :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference) (edge : EdgeValue Symbol Constraint),\n    edge \u2208 edgesOf (Value.node entry rows depth free) \u2192 edge \u2208 rows\nselectionLength :\n  \u2200 (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Constraint)) (depth : Nat)\n    (free : List InternedBinderProtocol.Reference), (edgesOf (Value.node entry rows depth free)).length \u2264 rows.length\nmass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core \u2264 ceiling\nreserved : eagerReserved bits recursiveDepth seed ceiling\nvalid : Constraint \u2192 Prop\nmarked : Nat \u2192 Prop\nslots :\n  SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal\n    caller.checked.native.machine.heap before.core marked\ncallbackFuel : Nat\nresult : Bool \u00d7 Metadata Typing\nafterCore : EnumerationState.State Symbol Constraint\nrecur : Nat \u2192\n  Metadata Typing \u2192\n    Caller (bits + 2) \u2192\n      Queries \u2192\n        Cached \u2192\n          Option Next \u2192\n            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) := \u22ef\nreturned : Packet formulas solver inventory caller memos result.snd (EnumerationExpandableIndex.frame afterCore before)\n_stable : EnumerationDriver.RenderStable before.core afterCore\nframe : EnumerationCompressionFrame.Frame before.core afterCore\n_types : result.snd.types = SourcePruningRecordTypes.updatedTypes metadata uv (Sum.inl fragment)\n_holes : result.snd.openHoles = metadata.openHoles\n_typing : result.snd.typing = metadata.typing\n_currentFits : Fits seed.snd caller.checked\n_currentKnown : Heap (fun guard => guard \u2208 seed.fst) caller.checked.native.machine.heap\ncallback :\n  \u2200 (extra : Nat),\n    Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment))\n        before.core result afterCore \u2227\n      (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (Sum.inl fragment)\n              before.core).run =\n          [Except.ok (result, afterCore)] \u2227\n        \u2200\n          (recur :\n            Metadata Typing \u2192\n              Caller (bits + 2) \u2192\n                Queries \u2192\n                  Cached \u2192\n                    Option Next \u2192\n                      NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))\n          (stop : Option (Metadata Typing \u2192 Nat \u2192 Bool)) (order : Metadata Typing \u2192 List Nat \u2192 Option Nat),\n          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order\n              (callbackFuel + extra) metadata uv fragment caller memos.query before =\n            if result.fst = true then NativeContinuations.HookResult.complete [] caller memos.query\n            else\n              recur result.snd caller memos.query (EnumerationExpandableIndex.frame afterCore before)\n                (SourcePruningEnumerationRestart.decision stop order result.snd\n                  (EnumerationExpandableIndex.frame afterCore before))\nrejected : result.fst = true\nretained : OutcomeResources formulas solver caller seed (NativeContinuations.HookResult.complete [] caller memos.query)\n\u22a2 Type\n",
    "limits": {
      "memory.max": "4294967296",
      "memory.high": "4294967296",
      "memory.swap.max": "0"
    }
  },
  {
    "stage": "math5387-typing",
    "sha256": "d1c875d6e71bb9b25c3aa8084fab6c5140841ee8f8c614acf609fcf08c86a2dd",
    "lines": 5387,
    "compiler_exit": 1,
    "report": "eager-recorded-callback-current-typing-checked.json",
    "diagnostic": "/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current-typing.lean:5302:5: error: Variable name `allocated` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _allocated\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n",
    "limits": {
      "memory.max": "4294967296",
      "memory.high": "4294967296",
      "memory.swap.max": "0"
    }
  },
  {
    "stage": "math5387-final",
    "sha256": "82b10ab658fedde650e794b0a57aa306775a18ed7bd1c06a687d4fb7625a8ed9",
    "lines": 5387,
    "compiler_exit": 0
  }
]
```

## Frozen fragments and proposals

These files retain their capture-time labels. The current own/full reports
above determine checked scope. The final six opaque/captured draft files are
NOT PART of this live5387 checkpoint and are checked separately. Other positive
depth headers are UNPROVED proposals. Earlier raw fragments are historical drafts.

### Frozen shared-driver-three-observers-visibility.patch

SHA256 303adfcf797f405c9b90ebba89eced97d500be7f5edc11dbc5be46933507b43d.

```json
{"encoding": "json-string", "text": "--- SharedDriver-original1859\n+++ SharedDriver-callable1862\n@@ -534,7 +534,8 @@\n       split <;> simp_all only [SourcePruningEnumerationSelectedStep.Result.narrowed.injEq] <;> subst_vars <;>\n         simp only [true_and] <;> exact ⟨_, rfl⟩\n \n-private theorem observed_prefix_slots\n+/-- The same actual prefix observation retains the marked Program slots. -/\n+theorem observed_prefix_slots\n     (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)\n     (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))\n     (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))\n@@ -715,7 +716,8 @@\n     framed (fun extra => (callback extra).2.1)\n \n omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in\n-private theorem render_stable_slots\n+/-- A stable read retains the same marked Program slots. -/\n+theorem render_stable_slots\n     (heap : NativeHeap) (before after : Core) (valid : Constraint → Prop) (marked : Nat → Prop)\n     (stable : EnumerationDriver.RenderStable before after)\n     (slots : ProgramSlots valid literal heap before marked) :\n@@ -737,7 +739,8 @@\n     exact ⟨payload, by simpa only [stable.values] using stored, role⟩\n \n omit [DecidableEq Symbol] [DecidableEq Node] in\n-private theorem prepared_marked_fields\n+/-- The same successful preparation retains the marked Program fields and bucket scope. -/\n+theorem prepared_marked_fields\n     (entryFuel nativeFuel uv handle : Nat) (scs : List Suspended)\n     (caller : Caller (bits + 2)) (before entered : Cached) (decoded value : Node) (heap : NativeHeap)\n     (valid : Constraint → Prop) (marked : Nat → Prop)\n"}
```

### Frozen visibility-verification.json

SHA256 63203f529af4c99a8666ef10cdeddf375a9a6b3ed751c9cde037f61595730769.

```text
{
  "status": "runtime-only uncompiled draft",
  "namespace": "MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive",
  "old_sha256": "90b7611bfe4c131f59f287ed5f2a9ce0a3bf41bcc8f0e4754ba283a1a6e8a859",
  "new_sha256": "f0ac41fb137fce6ca8262ddb1bad3c9f4ab8cf7e7017048385e061a2ae0c09d8",
  "old_lines": 1859,
  "new_lines": 1862,
  "inverse_exact": true,
  "old_public_tail_exact": true,
  "operations_or_instances_changed": false,
  "names": [
    "observed_prefix_slots",
    "render_stable_slots",
    "prepared_marked_fields"
  ]
}
```

### Frozen observed_prefix_slots-header.txt

SHA256 8f5844b5b6412f788f726290455d3089244510b46cc530d992df4d7d636936bf.

```text
theorem observed_prefix_slots
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing)
    (receipt : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates
      checkEmpty edgesOf stop order metadata formulas solver inventory fuel uv caller before memos observed)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata fuel fuel fuel fuel fuel fuel uv caller before memos.query = observed) :
    match (generalizing := false) observed with
    | .parked _ (some after) _ =>
        ProgramSlots valid literal caller.checked.native.machine.heap after.core marked
    | .narrowed _ _ reached _ _ (some after) _ _ =>
        ProgramSlots valid literal reached.checked.native.machine.heap after.core marked
    | _ => True := by
```

### Frozen render_stable_slots-header.txt

SHA256 a21b6f9275235d4da850ff4580a23b86382d97e16c21f5ba5da34893ce842eb9.

```text
theorem render_stable_slots
    (heap : NativeHeap) (before after : Core) (valid : Constraint → Prop) (marked : Nat → Prop)
    (stable : EnumerationDriver.RenderStable before after)
    (slots : ProgramSlots valid literal heap before marked) :
    ProgramSlots valid literal heap after marked := by
```

### Frozen prepared_marked_fields-header.txt

SHA256 182aab3cfc21ce21e98f34808508ce6b207dccfbca6c91a88a9749c8ef3b9445.

```text
theorem prepared_marked_fields
    (entryFuel nativeFuel uv handle : Nat) (scs : List Suspended)
    (caller : Caller (bits + 2)) (before entered : Cached) (decoded value : Node) (heap : NativeHeap)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (lookup : lookupNode caller.checked.native.machine.heap handle = some decoded)
    (actual : SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before =
      ([.ok ((uv, handle, scs, decoded), entered.core)], some (.done value heap)))
    (tagged : marked uv) :
    ValueFields valid literal value ∧ EnumerationSemantics.ValidSuspended scs ∧
      SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs := by
```

### Frozen three-observers-visibility-note.md

SHA256 07838a9555afcbcf916e500cd5d71e6e3d443f82de138808e618de550e6d5023.

```text
# Three existing prefix and preparation observers become callable

Status: frozen runtime-only visibility draft. No compiler was run.
Root approved this smaller reuse path on 2026-11-13 05:50 CET.
Namespace remains MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive.

Original SharedDriver1859 SHA
90b7611bfe4c131f59f287ed5f2a9ce0a3bf41bcc8f0e4754ba283a1a6e8a859.
Draft SourceSynthesisProgramRolesSharedDriver.lean1862 SHA
f0ac41fb137fce6ca8262ddb1bad3c9f4ab8cf7e7017048385e061a2ae0c09d8.

Only observed_prefix_slots, render_stable_slots and prepared_marked_fields
lose private. Each receives one STE doc sentence. All exact names, headers,
proof bodies, omit scopes, instances, operations and old public proof bytes
remain unchanged. No helper or producer is added. The exact inverse visibility
transformation restores EVERY original byte. The old public theorem and its
full remaining tail are separately verified byte-identical.

shared-driver-three-observers-visibility.patch:32 lines; SHA
303adfcf797f405c9b90ebba89eced97d500be7f5edc11dbc5be46933507b43d.
visibility-verification.json:16 lines; SHA
63203f529af4c99a8666ef10cdeddf375a9a6b3ed751c9cde037f61595730769.

Exact public header files:
- observed_prefix_slots-header.txt:23 lines; SHA
  8f5844b5b6412f788f726290455d3089244510b46cc530d992df4d7d636936bf.
- render_stable_slots-header.txt:5 lines; SHA
  a21b6f9275235d4da850ff4580a23b86382d97e16c21f5ba5da34893ce842eb9.
- prepared_marked_fields-header.txt:12 lines; SHA
  182aab3cfc21ce21e98f34808508ce6b207dccfbca6c91a88a9749c8ef3b9445.

observed_prefix_slots uses the SAME input Packet/Ready/current slots, actual
PrefixValid and literal common-fuel runPrefix observation. It retains exact
old marks at the parked or narrowed SOME cache and SAME actual native caller.
NONE/failure forms make no invented after-role claim. The existing full
resource/Post/Memos receipt remains available independently and unchanged.
This is one observed operation, not a cast of the whole shallow worker.

render_stable_slots transports exact old marks through an actual RenderStable.
prepared_marked_fields reads the SAME actual selected preparation and returns
ValueFields plus valid and annotation-only suspended tries for a marked slot.
No new field/provider premise, rerun, assignment or model is introduced.
The visibility change does not prove full eager-loop Program role preservation.

The earlier SelectedPrefix216 two-law draft and74-line repeated observer are
retained as UNUSED proposals. They are not needed on this simpler reuse path.
No live source, compiler, Git, docs, evidence, Haskell or board operation.
```

### Frozen unmarked-finalized-callback-header.txt

SHA256 965e1ceee7023ee91b4080953ac913cbf6df9ab4378f0ff774a5b86676b948dc.

```text
private theorem finalized_unmarked_callback_observation
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (unmarked : ¬marked uv)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      original.checked.native.machine.heap before.core marked)
    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (seed : Seed)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
    ∃ (next : Inventory) (final : Memos) (finalizeFuel : Nat) (finalized : Cached)
      (callbackFuel : Nat) (result : Bool × Metadata Typing) (afterCore : EnumerationState.State Symbol Constraint),
      (Post formulas solver next original reached final ∧ final.query = saved ∧
      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        (finalizeFuel + extra) uv fragment middle = some finalized) ∧
      Packet formulas solver next reached final metadata finalized ∧
      FragmentBound finalized.core.counter fragment ∧
      finalized.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound finalized.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
      finalized.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot finalized.core.representatives uv) ∧
      (Packet formulas solver next reached final result.2 (EnumerationExpandableIndex.frame afterCore finalized) ∧
      EnumerationDriver.RenderStable finalized.core afterCore ∧
      EnumerationCompressionFrame.Frame finalized.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          finalized.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) finalized.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment reached final.query finalized =
            if result.1 then .complete [] reached final.query
            else recur result.2 reached final.query (EnumerationExpandableIndex.frame afterCore finalized)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore finalized))) ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap finalized.core marked ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap (EnumerationExpandableIndex.frame afterCore finalized).core marked ∧
      ∀ extra (initialCaller : Caller (bits + 2)) (initialQueries : Queries)
        (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
          NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
        let work := finalizeFuel + callbackFuel + extra
        let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finalized
        let callbackResult : NativeContinuations.HookResult
            (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
          if result.1 then .complete [] reached saved
          else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
            (SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame afterCore finalized))
        (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.finalizeStopped fragment reached saved middle))) =
        match callbackResult with
        | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)

```

### Frozen eager-unmarked-callback-fragment.lean

SHA256 fa03c7a64723c566c630e6d145f117ce155a68f90353149c0f74f0d90836d7e5.

```text
section ActualFinalizedUnmarkedCallback
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem finalized_unmarked_callback_observation
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original reached : Caller (bits + 2)) (metadata : Metadata Typing) (before middle : Cached)
    (uv handle : Nat) (scs : List Suspended) (fragment : Fragment) (saved : Queries)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core) (unmarked : ¬marked uv)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      original.checked.native.machine.heap before.core marked)
    (data : ChildInputs formulas solver original metadata before scs fragment reached saved middle)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol)) (seed : Seed)
    (bounded : Fits seed.2 reached.checked)
    (known : Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap) :
    ∃ (next : Inventory) (final : Memos) (finalizeFuel : Nat) (finalized : Cached)
      (callbackFuel : Nat) (result : Bool × Metadata Typing) (afterCore : EnumerationState.State Symbol Constraint),
      (Post formulas solver next original reached final ∧ final.query = saved ∧
      (∀ extra, SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        (finalizeFuel + extra) uv fragment middle = some finalized) ∧
      Packet formulas solver next reached final metadata finalized ∧
      FragmentBound finalized.core.counter fragment ∧
      finalized.core = {middle.core with values := middle.core.values.set uv (.enumerated fragment), expansionAncestry := []} ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound finalized.core ≤
        SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ∧
      finalized.core.values[uv]? = some (.enumerated fragment) ∧ IsRoot finalized.core.representatives uv) ∧
      (Packet formulas solver next reached final result.2 (EnumerationExpandableIndex.frame afterCore finalized) ∧
      EnumerationDriver.RenderStable finalized.core afterCore ∧
      EnumerationCompressionFrame.Frame finalized.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 reached.checked ∧ Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          finalized.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) finalized.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment reached final.query finalized =
            if result.1 then .complete [] reached final.query
            else recur result.2 reached final.query (EnumerationExpandableIndex.frame afterCore finalized)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore finalized))) ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap finalized.core marked ∧
      SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
        reached.checked.native.machine.heap (EnumerationExpandableIndex.frame afterCore finalized).core marked ∧
      ∀ extra (initialCaller : Caller (bits + 2)) (initialQueries : Queries)
        (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
          NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
        let work := finalizeFuel + callbackFuel + extra
        let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finalized
        let callbackResult : NativeContinuations.HookResult
            (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2) :=
          if result.1 then .complete [] reached saved
          else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
            (SourcePruningEnumerationRestart.decision stop order result.2
              (EnumerationExpandableIndex.frame afterCore finalized))
        (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
        | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.complete fragment reached saved finished))
        | none => SourcePruningEnumerationSharedReceiptContinuation.run
            (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order work metadata uv)
            initialCaller initialQueries (some (.finalizeStopped fragment reached saved middle))) =
        match callbackResult with
        | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
        | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)

    := by
  have inherited : ∀ held, marked held → Avoids before.core.representatives held scs := by
    intro held heldMarked
    exact slots.incoming held heldMarked (.unenumerated (some handle) scs)
      (List.mem_of_getElem? stored)
  have middleSlots := child_inputs_program_slots valid SourceSynthesisLabelProgramBuildRoles.literal marked
    formulas solver original reached metadata before middle scs fragment saved ready.safe slots inherited data
  obtain ⟨next, final, finalizeFuel, finalized, finalReceipt⟩ :=
    finalize_child_inputs_packet formulas solver original reached metadata before middle uv handle scs fragment saved
      ready stored incoming data
  have retained := finalReceipt
  obtain ⟨_post, querySame, finalAt, finalPacket, fragmentBound, core, _mass, _stored, _root⟩ := retained
  let resetCore := {middle.core with expansionAncestry := []}
  have resetSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
      SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore marked :=
    ⟨middleSlots.bounded, middleSlots.roots, middleSlots.incoming, middleSlots.stored⟩
  have written : Success (EnumerationState.setValue uv (.enumerated fragment)) resetCore () finalized.core :=
    (EnumerationDriver.modify_success _ _ _).mpr core
  have finalizedSlots := (SourceSynthesisProgramRolesUnmarkedWrite.setValue_unmarked_program_slots valid
    SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap resetCore finalized.core
    marked resetSlots uv unmarked (.enumerated fragment) (by intro _ _ _ member; cases member) written).2.1
  obtain ⟨callbackFuel, result, afterCore, callback⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
      metadata uv fragment reached final finalized seed finalPacket fragmentBound bounded known
  have callbackFields := callback
  obtain ⟨_callbackPacket, _stable, callbackFrame, _types, _holes, _typing, _fits, _known, callbackAt⟩ := callbackFields
  have callbackSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
    reached.checked.native.machine.heap finalized.core afterCore marked callbackFrame finalizedSlots
  refine ⟨next, final, finalizeFuel, finalized, callbackFuel, result, afterCore,
    finalReceipt, callback, finalizedSlots, callbackSlots, ?_⟩
  intro extra initialCaller initialQueries recur stop order
  have finalizeAt := finalAt (callbackFuel + extra)
  rw [← Nat.add_assoc] at finalizeAt
  have continued := (callbackAt (finalizeFuel + extra)).2.2 recur stop order
  have same : callbackFuel + (finalizeFuel + extra) = finalizeFuel + callbackFuel + extra := by omega
  rw [same, querySame] at continued
  dsimp only
  rw [finalizeAt]
  simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
  rw [continued]
  cases observed : (if result.1 then NativeContinuations.HookResult.complete [] reached saved
      else recur result.2 reached saved (EnumerationExpandableIndex.frame afterCore finalized)
        (SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame afterCore finalized))) <;> rfl

end ActualFinalizedUnmarkedCallback
```

### Frozen unmarked-callback-observer-note.md

SHA256 bc0959490f0562cf4c0bf8be6b1c87facb4a10f4d766fcb231069cde65f75592.

```text
# Same-execution unmarked finalization and recording

Status: frozen uncompiled draft. Root owns strict checking.

## Frozen files

- Basis: checked Root0009 `eager-generic-output-and-zero-roles.lean`, 4820 lines.
- Basis SHA256: `971509effea62c097a86dc1f127f3065e26b5fb81a7ef556637bb1617e1d25a7`.
- Full candidate: `eager-unmarked-callback-observer.lean`, 4941 lines.
- Full SHA256: `f0eae7958853911ca57b795f891b797fcd8e8fbe1ada11a6ebf6e40a887dff7e`.
- Fragment: `eager-unmarked-callback-fragment.lean`, 119 lines.
- Fragment SHA256: `fa03c7a64723c566c630e6d145f117ce155a68f90353149c0f74f0d90836d7e5`.
- Header: `unmarked-finalized-callback-header.txt`, exact approved 70 lines.
- Header SHA256: `965e1ceee7023ee91b4080953ac913cbf6df9ab4378f0ff774a5b86676b948dc`.

## Insertion and dependencies

Prepend one acyclic import: `MicroCFTA.SourceSynthesisProgramRolesUnmarkedWrite`.
That module imports only the already-used ProgramEnumerationRoles module.
Insert the fragment before the final SharedEagerReservation namespace end.
The private section is `ActualFinalizedUnmarkedCallback`.
It uses the existing aliases, Typing/bits and only the EdgeKey equality instance.
Every old basis byte remains unchanged around these two insertions.
All old definitions, proof bodies, public statements and zero proof remain exact.
The new theorem is private; there are zero new public declarations.

## One endpoint throughout

The entry ProgramSlots and actual stored parent derive all-mark bucket Avoids.
Existing child_inputs_program_slots derives the middle slots from SAME ChildInputs.
Ready supplies its current Safe premise.
The proof invokes finalize_child_inputs_packet exactly once.
Its full inventory/Memos/Post/query and actual finalized cache remain together.
Its exact core equation derives the actual write at the ancestry-reset middle core.
Public UnmarkedWrite observes this SAME write and derives finalized slots.
An enumerated payload has no suspended references; it needs no FragmentRoles.
The proof does not call another finalizer producer.

It invokes callback_complete_resources exactly once at SAME finalized cache/Memos.
Public compression_frame_program_slots observes that SAME callback Frame.
The callback slots retain exactly the current marks.
All native and resource result fields in the approved header remain unchanged.
This includes actual callback raw/Success returns and every larger-fuel equation.
The combined finalizer/continueWith equation uses the old additive common fuel.
Its proof is byte-identical to the checked marked observer's final proof block.
It splits the SAME observed callback result into complete/stopped cases.

## Scope

Inputs describe current successful ChildInputs, not an assumed future worker result.
The entry roles concern original.heap and before.core only.
Finalized and callback role predicates are derived outputs.
The unmarked target is outside the current marks; no Type tag is inferred.
The fragment needs no Program FragmentRoles predicate.
Failed and raw-empty child states receive no new role claim.
No positive-depth prefix, preparation, captured or outer-depth proof changes.
The concrete eager outer-role composition remains open.
No finite Type assignment, satisfying model or output-existence claim is added.

## Static validation

Checked exact header inclusion and unchanged old basis bytes.
Checked one finalizer-packet call and one callback producer call.
Checked exact reuse of the old combined-equation proof.
Checked that the new fragment contains no proof holes or extra producer call.
No compiler, live source, Git, board, Haskell or evidence action was performed.
```

### Frozen eager-program-recorded-callback-fragment.lean

SHA256 1f15ef6202131d1a6ce7110e48eca6b31c9c57e8fc63dacea4d924e07d199d37.

```text
section ActualRecordedProgramCallback
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_callback_from_recorded_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome := by
  let recur := fun workFuel => SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith (recur (fuel + extra))
      graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
      (eagerFinal recursiveDepth seed ceiling) outcome
  obtain ⟨returned, _stable, frame, _types, _holes, _typing, _currentFits, _currentKnown, callback⟩ := recorded
  by_cases rejected : result.1 = true
  · have retained : OutcomeResources (Typing := Typing) formulas solver caller seed
        (.complete [] caller memos.query) := by
      refine ⟨caller, inventory, memos, Post.refl packet.context, bounded, known, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller seed
        (.complete [] caller memos.query) := by
      exact ⟨retained, fun _ member => by cases member⟩
    have growth := eagerFinal_ge recursiveDepth seed ceiling
    refine ⟨callbackFuel, .complete [] caller memos.query, ?_,
      resources_outputs_mono growth.1 growth.2 resources⟩
    intro extra
    rw [(callback extra).2.2 (recur (callbackFuel + extra)) stop order, ite_eq_left rejected]
  · have afterSlots := SourceSynthesisProgramRolesCompression.compression_frame_program_slots
      caller.checked.native.machine.heap before.core afterCore marked frame slots
    have massAfter : SourcePruningEnumerationPrefixAdmission.suspendedBound
        (EnumerationExpandableIndex.frame afterCore before).core ≤ ceiling := by
      change SourcePruningEnumerationPrefixAdmission.suspendedBound afterCore ≤ ceiling
      rw [SourcePruningEnumerationPrefixAdmission.suspendedBound_values before.core afterCore frame.values]
      exact mass
    obtain ⟨resumeFuel, outcome, running, resources⟩ := recursive
      inventory caller memos (EnumerationExpandableIndex.frame afterCore before) result.2 seed ceiling
      returned bounded known selectionMembers selectionLength massAfter reserved valid marked afterSlots
    refine ⟨callbackFuel + resumeFuel, outcome, ?_, resources⟩
    intro extra
    have actual := callback (resumeFuel + extra)
    rw [← Nat.add_assoc] at actual
    rw [actual.2.2 (recur (callbackFuel + resumeFuel + extra)) stop order, ite_eq_right rejected]
    have observed := running (callbackFuel + extra)
    have common : resumeFuel + (callbackFuel + extra) = callbackFuel + resumeFuel + extra := by omega
    rw [common] at observed
    exact observed

end ActualRecordedProgramCallback
```

### Frozen recorded-callback-note.md

SHA256 e3037e33d401d384de614a5a38541035475c1e771991174d130a7a1b8a6d74dd.

```text
# Recorded callback role closure

Time: 2026-11-13 05:59 CET. Status: uncompiled candidate.
Basis: checked5163/50293984. All existing source bytes remain exact.
Full source:5265 lines,806155ffde064fdf2e28960ffcee2a01bf73708e6083ec418e2710ec17a12c5d.
Fragment:101 lines,1f15ef6202131d1a6ce7110e48eca6b31c9c57e8fc63dacea4d924e07d199d37.
Exact approved53-line header:c6f12afbb8655e89baef2fb85a5de07c0746b94b39cc2c941add5fa03bcfc2c6.

The input is the entire same computed callback receipt. It contains actual
recordTypes Success/raw observations, its callback equation, Packet, Frame,
metadata fields and unchanged native resources. This helper executes no
callback, native query or finalizer producer. It consumes that receipt once.

The rejection arm keeps the same caller and empty output list. Existing
within-plan growth widens its complete old resources. The other arm derives
ProgramSlots at the same compression frame and the suspended-mass bound from
its same stored values. It invokes the lower concrete Resume once, with the
same caller, full Memos, computed metadata and reached cache. Additive fuel
aligns that stable Resume with every recorded callback observation. Both arms
retain one outcome, every larger-fuel equation and all old OutcomeResources.

Only the header's existing allocated proof is not needed after the callback
has already completed. Its exact name is retained. Root has the possible
unused-variable linter issue and the proposed name-only repair. No premise
has been removed or weakened. The full53-line header is byte-exact.

All seven other positive-depth targets remain unproved headers only. The
map now reuses the three existing common prefix/preparation observers after
their pending visibility check. No arbitrary-output-property outer Resume,
model, output-existence or full Haskell claim is added. No compiler, Git,
repository, Haskell, board or root evidence action ran.
```

### Frozen recorded-callback-typing-repair.json

SHA256 23f9e4e9e7d390dcc11f02cc4c590904b1498ca817c69508ea8b156ff58ef1da.

```text
{
  "status": "UNCOMPILED",
  "base_source": "/tmp/mcfta-eager-resource-cps-check-20261113-0009/eager-recorded-callback-current.lean",
  "base_sha256": "bd832fbf6888ac84da7c2b5eac03dd3944b6d714653f5a13ea8cc405ae41ffcb",
  "source": "/tmp/mcfta-eager-recorded-callback-20261113-0556/eager-program-recorded-callback-combined-typing.lean",
  "sha256": "d1c875d6e71bb9b25c3aa8084fab6c5140841ee8f8c614acf609fcf08c86a2dd",
  "lines": 5387,
  "change": "Add only explicit Typing to true-arm OutcomeResourcesWithOutputs annotation",
  "header53_exact": true,
  "allocated_unchanged": true
}
```

### Frozen recorded-callback-original53.txt

SHA256 c6f12afbb8655e89baef2fb85a5de07c0746b94b39cc2c941add5fa03bcfc2c6.

```text
private theorem eager_program_callback_from_recorded_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
```

### Frozen recorded-callback-underscore53.txt

SHA256 d8292f2f0d25ce080174b5fa39e3c091a4ff484ae374d2aafe93f8d0d8eddcf5.

```text
private theorem eager_program_callback_from_recorded_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (_allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome
```

### Frozen positive-depth-map.md

SHA256 a8d7bc79168aacc23421a6bce2959bbdefd662bda3761a996531be051e875a34.

```text
# Concrete positive-depth eager Program roles

Time: 2026-11-13 05:58 CET. Status: unproved positive-depth plan and private headers only.
Basis: checked5163/50293984554f44cf27329f5000b86fffd01a3ef00e1eb181c7067b596e3a68f4.
The existing EagerProgramResumeComplete37 contract stays exact. Its only extra
entry premise is CURRENT ProgramSlots. The new target has that same contract.
The public resource20 header and all executable workers stay unchanged.

## Closed contracts

The basis has the generic Type and concrete Program subtree WithOutputs chains.
Type positions use the generic chain with the SAME output predicate. The
Program chain derives child and tuple FragmentRoles and retains full old
resources, native endpoints, stopped prefixes and same-fuel equations.
Use outputOK := programOutputRoles valid marked at the outer composition.
Do not ask Packet to produce an arbitrary output predicate.

The marked finalized callback observer is checked5163:4968. It runs one
finalizer and one recordTypes producer. Gamma's unmarked119 observer is the
same attachment without a parent FragmentRoles premise; Root owns its pending
check. Its frozen header is965e1cee in runtime0528.

## One callback receipt, one recursive use

The proposed eager_program_callback_from_recorded_resources header accepts the
ENTIRE actual callback receipt already returned by one callback producer.
It adds current before-callback ProgramSlots, not desired after-callback roles.
CompressionFrame derives the after-callback slots. Its unchanged stores derive
the suspended-mass bound. The true rejection arm emits no outputs. The other
arm invokes the concrete lower-depth EagerProgramResumeComplete ONCE at that
same computed cache, metadata, caller and full Memos. It retains the same
continueWith equation at a common additive fuel. It calls no callback producer.

Marked and unmarked ordinary consumers pass their already-computed observer
receipt to this helper. They do not call callback_complete_resources again.
An opaque successful receipt is already finalized. It calls the callback
producer once, then passes that recorded receipt to this same helper.

## Actual captured alternatives

New captured and captured-row headers retain each old resource result, now
conjoined with per-output roles. Their extra inputs are current ProgramSlots
and marked-target EdgeFields for the ACTUAL current selected rows. The latter
is source data at the reached operand. Preparation derives it below. It is
not a future child-role or capacity supplier.

A captured proof runs ordinary_prefix_packet once. Observe its same own-class
allocation with ClassAllocation.suspendMany_program_slots. Derive all child
bucket Avoids from current slots.incoming and the stored bucket. For a marked
target, derive Program child scope and use the checked Program tuple producer
once. For an unmarked target, use the generic Type tuple producer once. The
actual successful tuple data feeds own_tuple_child_inputs; the marked branch
also assembles parent FragmentRoles from the same count and indexed roles.
Use the checked marked observer or Gamma's unmarked observer, then the recorded
callback helper. Keep the FINALIZED receipt in the captured Fold. Do not use
consumeSelected's unfinalized receipt as a substitute. Rejected and failed
branches keep their exact complete/stopped results and no-output role proofs.

The captured-row induction uses the same captured Core at each sibling. The
full caller/Memos endpoint from the previous row supplies the next sibling.
NativeHeap.keeps_program_slots transports current roles to that endpoint.
The checked append law retains each earlier output's own heap and witness.
Use an explicit non-generalizing local result match, as in checked4736.

## Preparation and opaque dispatch

Reuse the SAME SelectedPreparation.complete_resources_current receipt once
(SelectedPreparationCurrent:30; basis3196-3405). It supplies native Keeps and
entry RenderStable. The existing shallow driver's pure render_stable_slots:718
and prepared_marked_fields:740 already transport slots and derive marked
ValueFields, ValidSuspended and annotation paths from this exact observation.
They are private visibility/reuse cuts, not missing semantic invariants.
Public SelectedProgramChildRetention.prepared_fields:91 gives result=source
and heap unchanged for a marked Program input. No shallow worker cast is used.

Split prepared empty first: its literal opaque receipt is rejected and has no
outputs. In the ordinary branch derive conditional row fields and call the
new captured-row proof. In the remaining nonempty opaque branch the target
must be unmarked: marked ValueFields permits only empty/node, and annotation
paths exclude terminal tries. Use existing RolesOpaque.opaque_complete_resources_program_slots:43
ONCE. It retains exactly the primitive receipt, FinalizationAt and the SAME
Reserved bits seed(scs.length+1) used by basis eager_opaque_resources:3101.
Pad only along the existing eager schedule. No shallow budget is substituted.

## Prefix and depth closure

The actual expansion already computes checkpoint_resources plus the SAME
common-fuel PrefixValid observation (basis3411-3592). Reuse the existing
SharedDriver observed_prefix_slots:537 on that SAME observation. It already
derives roles at the actual parked cache and narrowed caller/cache. Root
verified its2420-module import closure has no Reservation dependency. Beta's
three-export visibility-only draft1862/f0ac41fb exposes observed_prefix_slots,
render_stable_slots and prepared_marked_fields without changing their proofs.
Root reported its strict check PASS at06:03. This replaces the earlier proposed
26-line adapter and its separate missing availability/action proofs.
Then reuse that exact parked cache in the lower concrete Resume IH, or that
exact narrowed caller/cache in preparation. Empty prefix outcomes emit none.
The positive-depth induction uses the checked concrete zero/direct-emission
case on current slots and the new expansion case. It retains one outcome,
all larger-fuel equations and all old OutcomeResources throughout.

The eight headers in positive-role-header-map.json remain UNPROVED targets.
Root approved only the recorded callback helper for implementation in runtime0556.
All other positive-depth proof bodies remain absent. The three existing common
observers need visibility only. They are in SourceSynthesisProgramRolesSharedDriver.lean,
in the SharedPreparedRecursive namespace; they do not transport a whole shallow worker.
No independent after-Packet provider is added: recorded contains the SAME
computed callback receipt. No new model, future role, public child/provider
or execution-fit assumption is proposed. No compiler, repository, Git, Haskell
or root evidence edit ran.
```

### Frozen positive-role-headers.lean.txt

SHA256 02dae6946e49ca9dbdafd1151185a98e138d8cec9db557a5c0efbee5a480a786.

```text
private theorem eager_program_callback_from_recorded_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits recursiveDepth seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (callbackFuel : Nat) (result : Bool × Metadata Typing)
    (afterCore : EnumerationState.State Symbol Constraint)
    (recorded :
      Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame afterCore before) ∧
      EnumerationDriver.RenderStable before.core afterCore ∧
      EnumerationCompressionFrame.Frame before.core afterCore ∧
      result.2.types = SourcePruningRecordTypes.updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      Fits seed.2 caller.checked ∧ Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap ∧
      ∀ extra,
        Success (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra) metadata uv (.inl fragment))
          before.core result afterCore ∧
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates (callbackFuel + extra)
          metadata uv (.inl fragment) before.core) = [.ok (result, afterCore)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next →
            NativeContinuations.HookResult (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)) stop order,
          SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order
            (callbackFuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame afterCore before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame afterCore before))) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursive.continueWith
        (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
          (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty (fuel + extra) (fuel + extra)
            (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
          holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal recursiveDepth seed ceiling) outcome

private theorem eager_program_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
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
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)

private theorem eager_program_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)

private theorem eager_program_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)

private theorem eager_program_prepared_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (ceiling uv handle : Nat) (scs : List Suspended)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (fits : Fits (SourcePruningEnumerationSharedRecursiveReservation.narrowSeed seed).2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (bucketBound : scs.length ≤ ceiling)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ (fuel : Nat) (observed : SourcePruningEnumerationSharedPreparedContinuations.Preparation) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv)
        checkEmpty (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
          (fuel + extra) (fuel + extra) (fuel + extra) uv edgesOf caller before memos.query = (observed, some outcome)) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) (finish uv outcome)

private theorem eager_program_expansion_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (uv : Nat) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : eagerReserved bits (recursiveDepth + 1) seed ceiling)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ fuel outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
          (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
        holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) (recursiveDepth + 1)
        metadata caller memos.query before (some (.expand uv)) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller (eagerFinal (recursiveDepth + 1) seed ceiling) outcome

private theorem eager_program_resume_complete
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) :
    EagerProgramResumeComplete (Typing := Typing) (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth

private theorem runEager_finite_complete_resources_program_slots
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
    (reserved : SourcePruningEnumerationSharedEagerReservation.eagerReserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked) :
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (SourcePruningEnumerationSharedEagerReservation.eagerFinal recursiveFuel seed ceiling) outcome
```

### Frozen eager_program_opaque_resources-header.txt

SHA256 5640bbd45cb8900f06df42e41d026a87033687df023bce64c84e1646a7636e57.

```text
private theorem eager_program_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
```

### Frozen eager-program-opaque-fragment.lean

SHA256 a0de95d0330b68e68f8fba7b7a7c575fc34b68e7b5b3ae725e130d348d5e7eef.

```text
section ActualProgramOpaqueResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_opaque_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat) (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates
      checkEmpty edgesOf stop order formulas solver recursiveDepth)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (seed : Seed) (bound ceiling uv handle : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (available : Available caller.checked.native.machine.heap value) (closed : value.free = [])
    (dispatch : (match (generalizing := false) value with
      | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) | _ => false) = false)
    (fits : Fits seed.2 caller.checked) (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (mass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling) (bucketBound : scs.length ≤ bound)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : fallbackReserved bits bound ceiling (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (unmarked : ¬marked uv) :
    ∃ (fuel : Nat) (receipt : SelectedEdge.Result (bits + 2)) (outcome : Fold),
      (∀ extra, SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra)
        uv scs value caller before memos.query = some receipt) ∧
      (∀ extra, SourcePruningEnumerationSharedReceiptContinuation.run
        (SourcePruningEnumerationSharedPreparedRecursive.continueWith
          (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
            (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
              (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveDepth)
          graph templates stop order (fuel + extra) metadata uv) caller memos.query (some receipt) = outcome) ∧
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
    := by
  have cost : scs.length + 1 ≤ bound + 1 := by omega
  obtain ⟨headFuel, receipt, reached, saved, final, next, headReceipt, headRoles⟩ :=
    SourceSynthesisProgramRolesOpaque.opaque_complete_resources_program_slots seed formulas solver inventory
      caller memos metadata before checkEmpty uv handle scs value packet ready stored incoming available closed
      dispatch fits (reserved.1.prefix cost) known valid marked slots unmarked
  obtain ⟨headRun, headPost, headQuery, _advanced, admitted, _pending, _history,
    headFits, headKnown, shape, _finalization⟩ := headReceipt
  have padding : Le (advance seed (scs.length + 1)).2 (advance seed (bound + 1)).2 ∧
      (advance seed (scs.length + 1)).1 ⊆ (advance seed (bound + 1)).1 :=
    ⟨SourcePruningEnumerationSharedIncomingReservation.advance_count_profile_mono seed cost,
      SourcePruningEnumerationSharedIncomingReservation.advance_count_alphabet_mono seed cost⟩
  have paddedFits := headFits.mono padding.1
  have paddedKnown : Heap (fun guard => guard ∈ (advance seed (bound + 1)).1)
      reached.checked.native.machine.heap := fun key edge resident => padding.2 (headKnown key edge resident)
  subst saved
  rcases shape with completed | stopped | rejected
  · obtain ⟨fragment, after, rfl, afterPacket, _counter, afterMass⟩ := completed
    have actualMass : SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ ceiling + bound := by omega
    have afterSlots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid
        SourceSynthesisLabelProgramBuildRoles.literal reached.checked.native.machine.heap after.core marked := headRoles
    obtain ⟨recordedFuel, result, afterCore, recorded⟩ :=
      SourcePruningEnumerationSharedPreparedRecursive.callback_complete_resources formulas solver next graph templates
        metadata uv fragment reached final after (advance seed (bound + 1)) afterPacket admitted.2.2.1
        paddedFits paddedKnown
    obtain ⟨callbackFuel, continued, callbackRun, resources⟩ :=
      eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates metadata uv
        fragment reached final after checkEmpty edgesOf stop order recursiveDepth recursive
        (advance seed (bound + 1)) (ceiling + bound) afterPacket admitted.2.2.1 paddedFits paddedKnown
        selectionMembers selectionLength actualMass reserved.2 valid marked afterSlots recordedFuel result afterCore recorded
    let folded : Fold := match continued with
      | .complete outputs actual queries =>
          .complete [.complete fragment reached final.query after] outputs actual queries
      | .stopped outputs reason endpoint =>
          .stopped [] outputs (.continuation (.complete fragment reached final.query after) reason endpoint)
    have fullResources := resources_outputs_post headPost resources
    have finished : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (fallbackPlan bound ceiling (fun retained current => eagerFinal recursiveDepth current retained) seed)
        (finish uv folded) := by
      cases continued <;>
        simpa only [folded, finish, SourcePruningEnumerationSharedPreparedRecursive.endpoint,
          OutcomeResourcesWithOutputs, OutcomeResources, fallbackPlan,
          SourcePruningEnumerationSharedPreparedRecursive.emitted] using fullResources
    refine ⟨headFuel + callbackFuel, .complete fragment reached final.query after, folded, ?_, ?_, finished⟩
    · intro extra
      have actual := headRun (callbackFuel + extra)
      rw [← Nat.add_assoc] at actual
      exact actual
    · intro extra
      have actual := callbackRun (headFuel + extra)
      have common : callbackFuel + (headFuel + extra) = headFuel + callbackFuel + extra := by omega
      rw [common] at actual
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run, actual]
      cases continued <;> rfl
  · obtain ⟨after, outer, waiting, rfl, _counter, _mass⟩ := stopped
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    refine ⟨headFuel, .stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after),
      .complete [.stopped [] (.ok (some []), reached, final.query, outer, waiting) (some after)] [] reached final.query,
      headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · simpa only [finish, fallbackPlan] using resources_outputs_mono growth.1 growth.2 resources
  · subst receipt
    have resources : OutcomeResourcesWithOutputs (Typing := Typing) (programOutputRoles valid marked)
        formulas solver caller (advance seed (bound + 1)) (.complete [] reached final.query) := by
      refine ⟨?_, fun _ member => by cases member⟩
      refine ⟨reached, next, final, headPost, paddedFits, paddedKnown, rfl, rfl, ?_⟩
      intro output member
      exact (List.not_mem_nil member).elim
    have growth := eagerFinal_ge recursiveDepth (advance seed (bound + 1)) (ceiling + bound)
    have endpoints : (caller, memos.query) = (reached, final.query) := by
      exact Option.some.inj _advanced
    obtain ⟨callerSame, querySame⟩ := Prod.mk.inj endpoints
    refine ⟨headFuel, .rejected caller memos.query before,
      .complete [.rejected caller memos.query before] [] caller memos.query, headRun, ?_, ?_⟩
    · intro extra
      simp only [SourcePruningEnumerationSharedReceiptContinuation.run,
        SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance]
    · have fullResources := resources_outputs_mono growth.1 growth.2 resources
      simpa only [finish, fallbackPlan, callerSame, querySame] using fullResources

end ActualProgramOpaqueResources
```

### Frozen eager-program-opaque-note.md

SHA256 c32a109fe0ee6d1f93ad76ff9f3cdf7acfafd0aea52361c53ed9a5c2725b94cb.

```text
# Concrete eager unmarked opaque resources

Status: frozen uncompiled draft. Root owns strict checking.

## Frozen files

- Basis: checked Root0009 `eager-recorded-callback-current-typing-underscore.lean`, 5387 lines.
- Basis SHA256: `82b10ab658fedde650e794b0a57aa306775a18ed7bd1c06a687d4fb7625a8ed9`.
- Candidate: `eager-program-opaque.lean`, 5520 lines.
- Candidate SHA256: `e7ae0a49486ef1393ce5d5d7d69ef1db26f0550834764a4aa46000a50cdc1589`.
- Fragment: `eager-program-opaque-fragment.lean`, 132 lines.
- Fragment SHA256: `a0de95d0330b68e68f8fba7b7a7c575fc34b68e7b5b3ae725e130d348d5e7eef`.
- Approved header: `eager_program_opaque_resources-header.txt`, 39 physical lines.
- Header SHA256: `5640bbd45cb8900f06df42e41d026a87033687df023bce64c84e1646a7636e57`.

## Scope and insertion

Insert before the final SharedEagerReservation namespace end.
Private section: ActualProgramOpaqueResources.
Private theorem: eager_program_opaque_resources.
Use existing aliases, Typing/bits/Key and Symbol/EdgeKey/Node equality instances.
No import delta is needed; checked SharedDriver already imports RolesOpaque.
Every original basis byte, proof body and public statement remains unchanged.
There are zero new public declarations.

## Actual opaque producer

Call RolesOpaque.opaque_complete_resources_program_slots exactly once.
Keep its complete original receipt as headReceipt and its role observation separately.
The receipt includes full Post/Memos/query, advance, admission, pending and history.
It also includes actual Fits/Heap, the three result shapes and FinalizationAt.
No old receipt field or finalization witness is replaced by another producer.
The reservation is exactly reserved.1.prefix at cost scs.length+1.
The proof pads that SAME returned profile/alphabet to advance seed (bound+1).
Its mass bound uses the SAME after cache and original bucketBound/mass.
The approved theorem returns the old all-fuel opaque/continuation equations.
It adds the concrete emitted-output property to their full resource outcome.
The approved header does not separately expose the private FinalizationAt witness.

## Complete branch

The SAME completed receipt supplies afterPacket and afterSlots.
Its admission supplies the SAME fragment bound.
Call callback_complete_resources exactly once with SAME final Memos/cache.
Pass that entire recorded tuple to eager_program_callback_from_recorded_resources once.
The helper preserves full actual callback execution and uses the concrete Resume IH.
It derives output roles at each emitted output's own caller/cache.
Post-compose through the SAME headPost; do not align independent Memos by query.
Use the old folded complete/stopped receipt wrappers and additive common fuel.
The resource conversion keeps both the original resource conjunction and output property.

## Stopped and rejected branches

Retain their literal old receipt and NativeContinuations.advance behavior.
Retain current native caller/query endpoints and full headPost/Memos resource witness.
Both branches emit no output; their concrete output property is vacuous.
The rejected endpoint equality comes from SAME actual receiptAdvance.
No role predicate for a failed state is added.
The old eagerFinal padding covers both branches without a callback call.

## Limits

The contract requires current unmarked target, ProgramSlots and old resource inputs.
Its private recursive input is the approved concrete EagerProgramResumeComplete IH.
No arbitrary-predicate Resume, new future role/model/provider gate or Type FragmentRoles.
No marked-empty, preparation, captured-row or outer-depth proof is changed.
This does not close positive-depth enumeration or prove a finite Type assignment.
It does not prove output existence, adequate depth or default runtime completeness.

## Static checks

Checked exact approved header inclusion and unchanged basis bytes.
Checked one opaque producer, one callback producer and one recorded helper call.
Checked no source holes and no import changes.
No compilation, live source, Git, board, Haskell or evidence action was performed.
```

### Frozen eager_program_captured_resources-header.lean.txt

SHA256 d6383b30c5e07119e706be5199bd27cfcc54d526b7423bce10187e192049e03e.

```text
private theorem eager_program_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
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
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome)
```

### Frozen eager-program-captured-fragment.lean

SHA256 7cfbf156e83ee4e40cf1cb02844541a080aa0742edd3e2cc5bb185338c519377.

```text
section ActualProgramCapturedResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private theorem eager_program_captured_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
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
        (fun retained current => eagerReserved bits recursiveDepth current retained) seed)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) seed) (finish uv outcome) := by
  classical
  let literal : String → Symbol := SourceSynthesisLabelProgramBuildRoles.literal
  let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
  let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
  let hook := fun (work : Nat) => SourcePruningEnumerationSharedPreparedRecursive.continueWith
    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild (width := bits + 2)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty work work work work work edgesOf)
      holeKey keyMatches admits graph templates checkEmpty edgesOf stop order work recursiveDepth)
    graph templates stop order work metadata uv
  change ∃ fuel outcome,
    (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
        (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
      (hook (fuel + extra)) (fuel + extra) uv scs edge caller memos.query before = outcome) ∧
    OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
      (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome)
  have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
      current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
  have planGrowth := tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
    limit (bound + own) ceiling continuation growth seed
  have planFits := fits.mono planGrowth.1
  have planKnown : Heap
      (fun guard => guard ∈ (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed).1)
      caller.checked.native.machine.heap := by
    intro key edge found
    exact planGrowth.2 (known key edge found)
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none =>
        let outcome : Fold := .stopped [] [] (.edge (some .unhandled) (caller, memos.query))
        refine ⟨0, outcome, ?_, ?_⟩
        · intro extra
          rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
          simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
            SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]
          rfl
        · constructor
          · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, .inr rfl, ?_⟩
            intro output member
            cases member
          · intro output member
            cases member
    | some projectedFields =>
        rcases projectedFields with ⟨tries, residual⟩
        obtain ⟨_roots, _action, middle, _paths, ownReceipt, middlePacket, middleMass, lower, reducing⟩ :=
          ordinary_prefix_packet formulas solver inventory caller memos metadata before parentEntry rows depth free
            edge scs packet (kept.available _ available) closed selected bounded pending allowed tries residual projected
        obtain ⟨_prepared, middleRun, _raw, middleCore, middleCounter, _middleForest, _middleSafe,
          _middlePaths, _middleRealized, _middleCounts, _middleFlags, _combinedPending, genuine, middleProtects⟩ := ownReceipt
        have ownAvoids : ∀ held, marked held → Avoids before.core.representatives held scs := by
          intro held tagged
          exact slots.incoming held tagged (.unenumerated (some handle) scs) (List.mem_of_getElem? stored)
        have observed := middleRun
        simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
          projected, Option.map_eq_some_iff] at observed
        obtain ⟨allocation, ownRun, endpoints⟩ := observed
        have sameMiddle : allocation.2 = middle := (Prod.mk.inj (List.cons.inj endpoints).1).2
        have ownObserved : SourcePruningEnumerationCachedOwn.suspendMany caller.checked.native.machine.heap tries before =
            some (allocation.1, middle) := by
          rw [← sameMiddle]
          exact ownRun
        obtain ⟨_ownSame, _cacheSame, _ownRaw, _counter, _forest, _safe, middleSlots,
            _oldProtection, _fresh⟩ :=
          SourceSynthesisProgramRolesClassAllocation.suspendMany_program_slots valid literal
            caller.checked.native.machine.heap tries before middle allocation.1 marked packet.safe slots ownObserved
        let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
        have inputAvoids : ∀ held, marked held → ∀ value bucket, (value, bucket) ∈ inputs →
            Avoids middle.core.representatives held bucket := by
          intro held tagged value bucket member
          exact (middleProtects held (slots.bounded held tagged) (slots.roots held tagged)
            (ownAvoids held tagged)).2 value bucket member
        have edgeBounds := (shapes parentEntry rows depth free available).2 edge selected
        have triesBound := edgeBounds.2 tries residual projected
        have inputLength : inputs.length ≤ limit := by
          simpa only [inputs, SourcePruningEnumerationEdgeInputs.children, List.length_map, List.length_zipIdx] using edgeBounds.1
        have inputFacts : ∀ value bucket, (value, bucket) ∈ inputs →
            Available captured value ∧ value.free = [] ∧ MergedOrdinaryHeight.height value ≤ height ∧
              bucket.length ≤ bound + own ∧ (∀ sc ∈ bucket, sc.var < middle.core.counter) ∧ InputsPending middle.core bucket := by
          intro value bucket member
          obtain ⟨_currentAvailable, childClosed, childBounded, childPending⟩ := genuine value bucket member
          have childRank := lower value bucket member
          obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
          cases same
          have inherited := SourcePruningEnumerationCostBounds.descend_length_le indexed.2 scs
          have added := SourcePruningEnumerationCostBounds.descend_length_le indexed.2
            (suspendedVars before.core.counter tries)
          rw [SourcePruningEnumerationCostBounds.suspended_length] at added
          refine ⟨available.children indexed.1 (List.mem_flatMap.mpr
            ⟨edge, selected, List.fst_mem_of_mem_zipIdx indexedMember⟩), childClosed, by omega, ?_, childBounded, childPending⟩
          simp only [List.length_append]
          omega
        have ownMass : SourcePruningEnumerationPrefixAdmission.suspendedBound middle.core ≤ ceiling := by
          rw [middleMass]
          exact mass
        let yes : Nat → List Fragment → Caller (bits + 2) → Queries → Cached → Fold :=
          fun work fragments reached saved after =>
            let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
            let middle := SelectedEdge.finish residual fragment after
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap work uv fragment middle with
            | some finished => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.complete fragment reached saved finished))
            | none => SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
                (some (.finalizeStopped fragment reached saved middle))
        let no : Nat → List Fragment → ChildDispatch.Observation (bits + 2) → Option Cached → Fold :=
          fun work completed observation candidate =>
            SourcePruningEnumerationSharedReceiptContinuation.run (hook work) caller memos.query
              (some (.stopped completed observation candidate))
        have completedConsumer : ∀ fragments reached saved after,
            TupleInputs formulas solver caller metadata middle inputs fragments reached saved after →
            (marked uv → SourceSynthesisProgramEnumerationRoles.FragmentRoles literal marked
              (.node edge.entry.key.symbol fragments)) →
            ∀ current retained, Fits current.2 reached.checked →
              Heap (fun guard => guard ∈ current.1) reached.checked.native.machine.heap →
              SourcePruningEnumerationPrefixAdmission.suspendedBound after.core ≤ retained → admitted retained current →
              ∃ fuel outcome, (∀ extra, yes (fuel + extra) fragments reached saved after = outcome) ∧
                OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached
                  (continuation retained current) (finish uv outcome) := by
          intro fragments reached saved after history parentRoles current retained fitted supported afterMass accepted
          let fragment := Fragments.Fragment.node edge.entry.key.symbol fragments
          let childAfter := SelectedEdge.finish residual fragment after
          have data := own_tuple_child_inputs formulas solver caller metadata before middle edge scs tries residual
            middleCore middleCounter middleProtects fragments reached saved after history
          have dataSlots := child_inputs_program_slots valid literal marked formulas solver caller reached metadata
            before childAfter scs fragment saved packet.safe slots ownAvoids data
          by_cases chosen : marked uv
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                _fragmentRoles, finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_program_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen ⟨data, dataSlots, parentRoles chosen⟩
                graph templates current fitted supported
            obtain ⟨_post, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
          · obtain ⟨next, final, finalFuel, finished, callbackFuel, result, afterCore, finalReceipt, callback,
                finalSlots, _callbackSlots, _coupled⟩ :=
              finalized_unmarked_callback_observation valid marked formulas solver caller reached metadata before childAfter
                uv handle scs fragment saved ready stored incoming chosen slots data graph templates current fitted supported
            obtain ⟨_post, querySame, finalAt, finishedPacket, fragmentBound, _core, finalMass, _stored, _root⟩ := finalReceipt
            have finalMassBound : SourcePruningEnumerationPrefixAdmission.suspendedBound finished.core ≤ retained :=
              Nat.le_trans finalMass afterMass
            obtain ⟨hookFuel, hookOutcome, hookAt, resources⟩ :=
              eager_program_callback_from_recorded_resources holeKey keyMatches admits formulas solver next graph templates
                metadata uv fragment reached final finished checkEmpty edgesOf stop order recursiveDepth recursive current
                retained finishedPacket fragmentBound fitted supported selectionMembers selectionLength finalMassBound accepted
                valid marked finalSlots callbackFuel result afterCore callback
            rw [querySame] at hookAt
            let receipt : SelectedEdge.Result (bits + 2) := .complete fragment reached saved finished
            let outcome : Fold := match (generalizing := false) hookOutcome with
              | .complete outputs finalCaller finalQueries => .complete [receipt] outputs finalCaller finalQueries
              | .stopped outputs reason endpoint => .stopped [] outputs (.continuation receipt reason endpoint)
            refine ⟨finalFuel + hookFuel, outcome, ?_, ?_⟩
            · intro extra
              have finalizeAt := finalAt (hookFuel + extra)
              rw [← Nat.add_assoc] at finalizeAt
              have continued := hookAt (finalFuel + extra)
              have same : hookFuel + (finalFuel + extra) = finalFuel + hookFuel + extra := by omega
              rw [same] at continued
              change (match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
                (finalFuel + hookFuel + extra) uv fragment childAfter with
                | some finished => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.complete fragment reached saved finished))
                | none => SourcePruningEnumerationSharedReceiptContinuation.run
                    (hook (finalFuel + hookFuel + extra)) caller memos.query
                    (some (.finalizeStopped fragment reached saved childAfter))) = outcome
              rw [finalizeAt]
              simp only [SourcePruningEnumerationSharedReceiptContinuation.run]
              have hookStep : hook (finalFuel + hookFuel + extra) fragment reached saved finished = hookOutcome := by
                simpa only [hook] using continued
              rw [hookStep]
              cases hookOutcome <;> rfl
            · cases hookOutcome <;> exact resources
        have tupleComplete : ∃ fuel outcome,
            (∀ extra, SourcePruningEnumerationSharedChildVisitors.visitChildren
              (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
                (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) (fuel + extra) edgesOf)
              (yes (fuel + extra)) (no (fuel + extra)) inputs caller middle memos.query = outcome) ∧
            OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
              (tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation seed) (finish uv outcome) := by
          by_cases chosen : marked uv
          · have edgeFields := fields chosen
            obtain ⟨payload, present, role⟩ := slots.stored uv chosen
            have same : payload = .unenumerated (some handle) scs := Option.some.inj (present.symm.trans stored)
            subst payload
            have bucketScope : EnumerationSemantics.ValidSuspended scs ∧
                SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion scs := by
              cases role with
              | pending _native _bucket _original _found _valueFields validTries annotationPaths =>
                  exact ⟨validTries, annotationPaths⟩
            let programIndex : Nat → Prop := fun index =>
              (edge.entry.key.symbol = literal "app" ∧ (index = 2 ∨ index = 3)) ∨
                (edge.entry.key.symbol = literal "filter" ∧ index = 1)
            have inherited : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie ∧
                ∀ path ∈ EqualityTrie.fromPathTrie sc.trie, ∃ tail, path = 0 :: tail := by
              intro sc member
              refine ⟨bucketScope.1 sc member, ?_⟩
              intro path represented
              obtain ⟨tail, same⟩ := bucketScope.2 sc member path represented
              exact ⟨tail, same.symm⟩
            have inputFields : ∀ index value bucket, inputs[index]? = some (value, bucket) → programIndex index →
                SourceSynthesisHereditaryProgramFields.ValueFields valid literal value ∧
                  EnumerationSemantics.ValidSuspended bucket ∧
                  SourcePruningEnumerationPathTransport.BucketPaths SourceSynthesisGuardRegions.annotationRegion bucket := by
              intro index value bucket selectedInput wanted
              obtain ⟨childFields, _inheritedEmpty, _ownBucket, childScope⟩ :=
                SourceSynthesisProgramChildScope.program_child_scope valid edge edgeFields scs before.core.counter
                  inherited tries residual projected index value bucket selectedInput wanted
              refine ⟨childFields, fun sc member => (childScope sc member).1, ?_⟩
              intro sc member path represented
              obtain ⟨tail, same⟩ := (childScope sc member).2 path represented
              exact ⟨tail, same.symm⟩
            have tupleConsumers : ProgramTupleConsumersWithOutputs (programOutputRoles valid marked) valid literal marked programIndex
                formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                obtain ⟨history, _afterSlots, countSame, childRoles⟩ := history
                have fragmentCount : fragments.length = edge.children.length := by
                  simpa only [inputs, SourcePruningEnumerationEdgeInputs.children,
                    List.length_map, List.length_zipIdx] using countSame
                have assembled := SourceSynthesisProgramParentCallbackRoles.fragment_roles_of_children valid marked edge
                  edgeFields fragments fragmentCount childRoles
                exact completedConsumer fragments reached saved after history (fun _ => assembled)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query _prefixRoles current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_program_child_height_complete_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_program_tuple_complete_of_child_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple valid marked programIndex inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts middleSlots inputAvoids inputFields shapes selectionMembers selectionLength reserved growth tupleConsumers
          · have tupleConsumers : TupleConsumersWithOutputs (programOutputRoles valid marked) formulas solver caller metadata middle inputs uv continuation admitted yes no := by
              constructor
              · intro fragments reached saved after history current retained fitted supported afterMass accepted
                exact completedConsumer fragments reached saved after history (fun impossible => (chosen impossible).elim)
                  current retained fitted supported afterMass accepted
              · intro completed reached saved after outer waiting next final post query current retained fitted supported _accepted
                let receipt : SelectedEdge.Result (bits + 2) := .stopped completed
                  ((.ok (some []), reached, saved, outer, waiting)) (some after)
                let outcome : Fold := .complete [receipt] [] reached saved
                have resources : OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver reached current (finish uv outcome) := by
                  constructor
                  · refine ⟨reached, next, final, Post.refl post.context, fitted, supported, rfl, query.symm, ?_⟩
                    intro output member
                    cases member
                  · intro output member
                    cases member
                have enlarged := growth retained current
                exact ⟨0, outcome, fun _ => rfl, resources_outputs_mono enlarged.1 enlarged.2 resources⟩
            have child := eager_child_height_complete_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver
            have tuple := eager_tuple_complete_of_child_with_outputs (programOutputRoles valid marked)
              (Typing := Typing) (bits := bits) checkEmpty edgesOf captured limit own height formulas solver child limit
            exact tuple inventory caller memos metadata middle seed
              (bound + own) ceiling inputs uv continuation admitted yes no middlePacket fits known kept ownMass inputLength
              inputFacts shapes selectionMembers selectionLength reserved growth tupleConsumers
        obtain ⟨fuel, outcome, running, resources⟩ := tupleComplete
        refine ⟨fuel, outcome, ?_, resources⟩
        intro extra
        rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts, reducing]
        exact running extra
  · let outcome : Fold := .complete [.rejected caller memos.query before] [] caller memos.query
    refine ⟨0, outcome, ?_, ?_⟩
    · intro extra
      rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
      simp only [SourcePruningEnumerationSharedChildVisitors.visitSelected,
        SourcePruningEnumerationCachedOwn.prepare, allowed]
      rfl
    · constructor
      · refine ⟨caller, inventory, memos, Post.refl packet.context, planFits, planKnown, rfl, rfl, ?_⟩
        intro output member
        cases member
      · intro output member
        cases member
end ActualProgramCapturedResources
```

### Frozen captured-note.md

SHA256 b3e7ff3ca4df09f2bd6159ca4c9bfda325e248b18ae99292ca55f7b7f6343c2b.

```text
# One actual captured row with Program output roles

Time: 2026-11-13 06:17 CET. Status: uncompiled.
Basis: checked5387/82b10ab6. The inverse insertion check reproduces that basis exactly.
The exact55-line d6383b30 header has no change. No new input premise is needed.

The proof runs ordinary_prefix_packet once. It observes the same class allocation
to retain current marks. Current stored scs plus ProgramSlots derives all-mark
bucket avoidance. If the target is marked, its same stored SlotRole supplies
valid tries and annotation paths. Conditional current EdgeFields supplies the
indexed Program child fields through program_child_scope.

The marked branch uses the checked Program tuple WithOutputs producer. Its
actual ordered child count and FragmentRoles supply the assembled parent role.
The unmarked branch uses the generic Type tuple WithOutputs producer. Both
branches call one shared completed-tuple consumer on their same TupleInputs.
It chooses one marked or unmarked actual finalization/callback observer. It
passes that entire recorded callback receipt to the checked recorded helper.
It does not call callback_complete_resources, rerun Finalize or read native
nodes independently. All native and full Memos endpoints come from these
same receipts. Additive fuel retains the actual finalized SelectedEdge receipt.

The literal unhandled, arity-rejected, child-stopped and hook-stopped arms keep
their complete old outcomes. Empty output lists satisfy the output predicate.
All old OutcomeResources remain conjoined with per-output extending ProgramSlots.
The only recursion supplier is the private concrete lower-depth Resume IH.
This file adds no scan, preparation, expansion or depth proof body. Those
headers remain unproved. No adequate depth, output existence, model or Haskell
correspondence claim is added. No compiler, Git, repository, Haskell or board
action ran.
```

## Reproduction

Run each own check.py and the compatibility check.py from the repository root
or /tmp under the existing serial4GiB cap. They pin source bytes and check real
public namespaces/axioms. Reproduce historical sources with the printed reverse
diffs and GNU patch --batch --output RESULT INPUT PATCH. Decode JSON-string
payloads first. Check every recorded SHA256. The two source tracks replay independently.

## Later private checks and unproved row-header scope repair

These checks are OUTSIDE the live5387 checkpoint. Private opaque5520 and
combined captured5899 passed strict Lean with the same resource limits. Their
source fragments above reconstruct those separate candidates; no whole outer
role theorem follows. The unproved old captured-rows header placed Slots and
EdgeFields before the forall that binds their actual operands. The proposed
57-line repair moves each current premise under its own actual inputs. It
adds no assumption. The old unproved header is retained. No checked theorem
was changed by this draft correction. The row proof remains unproved here.

```json
[
  {
    "at": "2026-11-13T06:19:39.495445+01:00",
    "source_sha256": "e7ae0a49486ef1393ce5d5d7d69ef1db26f0550834764a4aa46000a50cdc1589",
    "compiler_exit": 0,
    "limits": {
      "memory.max": "4294967296",
      "memory.high": "4294967296",
      "memory.swap.max": "0"
    }
  },
  {
    "at": "2026-11-13T06:20:03.172685+01:00",
    "source_sha256": "9bf99d8a24dfb0f1c39a30a0de9f5783fcb0a281188667ced29440215a68d03e",
    "compiler_exit": 0,
    "limits": {
      "memory.max": "4294967296",
      "memory.high": "4294967296",
      "memory.swap.max": "0"
    }
  }
]
```

### Unproved captured-rows-original-header57.lean.txt

SHA256 3d9080dc98f51c0b7c03216dbbae69b17aabc52776eeed71e00bbf0bf8ee723d.

```text
private theorem eager_program_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked)
    (fields : marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) :
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
```

### Unproved captured-rows-proposed-current-scoped-header57.lean.txt

SHA256 b7e811cba667828146f7292d2f519714fd681588ce1306fb4d4ddc3bc681ed40.

```text
private theorem eager_program_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop) :
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
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) →
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome)
```

## Later ordered-row strict PASS outside live5387

The later6053 candidate with the corrected current-input header passed strict
Lean at06:30:57 CET. This supersedes only the draft status above. It adds one
153-line ordered scan proof on the checked5899 candidate. It uses the SAME
actual reached native Post.keeps for current slots at unchanged captured Core.
It preserves ordered append, stopped prefixes and the full resource packet.
This separate candidate does not change live5387 or add a public outer role law.

```json
{
  "at": "2026-11-13T06:30:57.148487+01:00",
  "source_sha256": "b0db209d6606a0006323da57ba5877ee0dc9377368b2dc313d342d0476c2d450",
  "compiler_exit": 0,
  "limits": {
    "memory.max": "4294967296",
    "memory.high": "4294967296",
    "memory.swap.max": "0"
  }
}
```

Fragment SHA256 a622421f285adddf3a151a212574dfa9fa2543e28a8993e3fca373239187cff9.

```lean
section ActualProgramCapturedRowsResources
variable {Key : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
open SourcePruningEnumerationFiniteReservation (iterate iterate_ge)

private theorem eager_program_captured_rows_resources
    (holeKey : Typing → Nat → Key) (keyMatches : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveDepth : Nat)
    (recursive : EagerProgramResumeComplete (bits := bits) holeKey keyMatches admits graph templates checkEmpty edgesOf
      stop order formulas solver recursiveDepth)
    (captured : InternedConstructorTemplates.State Symbol Constraint) (limit own height : Nat) (count : Nat)
    (valid : Constraint → Prop) (marked : Nat → Prop) :
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
    SourceSynthesisProgramEnumerationRoles.ProgramSlots valid SourceSynthesisLabelProgramBuildRoles.literal
      caller.checked.native.machine.heap before.core marked →
    ∀ (alternatives : List (EdgeValue Symbol Constraint)), alternatives.length ≤ count →
    (∀ edge ∈ alternatives, edge ∈ rows) →
    (marked uv → ∀ edge ∈ alternatives, SourceSynthesisHereditaryProgramFields.EdgeFields valid
      SourceSynthesisLabelProgramBuildRoles.literal edge) →
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
      OutcomeResourcesWithOutputs (programOutputRoles valid marked) formulas solver caller
        (iterate (fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling
          (fun retained current => eagerFinal recursiveDepth current retained) current) seed count) (finish uv outcome) := by
  induction count with
  | zero =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet _ready _stored _incoming fits known _kept _mass _bucketBound parentEntry rows depth free _available _closed _ranked _bounded _pending _slots
        alternatives length _selected _fields _shapes _selectionMembers _selectionLength _reserved
      cases alternatives with
      | cons edge rest => simp only [List.length_cons] at length; omega
      | nil =>
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits, known, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
  | succ count ih =>
      intro inventory caller memos metadata before seed bound ceiling scs uv handle
        packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked bounded pending slots
        alternatives length selected fields shapes selectionMembers selectionLength reserved
      let continuation : Nat → Seed → Seed := fun retained current => eagerFinal recursiveDepth current retained
      let admitted : Nat → Seed → Prop := fun retained current => eagerReserved bits recursiveDepth current retained
      have growth : ∀ retained current, Le current.2 (continuation retained current).2 ∧
          current.1 ⊆ (continuation retained current).1 := fun retained current => eagerFinal_ge recursiveDepth current retained
      let row := fun current => tuplePlan (nodePlan limit own height) limit (bound + own) ceiling continuation current
      have rowGrowth : ∀ current, Le current.2 (row current).2 ∧ current.1 ⊆ (row current).1 := by
        intro current
        exact tuplePlan_ge (nodePlan limit own height) (nodePlan_ge limit own height)
          limit (bound + own) ceiling continuation growth current
      cases alternatives with
      | nil =>
          have enlarged := iterate_ge row rowGrowth seed (count + 1)
          have supported : Heap (fun guard => guard ∈ (iterate row seed (count + 1)).1)
              caller.checked.native.machine.heap := by
            intro key edge found
            exact enlarged.2 (known key edge found)
          refine ⟨0, .complete [] [] caller memos.query, fun _ => rfl, ?_⟩
          constructor
          · exact ⟨caller, inventory, memos, Post.refl packet.context, fits.mono enlarged.1,
              supported, rfl, rfl, fun _ member => by cases member⟩
          · intro output member
            cases member
      | cons edge rest =>
          have firstReserved := reserved 0 (by omega)
          obtain ⟨headFuel, headOutcome, headRunning, headResources⟩ := eager_program_captured_resources
            holeKey keyMatches admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth recursive
            captured limit own height inventory caller memos metadata before seed bound ceiling scs uv handle
            packet ready stored incoming fits known kept mass bucketBound parentEntry rows depth free available closed ranked
            edge (selected edge (by simp)) bounded pending shapes selectionMembers selectionLength firstReserved
            valid marked slots (fun tagged => fields tagged edge (by simp))
          have farther := iterate_ge row rowGrowth (row seed) count
          cases headOutcome with
          | stopped processed outputs current =>
              refine ⟨headFuel, .stopped processed outputs current, ?_, resources_outputs_mono farther.1 farther.2 headResources⟩
              intro extra
              rw [SourcePruningEnumerationSharedBranching.scan, headRunning extra]
          | complete processed outputs reached saved =>
              obtain ⟨next, final, post, query, reachedPacket, reachedFits, reachedKnown, _outputResources⟩ :=
                SourcePruningEnumerationSharedPreparedRecursive.completed_captured_packet formulas solver
                  inventory caller memos metadata before (row seed) outputs reached saved packet headResources.1
              have laterReserved : ∀ index, index < count →
                  tupleReserved (nodePlan limit own height) (nodeReserved bits limit own height)
                    limit (bound + own) ceiling continuation admitted (iterate row (row seed) index) := by
                intro index inside
                exact reserved (index + 1) (by omega)
              have restLength : rest.length ≤ count := by simp only [List.length_cons] at length; omega
              have reachedSlots := SourceSynthesisProgramRolesNativeHeap.keeps_program_slots
                caller.checked.native.machine.heap reached.checked.native.machine.heap before.core marked post.effects.keeps slots
              obtain ⟨tailFuel, tailOutcome, tailRunning, tailResources⟩ := ih next reached final metadata before (row seed)
                bound ceiling scs uv handle reachedPacket ready stored incoming reachedFits reachedKnown
                (kept.trans post.effects.keeps) mass bucketBound parentEntry rows depth free available closed ranked bounded pending reachedSlots
                rest restLength (fun edge member => selected edge (List.mem_cons_of_mem _ member))
                (fun tagged edge member => fields tagged edge (List.mem_cons_of_mem _ member)) shapes
                selectionMembers selectionLength laterReserved
              let result : Fold := match (generalizing := false) tailOutcome with
                | .complete later remaining finalCaller finalQueries =>
                    .complete (processed ++ later) (outputs ++ remaining) finalCaller finalQueries
                | .stopped later remaining current => .stopped (processed ++ later) (outputs ++ remaining) current
              refine ⟨headFuel + tailFuel, result, ?_, ?_⟩
              · intro extra
                have headAt := headRunning (tailFuel + extra)
                have tailAt := tailRunning (headFuel + extra)
                have hs : headFuel + (tailFuel + extra) = headFuel + tailFuel + extra := by omega
                have ts : tailFuel + (headFuel + extra) = headFuel + tailFuel + extra := by omega
                rw [hs] at headAt
                rw [ts, query] at tailAt
                rw [SourcePruningEnumerationSharedBranching.scan, headAt]
                dsimp only
                rw [tailAt]
                cases tailOutcome <;> rfl
              · simpa only [SourcePruningEnumerationFiniteReservation.iterate_succ, row, result] using
                  (resources_outputs_append uv processed outputs tailOutcome post farther.1 farther.2
                    (by simpa only [query, finish, row] using headResources) tailResources)
end ActualProgramCapturedRowsResources
```
