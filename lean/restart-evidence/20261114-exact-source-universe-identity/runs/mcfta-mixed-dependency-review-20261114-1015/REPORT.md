# Mixed stored dependencies: an existing history invariant separates the cases

Status: read-only semantic review. Both Lean drafts are UNCOMPILED. No formal credit is claimed for the new declarations.

The existing `EnumerationReferences.PendingReferences`344–345 says every suspended reference avoids the union-find class of every enumerated slot. It excludes a suspended edge whose target has an enumerated payload. This fact is stronger than the selected-root incoming exclusion used by the three checked pure-cycle laws.

StoredDependency in the candidate is a read-only Prop relation. Its two constructors read literal source payloads: an unenumerated suspended bucket, or a hole in an enumerated fragment. The target uses the actual SameClass relation in both cases. The relation neither computes a new result nor substitutes an evaluator for the worker.

The first57-line draft derives three facts from PendingReferences: a dependency edge ending at an enumerated slot starts enumerated; every predecessor on a finite path ending enumerated is enumerated; a pending slot cannot reach an enumerated endpoint. A closed walk containing both payload kinds would contain such a forbidden path. Thus an instantaneous genuinely mixed suspended/fragment cycle cannot exist in a state carrying this invariant.

The108-line v2 retains all original declarations and adds the existing EnumerationOrder.Stratified facts. Expanded fragment edges strictly increase level, and the level function respects forest classes. Every path ending enumerated gains at least its length in level. A positive-length closed path based at an enumerated slot is impossible. Choosing any enumerated point as the base therefore excludes both pure-fragment and mixed cycles. The previously checked selected-clear proper-cycle laws cover the separate pure suspended-cycle obstruction.

## Actual transition map

- `EnumerationReferences.initial_pending`367 and `EnumerationOrder.initial_stratified`25 derive the properties at the SAME initialized root. They are not completion witnesses.
- Compression keeps values and classes: References.pending_read378; NativeLanguage.frame_sameClass100 and satisfies_frame113. This transports a single assignment rather than choosing independent node witnesses.
- The actual native repeated check `Recursion.complete`52–53 and `selected_complete`174 retain PendingReferences and IncomingAvoid. Its clear changes one pending bucket. `Clear.complete`39–40 derives the same properties for the literal write. It cannot introduce a new enumerated payload.
- `SelectedOrdinary.complete_with_history`34 takes the existing pending-history invariant and retains it at its actual checked/narrowed caches57/106. The original action does not silently replace it with a future supplier.
- `NativeReferences.assimilated_allowed`17 and `incoming_written`36 describe actual concatenated pending buckets. `dispatch_allowed`53, `fold_allowed`71 and `prepared_allowed`129 propagate those exact references. `pending_preserved`189–201 combines their effects with old enumerated origins and protected old classes. Its effects premise must come from these operation producers; it must not become a new end-to-end assumption.
- `ChildCompletion.complete_with_fragments`92 retains PendingReferences and supplies PendingFragment/FragmentAvoid93–98. `TraversalCompletion.complete_with_fragments`70 retains it over the reached child list. Their original admission/range/resource inputs remain in scope; this review does not supply a global admission theorem.
- `NativeBranchCompletion.Pending`42–47 covers complete/rejected caches and the explicit empty stopped branch. Its `FragmentHistory`49–55 transports Stratified through actual completed final-root writes, with one frontier increment. `complete_with_history`155 retains these receipt fields under its original entry inputs. Generic References.setValue_pending410 shows the mechanism: the chosen root's incoming exclusion justifies turning it into an enumerated slot. Generic enumerateOut_pending425 composes child traversal, ancestry bookkeeping and that final write.
- `Dependencies.returned_hole_pending`411–443 proves actual generic traversal returns holes at pending representatives. Its result and `FragmentAvoid` support the dependency order; a hole returned from a new fragment cannot already name an old expanded root under those inputs.

These are concrete component producers. The complete original-source run must compose them at every relevant observed branch with its original resources. This packet does not turn PendingReferences, Stratified or any provider-shaped effect into a replacement user gate for finite completion. It also does not claim that the complete current recursive identity worker already has that global producer.

## Meaning and ancestry remain separate

Satisfies142–146 uses ONE assignment for forest aliases, stored pending restrictions, enumerated fragment fill equations and residuals. Fragments.slotSatisfies104–108 makes the fragment equation explicit. PendingWriteLanguage.pending_write16 preserves this same assignment while adding the actual incoming domain and suspended constraints. ParkedLanguage.checkRepeated_true_satisfies68 retains exactly the removed original bucket as a separate conjunct. Those facts do not produce a shared finite assignment by themselves.

RecursionKey retains node identity and normalized trie-path sets but omits target UVars. AncestryExtension.Extends17 preserves old per-slot keys; KeyAncestry18 restricts their trie carrier. These history facts are not a semantic proof that a removed bucket follows from the remaining state. The new separation argument relies on actual reference and level invariants, not on interpreting equal recursion keys as equal finite witnesses.

The exact weak two-slot model and its uncompiled obligations are in FORMAL-COUNTERMODEL-AND-OBLIGATIONS.md. Its before-state has no finite joint assignment; clearing yields a simple joint assignment. It satisfies the intended cache/selection shape and admits Stratified, but fails PendingReferences. This distinction prevents a model-level failure from being reported as a Haskell defect.

## Remaining goal

A finite common completion of the ORIGINAL root still needs a source-derived assignment that satisfies all shared type aliases, required paths, selected native domains and residuals. The new candidate excludes an entire class of mixed obstructions in states with the existing produced histories. Absence of cycles alone does not establish compatibility or existence of a finite joint witness. Pure suspended constraints may contain zero-length/terminal segments that first require the actual union/terminal normalization; the previously checked proper-cycle statement has its exact stated scope.

No compiler, evaluation/runtime job, live source edit, Haskell edit, Git or board action ran. Earlier reports, failed drafts and proof receipts remain unchanged. Source pins below are identities of consulted originals, not whole-body review claims or a reset of historical unions/UNKNOWNs. Several guessed filenames were absent. Broad filename/declaration/context queries returned truncated output; only subsequently inspected named cuts support the stated contracts. No semantic claims use unviewed bodies or copied historical aliases.
