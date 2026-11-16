# Whole real eager raw alias growth

Status: UNCOMPILED. Root owns compilation and publication.

The candidate contains the complete proof draft for the ORIGINAL
`SharedEagerReservation.runEager_real_entry_aliases_at_any_budget` header.
`PUBLIC-HEADER.lean.txt` is byte-exact with the original `c4cb44f2` target.
It retains the original Packet, Fits, Heap, selectors, mass, reservation,
metadata, source, width, work fuel, recursive fuel, and all emitted outputs.

The internal `alias_whole_resume` statement is stronger. It quantifies over
arbitrary actual entry caches and decisions. It uses genuine Nat induction on
`recursiveDepth`, while `workFuel` stays fixed. Its result covers all outputs
in the actual complete or stopped outcome. It does not require the public
resource facts. The public proof retains those original inputs and clears
the unused resource hypotheses before applying the internal theorem.

The concrete proof links are as follows.

- `alias_entry_forward` follows the actual `Entry.enter` action. It composes
  successful `getValue` and representative compression, then the exact
  forest-preserving expansion-ancestry update.
- `alias_opaque_complete` recovers the actual shared child singleton and
  finalization from a completed opaque receipt. It uses the successful child
  alias law and the finalizer law for those same endpoints.
- `alias_continue` invokes the smaller-depth induction hypothesis only in the
  actual false Left callback branch. The callback alias law supplies the
  exact recursive input cache. Pruned and unsupported callbacks emit nothing.
- `alias_prepared_outputs` derives the actual entry success from the first
  projection of the same `SelectedPreparation.run` observation. Its ordinary
  branch selects the actual producing scan row. The checked causal producer
  supplies the SAME callback restart input, output occurrence, and aliases.
  It then invokes the same smaller-depth induction hypothesis. It does not
  transfer aliases from another sibling row.
- `alias_parked_core` reuses only the no-Total actual-operation inversion from
  `SharedParkedRawBucketReceipt`. It derives the literal pure restart receipt
  and proves that its returned core is the checked core. It does not consume
  the stronger resource or ancestry conclusions of that module.
- The outer induction uses `runPrefix_sameClass_forward` at the six original
  supplied work-fuel arguments. Actual parked continuations use their checked
  core. Actual narrowed continuations use the attached candidate cache.

The source-stage split retains missing receipts, empty/rejected actions,
callback pruning, preparation failures, malformed observations, parked
restart, and successful preparation. The preparation helper retains terminal,
opaque, ordinary node, and unsupported value branches. Complete and stopped
folds expose the same retained output lists.

There is no public future Frame, callback, history, model, resource, or alias
supplier. Every internal smaller-depth hypothesis is discharged by the Nat
induction. There is no work-fuel increase or empty-cache substitution.
The candidate does not prove a native model, target typing, assignment
compatibility, or a simultaneous historical completion.

All normal dependencies are pinned in `SOURCE-PINS.sha256`. The source uses
`autoImplicit false` and default proof limits. Its public axiom probe is
appendable and contains no import. No compiler, Source edit, Git command,
board action, or temporary file was used.
