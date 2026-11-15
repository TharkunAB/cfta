# Actual shared parked step: removed raw bucket

Status: UNCOMPILED candidate. The root agent owns validation.

Public candidate:

`MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive.parked_singleton_removed_bucket_receipt`

The input is the actual configured `SelectedStep.runPrefix` parked singleton
used by the shared prepared worker. The only state invariant supplied is
`UnionFind.Total before.core.representatives`. The theorem does not take a
read, clear, cache repair, restart, earlier entry, model, or future callback
as a premise. It derives the operation receipts from the actual prefix.

The result retains these facts:

- The exact `getValue` singleton and its complete raw bucket.
- The original stored slot at the reached canonical root.
- The original finite UF path from the requested UVar to that root.
- The actual decoded recursive boundary and the actual true check.
- The representative read, compression frame, repeated key, and clear write.
- The same original full bucket at the resolved slot immediately before
  the write replaces it with `[]`.
- The exact cache repair and restart observations.
- Unchanged restart metadata and enumeration Core.
- The exact shared prepared `resume` equation at one less recursive depth.

The proof identifies the two reached roots through UF path uniqueness.
It does not infer a target identity from a trie or a recursion key.

The bucket is never mapped to shapes or deduplicated. Every indexed raw
suspension keeps its trie and variable in the original stored bucket. The
receipt also gives class preservation for every indexed raw target across
the actual compression and clear. It does not identify any such target with
the cleared root. This distinction remains necessary for terminal targets.

The direct restart takes the same native caller and query memo as its input.
The recursive suffix can change those endpoints. No Left callback appears
between this clear and that restart. The receipt does not move an earlier
expansion's Left callback to the cleared slot.

The existing `RecursiveEquations.resume_parked` belongs to the legacy
backend. It was not used as a shared-backend equivalence. The new equation
uses the literal `SharedPreparedRecursive.resume` definition.

The private helper retains more information than the existing private
`SelectedClearCycles.true_check_write`: it keeps the decoded boundary,
actual representative, and seen key, and it needs Total rather than Ready.
It does not duplicate a public origin producer.

The next missing causal case is concrete. An actual shared ordinary row
must connect its earlier `Entry` bucket, own preparation, child operations,
and returned parent tail to this later prefix's canonical slot and complete
bucket. The connection must retain each suspension's raw target and full
path, including duplicate positions. The checked terminal write origin
theorem supplies one child write. This receipt supplies the later clear.
No current theorem supplies the intervening actual source-task history.
The shared worker's pending nonempty tuple and parent-tail induction is the
place to derive that history. A repeated key alone cannot supply it.

The full target remains open: each actual emitted partial root needs ONE
finite accepted completion of the SAME original root under ONE compatible
assignment. That assignment must satisfy retained domains, paths, aliases,
residual guards, and all historically removed obligations. Full emitted
history extraction, later-clear compatibility, parked backward completion,
and finite productivity remain open. This receipt does not claim any of
those results. It covers one observed continuing parked prefix only.

Exact original target:

`lean/restart-evidence/20261114-shared-child-resources-and-atom-steps/runs/mcfta-same-branch-clear-causal-review-20261114-1659/RELATION-TARGET.md`

Original source header:

`lean/restart-evidence/20261114-shared-child-resources-and-atom-steps/runs/mcfta-same-branch-clear-causal-review-20261114-1659/EXISTING-SAME-SOURCE-INITIALIZER-HEADER.lean.txt`

No Haskell defect, fix, diagnostic, or runtime change was established.
No live Lean source, compiler, Git, board, child, or temporary evidence was
changed. All earlier packets remain unchanged.
