# Next: current literal class Scan and first-seeded queries

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md,
docs/adr/0004-explicit-graph-boundary.md, and lean/notes-current-conjunction-worker.md.
Source main remains ccebf0f7. The preceding published checkpoint is ebf92715.

## Completed literal dependencies

Current allocated merge, Target, shared Force/Leaf, structural edits, class
passes, and conjunction execution have literal bounded workers. The current
conjunction worker implements rows, the dynamic worklist, decision, and the
fourth memo. AllocatedConjunctionWorkerActual.finite constructs stable
execution and the full caller Post from initial Context and query residency.
True proves emptiness; false proves no acceptance fact. Input inventory and
native cells remain unchanged by this conjunction stage.

## Exact next implementation

1. Implement literal Seeded Operand/Fold/Seeded from
   SourceCurrentAllocatedSeededQuery. A projection retains equality operations
   and native tables. A nonempty path list rotates seed :: rest to
   rest ++ [seed]. Project the head, execute the tail, then run the checked
   native intersection at its actual returned state. Empty input returns
   Empty without work. Do not call the merged Target operand: this query
   projects without mergeAlternatives.
2. Reuse SourceEqualityProjectionWorker.forest and the literal checked
   native execution used by AllocatedTargetWorker.leaf. Keep projection,
   read, and native bounds distinct. Native success alone does not prove
   initial physical safety. Adapt TargetWorkerNative's bridge under the
   actual initial Good, idle, resident closed operands, and reached ranges.
   SeededRanges and FoldRanges describe only actual reached checks.
3. Implement Scan from SourceCurrentConjunctionClassScan. The primary false
   branch selects the class and continues. Primary true runs secondary.
   Secondary true skips the class. Secondary false runs the actual seeded
   query and current conjunction memo. A true memo answer stops before the
   suffix; false continues at its exact returned checked state and fourth
   memo. Preserve original class order, repeated paths, and selected classes.
4. Use the existing literal gate definitions in EndpointStatefulGate and
   SourceCurrentMuEndpoint, with SourceCurrentSecondaryTrace adapters for
   the current secondary policy. Use SourceMemoGate.unconstrained and
   SourceEndpointReachability.reaches. Verify the primary current-source
   adapter before reuse. Do not supply arbitrary Boolean answers or a gate
   completion callback. Retain pending, unresolved, and exhausted unfolding
   outcomes and their exact returned heaps.
5. Derive the SAME successful Scan graph and strict
   SourceCurrentAllocatedScanSourceReads receipt. The old primary receipt
   could query another node. Use SourceCurrentAllocatedPrimaryReads for
   primary node queries, not merely its erasure. Logical global receipts
   remain separate from concrete host global-table execution.
6. Prove stable sufficient bounds from finite current graphs. Prove success
   stability and whole checked/fourth/selected-list uniqueness. Then use
   SourceCurrentConjunctionClassScanCompletion.Ranges and legitimate entry
   facts to construct execution. The range plan supplies no completed query,
   final state invariant, or result language law.
7. Compose full caller Context/Post, actual probe heaps, input availability,
   stopped-class exclusion, and retained class order. Use current independent
   semantic adapters. Do not assume the future native result law or a
   different returned inventory. Preserve both outer result families and
   the warm merge memo.

The current SeededQuery header has historical scope notes. Later contextual
query/Scan modules prove stronger relational language receipts. Inspect those
modules before claiming a missing semantic law or adding another assumption.
The strongest public endpoints still need a literal checked Scan adapter.

## Subsequent work and full objective

Compose local precheck/reduction, required children, and the completed class
pass. Then implement parent construction and the mutual outer two-family
worker. The existing root_exact theorem supplies language preservation only
for a completed source-aligned call. General constrained outer termination,
unequal-length path classes, and repeated-pass convergence remain open.
The public reducePartially performs one pass.

Keep all frontend, exact Sized, generator rank, probability, solver, callback,
codec, concrete-container, identity, machine, and host-runtime obligations.
In particular, all-operand serial conjunction exposure does not prove the
host's skipped reads for an empty tuple prefix. Keep pending publication,
concurrency, global tables, and noConstraint CAF explicit. Preserve the
optimized interned core and all older proofs, counterexamples, repairs,
and marked drafts.

No Haskell change occurs in the conjunction checkpoint. Reuse the strict Nix
and 788-example plus golden validation. Record every later Haskell fix FIRST
in root FINDINGS.md with failure, reproducer, files, commit, checks, and
upstream status. Pull before work. Use one canonical Lake process at a time
and poll its actual handle to terminal. Push verified formalize checkpoints
regularly. No board posts or deployments. Keep the full goal active.
