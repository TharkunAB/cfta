# Checked edge and Mu profiles with actual event receipts checkpoint

# Checked edge and Mu profiles with actual event receipts checkpoint

Checked at 2026-11-15 19:18 CET. Checked code: `7abce1d893aa8f60a45b2375f27de6497a592f91`.
Prior published checkpoint: `439604901ad0c1cc7fa30b6e6cfbc4e637097d60`.
Source digest: `987d9876632c6db54856cc3bdb851663eab538b09c0006b5b83c812f73e28834`. All 6,094 prior non-Audit sources and headers
remain byte-exact. Main remains `e53852064d3ef5a2eafec47d754c27504b11de5f`
and is an ancestor. No Haskell, Cabal, LiquidHaskell or tests changed.

Five public modules add five statements. All five public gates passed in
session 18684 with exit 0. The Audit checks 97,476 dependencies and reports
379 explicit results: 376 standard and three without axioms. Independent
imports report five standard results. The tree has 6,100 sources and
5,100 direct Audit imports. No visibility export changed.

The new statements prove these results:

- `SamePrefixEdgeChildResult.edge_child_law_at_node_finish` derives the
  actual returned edge cell and its retention to the actual node-parent
  state before its finish. The suffix comes from the SAME fixed trace.
  Both cache laws at that state give the requested edge law. No future
  state, retention, availability, cache model or node-key premise is added.
- `CheckedEdgeBodyProfile.edge_body_children_profile_of_fuel_induction`
  proves Profile for every returned row child. It covers accepted PCS
  children and sentinel paths. It retains the original ordered zip,
  actual query dispatch, original plans and raw smaller child counts.
  A sentinel body has two steps. An accepted body has walkCount+2 steps.
  Final row residency and the complete constructor endpoint are derived.
- `ClosedUniverseMuProfile.closed_universe_mu_profile_trace_result`
  handles an actual selected left/right Mu case at the empty domain.
  It retains full original U/P and the actual ordered entry. The smaller
  M child has the SAME original P height. Its closed Profile result makes
  the actual optional binder return that same complete state and value.
  Local C supplies Profile(P). GLOBAL M still allows arbitrary original
  closed P and must not acquire an only-U(P) premise.
- `NodeQueryDispatchOrigin.actual_node_query_dispatch_from_initial_query_finish`
  recovers the actual preceding captured node query and queryBefore state.
  A checked prefix proves its physical and input facts. Actual lookup and
  demand prove exact captured-request equality. Both the actual dispatch
  and its isolated one-step form reach the SAME beforeBody state. The
  receipt retains raw body, owner, continuation and queryUsed+1+bodyCount
  count equation. It does not run a fresh query at an evaluating state.
- `SourceCurrentNativeOrderedOriginalEntry.ordered_original_entry_common_operands`
  retains the real U/P OR P/U entry event. It proves exact equality of
  the canonical allocation tuple at the SAME current cache. It derives
  full operand availability at entry and the actual common reader,
  unchanged entered heap/operations, canonical domain key, nonempty free
  map, physical growth and original P identity/height uniqueness. Equal
  allocation does not fabricate a canonical U/P Code occurrence.

Private checks 86020, 15817 and 12693 passed. Original batch 46091 and
ordered-entry check 32155 failed and have zero proof credit. The one-line
edge repair reduces Empty's atom list before membership elimination.
The Mu repair unfolds three local definitions. The entry repair unfolds
emptyDomain before rewriting its canonical allocation. Complete public
declarations remain byte-exact. The archive preserves original drafts,
failed checks, exact repairs, frozen headers and reproducible commands.

The general native C/M HISTORY remains OPEN. Its full target is now frozen
in the private `20261115-current-general-cm-history-width-pin-draft` packet.
That target has no supplied body-rule or future-model premise. It retains
the accepted source/build, full stored U, full original P, actual original
entry, original height and both orders, exact initialization and all
original budgets/plans. Its internal invariant must also retain existing
pure, open-body product and cutoff laws. C/M alone is not closed under all
internal B/U descendants. An old writer can precede a later authentic
entry. Do not add entry-to-earlier-producer growth or P availability there.

Next work:

1. Promote the ordered source consumers after public review. Private
   check 19451 passed the ordinary-child qualifier and finite-prefix
   reference control. Their frozen raw packets remain separate from this
   published batch. The ordered mixed-reference result wrapper is next.
2. Prove the original-M union producer with actual member admission under
   the SAME original D and strict height below ORIGINAL P. Preserve B/R,
   both operand orders and both authentic entry orientations.
3. Add the actual preceding EDGE-query dispatch receipt. The new NODE
   receipt supplies authentic query starts for raw node-body lemmas.
   The edge-body consumer needs the corresponding edge-query start.
4. Instantiate the strengthened actual-prefix cache invariant. Discharge
   every semantic node and edge finish case from the actual past laws.
   Every qualified C/M input has a flat key, including literal Empty.
   Only unresolved reference placeholders bypass flat keys; closed inputs
   cannot be those placeholders. R is interned and B is the source node.
5. Extend from one literal initial node query to actual source-worker
   history. Derive source admission, original plans, all 66 resource
   probes and stop states. Preserve prior emissions after a later stop.

The Kernel coupled C/M theorem in
`SourceSynthesisCurrentUniverseGeneratedTypeClosure` is ALREADY PROVED.
Successful finite qualified Kernel intersections preserve availability,
closedness and only-U boundary atoms. Profile permits Empty. It does not
establish inhabitance, historical compatibility or a joint accepted term.

The full goal remains ONE finite accepted completion of the SAME original
emitted partial root under ONE compatible assignment satisfying actual
native domains, retained paths, UF aliases, residuals, readback, parked
backward recompletion and EVERY removed historical obligation on THAT
output branch. Full native Satisfies, typing/depth adequacy and completeness,
both preprocessing/LPO language directions, stream order/multiplicity/lazy
demand, exact node-count classes/counts/weights/training, both rank inverses,
host bounds and compiled Haskell correspondence remain open obligations.
No runtime Haskell bug or fix follows from the proof-only repairs above.
Record any actual Haskell fixes in FINDINGS for external work.

Checkpoint:
`lean/restart-evidence/20261115-native-edge-and-mu-profile-checkpoint/`.
Sources and saved commands reproduce the checks. Compiled objects are
disposable. Cleanup removed 6,265,200 bytes from five terminal private
object directories. Readable /tmp contains 508,815,471 bytes. Five protected
entries, public .lake and unknown work remain untouched. Primary usage is
27%. Pause and notify Matti if it exceeds 80%. Goal ACTIVE. Root owns
compiler, Source, Git, board and cleanup. Active next drafts stay separate.

---



The checked source reproduces the Lean results. The pinned Nix shell and saved
public drivers give the exact commands. Run heavy jobs serially. This batch
uses an 8 GiB memory cap and zero swap. Earlier immutable checkpoints retain
their own exact compiler limits and results.

This archive contains lossless inputs, marked open targets, failed attempts,
repairs, and derived check logs. It contains no compiled objects, symlinks,
or copied import overlays. Historical private paths are not public build
requirements. Recreate private output paths and pins when repeating attempts.

archived-inputs.json maps each input to its original path, bytes and hash.
manifest.json covers every payload. verify.py checks decompressed inputs,
source digest, code patch, document reconstruction, and the manifest.
Use --current-tree only at the pinned source and checkpoint document state.
