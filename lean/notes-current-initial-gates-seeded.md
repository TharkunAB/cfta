# Current library proof and initial gate and seeded query resources

This checkpoint starts at published 50abb08b. Proof commits are 9468af32
and c36639a1. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of public contracts. First specify the intended behavior.
Then prove correspondence with the current Haskell implementation. Initial
support and resources cannot assume a later successful call or its result.
Documented errors and validation order form part of each contract.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not establish a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverse laws. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, nested Mu and unions, physical stores, and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed collection and supported open WarmHead exposure with exact heaps, literal widths, and stable replay. | Arbitrary open recursion and remaining callers. |
| Comparison, selection, and Merge | Initial counters and causal mass construct modeled workers with histories, heap effects, memo state, and sufficient fuel. | Remaining callers, separate language-law hypotheses, and runtime correspondence. |
| Recursive intersection | Closed resident operands construct a checked native query with language, full Frame, origins, stores, and an initial instruction bound, without a finite input Cap. | General adaptive callers and public correspondence. |
| Operand, Target, Force, and Leaf | Initial selected paths, domains, Frames, and reservations construct complete shared-state returns. | Outer caller composition and runtime correspondence. |
| Mixed edits and class passes | Initial finite tries and selected domains construct edits, a complete tail-first class pass, and its full caller Post. | Earlier source gates, complete Scan, outer recursion, and runtime correspondence. |
| Selected Required | Original false primary certificates construct the full return at a forecast and both fuel bounds computed from the initial trie, literal forest count, and profile. | Compose the new gates with the original source control flow and remaining cap support. |
| Primary and secondary gates | Initial Frame, Fits, and available values construct their own actual class returns, forecasted Fits, full Frame, and stable computed worker results. | Full Scan and outer callers. |
| First-seeded queries | Initial selected PathSupport and pure query reservations construct their own query, reads, full Frame and caller Post, initial Fits, and stable computed worker result. | Connect the false secondary trace and subsequent conjunction memo call in the complete Scan. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver results remain preserved. These Lean
definitions are handwritten. They do not yet establish full correspondence
with compiled Haskell. Read notes-current-required-numeric.md for the
preceding detailed Required contract.

## Initial gate construction

SourceCurrentPrimaryGateResources defines pure heap and fuel schedules.
The input profile bounds the free-occurrence unfolding rank through causal
payload mass. Node work follows the path length and unfolding rank.
Ordinary work fixes the original row count before scanning. Each suffix
uses the preceding return's predicted heap. A false path prefix can allocate
before a later path succeeds. The schedule retains that allocation.

SourceCurrentPrimaryGateNumericReplay.class_complete and
SourceCurrentSecondaryGateResources.class_complete construct their own
actual traces. They retain available original operands, ready heaps,
forecast Fits, and exact replay at every larger gate fuel. They require
neither closed operands nor a finite Cap nor WarmHead support. Their fixed
predicate parameters remain explicit.

SourceCurrentGateGuard proves causal GuardHeap retention along those
actual traces. SourceCurrentGateFrameResources then retains the full
query Frame at the same inventory. Native tables and domain supplies
remain exact. These adapters construct the trace before deriving its
returned Frame. They do not accept a future trace or reached bound.

## First-seeded query construction

SourceCurrentConstrainedCapSeededForecast follows source order. It first
projects the head path, then completes the tail fold, then executes the
native query. The original first path supplies the final seed. Projection
uses the original forest count. The fold performs no Merge call.

The pure SeededReserved predicate supplies Room at predicted query entry
profiles. It refers only to initial paths, forest count, profile, and word
width. It does not inspect a future execution. The common fuel bounds
projection, demanded reads, and native queries. Increasing those three
fuels independently retains the same complete return.

SourceCurrentConstrainedCapSeededProjection permits selected open
WarmHead exposure through anchored PathSupport. It builds the actual
projection graph and reads. It retains Frame, Fits, closed available
projected operands, and global memo effects. Whole-forest closedness and
finite input Caps are not premises. Unselected open siblings remain valid.

SourceCurrentGeneratedQueryFrameResources constructs the next native
query from closed resident projected operands and initial Room. A closed
constrained Mu can be outside every finite Cap. This adapter does not
require such a Cap. It rebases the inventory at the actual entry heap.
Its own trace supplies the language receipt, origins, universal conditional
joint cache laws, Frame, initial instruction bound, and forecast Fits.

SourceCurrentConstrainedCapSeededNumeric.complete composes those actual
calls. Its same return retains the query graph, reads, full Frame, physical
effects, native extension, available closed result, global memo effect,
causal probes, Fits, and nonempty-path Includes. Includes is one-way.
An empty path list returns empty and needs no reservation.

SourceCurrentSeededCallerNumeric.complete additionally retains the full
caller Post at the returned inventory. Both outer result tables, fourth
memo, and Merge remain exact. Its of_receipt helper verifies a completed
receipt. The initial complete endpoint constructs that receipt itself.
Neither endpoint replaces one language law with another.

These resource bounds are logical majorants. They do not establish an
extracted Haskell runtime budget or concrete host capacity. Selected
WarmHead support still excludes arbitrary open recursion. Earlier Required
all-root Caps remain stronger than the live source refusal gate.

## Missing composition

1. Construct initial numeric resources for the current conjunction
   emptiness Decision and Memo.Call. Complete rows expose operands,
   enumerate matching tuples, fold equality, and project class requirements.
   Requirements can allocate constructor nodes. A closed unfolding-history
   bound alone does not bound that work.
2. Compose primary gate, secondary gate, seeded query, conjunction memo,
   and the following original class at their actual returned heaps. Replace
   ClassScanCompletion.Ranges with an initial pure resource schedule.
   The new seeded producer avoids SeededRanges, but the old complete Scan
   still uses it. Derive selected support from the original false secondary
   trace. Then compose Required preparation and the numeric class caller.
3. Complete active and stored outer descent, arbitrary constrained Mu,
   and convergence. ParentWorkerActual.ResidentRanges and
   PartialWorkerRanges still supply reached outer checks. Busy cells do
   not establish completed execution.
4. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank source adapters.
   Exact ranks require original sorted explicit rows. Language equality
   alone does not fix rank order.
5. Prove Haskell lazy demand, memo publication, solver, runtime, IO,
   randomness, and concrete capacity correspondence. Finally compose all
   public construction, transformation, graph-conversion, query,
   generation, and sampling contracts.

Target inclusion, Merge overapproximation, native exact intersection,
class-satisfying preservation, and exact Required filtering remain
separate language laws.

## Validation and Haskell handoff

The pinned Audit passes 2971 jobs and 65537 dependency checks. All ten
final strict production logs are empty. All ten canonical targets pass.
The canonical dependency graph retains one earlier warning in unchanged
InternedFreshOrdinaryClosedCompletion. No new strict warning remains.
Ten groups check all 87 public declarations and ten constructed integrations.
Only propext, Classical.choice, and Quot.sound occur. Eight component
manifests retain 299 entries and 299 hash references.
Read restart-evidence/20261017-initial-scan-resources/checkpoint-validation.json
for final source hashes, complete signatures, axiom reports, constructed
integrations, exact successful attempts, and component manifests.

Preservation checks 15137 starting files, 2960 older non-Audit sources,
239 Haskell files, 206 active-package files, two stashes, three other
worktrees, and 94 frozen module manifests with 728 entries. Audit adds
ten imports. Earlier proofs, counterexamples, repairs, marked drafts,
evidence, and the optimized interned core retain their bytes.

This checkpoint adds no Haskell patch or new behavior defect. FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged and validated in source c0cc8a05. The Chain reproducer returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild checks. Record every later Haskell repair in
FINDINGS with its failure, executable reproducer, affected paths, commit,
checks, and upstream status. The complete library goal stays active.
