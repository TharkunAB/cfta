# Current library proof and initial conjunction resources

This checkpoint starts at published 2d7b0fa2. Proof commit is 75348c57.
Source main remains c0cc8a05, merged at 896b0a1c.
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
| Primary and secondary gates | Initial Frame, Fits, and available values construct their own actual class returns, forecast Fits, full Frame, and stable computed worker results. | Full Scan and outer callers. |
| First-seeded queries | Initial selected PathSupport and pure query reservations construct their own query, reads, full Frame and caller Post, initial Fits, and stable computed worker result. | Connect the false secondary trace and subsequent conjunction memo call in the complete Scan. |
| Conjunction Decision and Memo | Initial heap guards, admission budget, and profile construct rows, worklist, Decision, and Memo.Call with shared computed worker ceilings and full caller Post. | Forecast guards across native queries and compose the complete Scan. False answers do not prove nonemptiness. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver results remain preserved. These Lean
definitions are handwritten. They do not yet establish full correspondence
with compiled Haskell. Read notes-current-initial-gates-seeded.md for the
preceding detailed gate and seeded query contracts.

## Initial conjunction construction

InternedValueMass does not measure guards or equality path metadata.
Its scalar bound alone cannot bound the number or depth of class paths.
SourceCurrentConjunctionGuardUniverse.guards collects the finite raw guard
list from the actual entry heap. Actual reads and requirement projections
retain that carrier. The proof follows the actual allocation histories.

SourceCurrentConjunctionTupleBounds enumerates finite ordered guard words.
It uses the exact source combination and normalization. The resulting
shape bound bounds class count, paths per class, and path depth. The tuple
bound is the original row width raised to the original operand count.
Duplicate operands remain separate occurrences. No tuple set replaces the
source list or its order.

SourceCurrentConjunctionExposureResources constructs its own closed reads
at the initial forest forecast. ProjectionResources constructs its own
selected projection jobs at the initial depth, forest count, and scalar.
Each job retains effects, available closed results, equal forest length,
forecast Fits, and exact replay at every larger shared pair of fuels.

RequirementResources bounds the literal canonical class schedule.
RequirementNumeric then bounds returned child columns, class requirements,
and each requirement width. Children execute before class requirements.
TupleNumeric combines those bounds with the actual normalized guard shape.
Its own return retains the exact equality cache fold and numeric bounds.

RowsResources first predicts exposure width. It then bounds all matching
tuples with fixed original dimensions. Each returned pending conjunction
fits the final width bound. Its own return retains physical effects, the
finite guard carrier, Fits, and exact shared worker replay.

WorklistResources iterates that row forecast through the original admission
budget. Admission consumes one budget unit and can allocate. Skip and
empty branches retain the physical state. Pending widths grow only within
the predicted scalar. The producer constructs its own actual Run and
computes the projection and reader ceilings from initial data.

SourceCurrentConjunctionNumeric constructs its own Decision and Memo.Call.
The entry heap supplies its own finite guard list. Hits retain the exact
physical state. Misses construct the actual decision. The same return
retains Effects, memo Correct, AnswerSound, Extends, causal GuardHeap,
forecast Fits, and exact replay at all independently larger worker fuels.
It requires no future graph, reached resource callback, worker success,
finite input Cap, or whole-input closedness.

AnswerSound is one-sided. A true answer establishes emptiness. A false
answer does not establish nonemptiness. This remains the Decision contract
when the admission budget is exhausted or the input is open.

SourceCurrentConjunctionCallerNumeric.complete constructs the call in the
full current caller. Its same return retains the full Frame at the same
inventory, complete Post, original numeric forecast Fits, global memo
validity, and causal probes. Both outer result tables and Merge remain
exact. The actual saved fourth memo extends the original memo. Native
cells and domain supplies remain exact. No native query Room is needed
inside this conjunction call.

These bounds are logical majorants. Some pure definitions are
noncomputable. They do not establish an extracted Haskell runtime budget
or concrete host capacity.

## Missing composition

1. Forecast guards across the actual native queries in the full Scan.
   Those queries can synthesize guards. The new conjunction forecast uses
   the guard list at its own entry heap. An earlier scalar alone does not
   bound that list. Construct an initial guard and resource schedule for
   primary gate, secondary gate, seeded query, memo call, and original
   class suffix at their actual returned heaps. Replace reached
   ClassScanCompletion.Ranges and SeededRanges in the complete Scan.
2. Derive selected PathSupport from the actual false secondary trace.
   Compose Required preparation and the numeric class caller with the
   original source control flow. Required all-root caps remain stronger
   than the live source refusal gate. Discharge the remaining cap support.
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

The pinned Audit passes 2983 jobs and 65714 dependency checks. All twelve
final strict production logs are empty. All twelve canonical targets pass.
The dependency graph retains one earlier warning in unchanged
InternedFreshOrdinaryClosedCompletion. No new strict warning remains.
Seventeen groups check all 116 public declarations and fourteen constructed
integrations. Only propext, Classical.choice, and Quot.sound occur.
Nine component manifests retain 305 entries and 305 hash references.
Read restart-evidence/20261017-conjunction-resources/checkpoint-validation.json
for final source hashes, signatures, axiom reports, exact successful
attempts, and component manifests. Read that directory's README for proof
printing, lossless log compression, and auxiliary diagnostic provenance.

Preservation checks 15353 starting files, 2970 older non-Audit sources,
239 Haskell files, 206 active-package files, two stashes, three other
worktrees, and 95 frozen module manifests with 740 entries. Audit adds
twelve imports. Earlier proofs, counterexamples, repairs, marked drafts,
evidence, and the optimized interned core retain their bytes.

This checkpoint adds no Haskell patch or new behavior defect. FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged and validated in unchanged source c0cc8a05. The Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains
opaque-pool evaluation. Record each later Haskell repair in FINDINGS with
its failure, executable reproducer, affected paths, commit, checks, and
upstream status. The complete library goal stays active.
