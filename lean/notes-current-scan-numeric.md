# Current library proof and complete initial Scans

This checkpoint starts at published ba44d54f. Proof commit is d82a0f7e.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of public contracts. First specify the intended behavior.
Then prove correspondence with the current Haskell implementation. Initial
support cannot assume a later successful call or its result. Documented
errors and validation order form part of each contract.

The contracts include distinct accepted terms per node-count size, exact
counts, enumeration order, both rank/unrank inverse laws, transformation
language relations, generation coverage, and sampling laws. Terms,
accepting runs, and generator members have different definitions. Language
equality, inclusion, and representative restriction have different contracts.
Build and theorem totals do not establish a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, explicit row order, size-major enumeration, and both rank/unrank inverse laws. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, nested Mu and unions, physical stores, and causal payload bounds. | Lazy forcing, publication, and Haskell runtime correspondence. |
| Recursive reads | Initial resources construct closed collection and supported open WarmHead exposure with exact heaps and stable replay. | Arbitrary open recursion and remaining callers. |
| Comparison, selection, and Merge | Initial counters and causal mass construct modeled workers with histories, effects, memo state, and sufficient fuel. | Remaining callers, separate language-law hypotheses, and runtime correspondence. |
| Recursive intersection | Closed resident operands construct a checked native query with language, full Frame, origins, stores, and initial instruction bounds, without a finite input Cap. | General adaptive callers and public correspondence. |
| Operand, Target, Force, Leaf, and mixed edits | Initial selected paths, domains, Frames, and reservations construct complete shared-state returns and caller Post. | Outer caller composition and runtime correspondence. |
| Class pass and selected Required | Initial finite tries and supported selections construct complete returns at initial profile and fuel forecasts. | Remaining Required caps and the complete source caller. |
| Gates and first-seeded query | Initial invariants construct exact gate and query returns. False secondary traces derive anchored selected PathSupport. | Arbitrary open recursive inputs outside the stated support. |
| Conjunction Decision and Memo | Initial finite guard carriers and admission budgets construct complete physical returns and full caller Post. | False answers do not establish nonemptiness. |
| Complete Scan | Initial class schedules construct every reached phase, the original class suffix, full Frame, derived ranges, complete caller Post, and stable worker return at five independent fuel bounds. | Compose Required and the outer source recursion at their actual returned states. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier arithmetic, equality, union-find, memo, generation, ranking,
sampling, and restricted-driver results remain preserved. These Lean
definitions are handwritten. They do not yet establish full correspondence
with compiled Haskell.

## New initial Scan construction

An initial scalar cannot bound every later raw guard. Native queries can
create guards. NativeGuardAlphabet therefore adds top and every ordered
source conjunction pair to a finite guard list. NativeGuardCode tracks
literal guards in suspended code. NativeGuardStep retains the physical
heap annotation and advances the control annotation at each actual yielded
instruction. NativeGuardTrace iterates that step over the actual physical
trace. GeneratedQueryGuardResources widens the result to the initial
instruction bound. Its producer constructs its own query receipt and guard
carrier. It does not take a future trace or a finite input Cap as input.

SeededProjectionCarrier retains an arbitrary heap annotation through
supported open projection. It permits an open unselected sibling.
SeededGuardForecast and SeededGuardNumeric follow source order: head
projection, original tail fold, then the actual native query. The returned
tail profile and guard carrier feed that query. The result retains the
existing query receipt, reads, Frame, Fits, Includes, and stable execution.
Includes remains one-way.

SecondarySeededSupport derives anchored PathSupport at the exact heap
returned by an actual false secondary trace. Proper paths are necessary.
A false trace for the empty path does not imply root PathSupport.
SeededInitialRanges constructs the older SeededRanges interface from
initial support, Frame, Fits, valid memos, and pure reservations. Full-state
uniqueness aligns arbitrary graphs in that interface with constructed
projection and query returns.

ScanNumericForecast advances a pair of guard alphabet and numeric profile
through the primary gate, secondary gate, seeded query, conjunction memo,
and original class suffix. It pads branches that omit later phases. It
computes one shared ceiling for the five worker fuels. Each actual fuel
can increase independently.

ScanNumeric.complete constructs its own complete Scan. Its Receipt retains
the actual graph, full Frame, forecast Fits, finite guard carrier, physical
effects, available original forest, correct saved fourth memo, Extends,
and the exact literal worker result. The older ClassScanCompletion.Ranges
interface is an output. Selected, skipped, continued, and stopped branches
use the actual returned heaps. A true memo answer stops before the suffix.
ConjunctionCallUnique aligns the answer, complete physical state, and
complete saved memo for calls with the same inputs.

ScanCallerNumeric.complete obtains the initial guard list from the actual
heap. The same produced Scan constructs strict logical source reads and
the complete caller Post. The Frame and Post use the same returned
inventory. Selected classes preserve original order and repeated
occurrences. A stopped class belongs to the original list and refutes every
accepted original forest. Both outer result tables and Merge remain exact.
The actual saved fourth memo is retained with Extends.

Initial hypotheses remain explicit. They include Frame, Fits, available
values, correct and valid memos, proper paths, and pure initial query
reservations. Stopped-class refutation also requires active nontrivial
classes. No producer takes a future graph, reached ranges, worker success,
output profile, finite input Cap, or whole-forest closedness as input.
The logical source reads are not concrete Haskell host-table events.

AnswerSound remains one-sided. True establishes emptiness. False does not
establish nonemptiness, including when the admission budget is exhausted.
The numeric and fuel bounds are logical majorants. Some pure bounds are
noncomputable. No extracted Haskell budget or host capacity follows.

## Missing work

1. Compose the complete Scan with Required preparation and the numeric
   class caller in the original source control flow. Derive remaining
   Required cap support from legitimate initial data. The new Scan itself
   requires no finite input Cap.
2. Compose outer parent and mutual recursive calls. Prove progress and
   convergence for the intended recursive domain. Preserve the source
   refusal policy. Existing all-root finite caps are stronger than that
   policy and cannot replace it without an explicit scope restriction.
3. Cover arbitrary constrained Mu bodies and the remaining open recursive
   inputs. Existing uncapped closed native operands and supported open
   projections do not establish this whole-domain result.
4. Connect the handwritten Lean workers to the current public Haskell
   adapters and runtime. Account for laziness, forcing, publication order,
   memo events, validation errors, and concrete resource capacity.
5. Compose each public language, counting, enumeration, ranking, generation,
   and sampling contract with those current adapters. Preserve exactness,
   inclusion, and representative restriction as separate specifications.

Read restart-evidence/20261017-scan-guard-resources/README.md and
checkpoint-validation.json for exact checks and evidence boundaries.
Audit passes 2998 jobs and 65859 theorem dependency checks. All fifteen
final strict logs are empty. All fifteen canonical targets pass.
Earlier failed or interrupted attempts retain their source and raw logs.

No Haskell change or new behavior defect is added. FINDINGS keeps the
external repair registry first. Field-pool repair b9219b9e is merged and
validated in unchanged source c0cc8a05. The Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque-pool
evaluation. Record each later Haskell repair with its failure, reproducer,
affected files, commit, checks, and upstream status.
