Continue the cfta formalization in /home/tritlo/Code/mcfta.

Read NEXT-PROMPT.md, HANDOFF.md, root FINDINGS.md, CONTEXT.md, and docs/adr/0004-explicit-graph-boundary.md. Then read lean/notes-sized-finite-keys.md and the note for the next proof target. HANDOFF.md records the current proof map, commands, preservation hashes, and remaining obligations. Older next-target statements may be stale.

## Main refresh with derived refinement APIs

Current source main: `6fe34ab815d41bd282e46903afc693e9671bd2d3`.
Preserving merge: `9f8d3afc`. Pre-merge proof checkpoint: `7c5f4367`.
Backup: `backup/formalize-before-main-6fe34ab8-20261015-1559`.
Continue on `formalize` and push verified checkpoints. Read
`lean/notes-main-6fe34ab8.md`, then `lean/notes-native-field-running-invariants.md`.
After each pull, check origin/main ancestry before proof edits. Merge newer
main commits with a backup and preservation check; retain the formalize history.
The branch pull fetched a new main while formalize remained current with
its own tracking branch. The closing ancestry check detected the pending
main update. The merge retained both changelog entries in its only conflict.
The optimized interned core, equality repair, Sized, and all earlier proofs
remain. No proof history was rewritten. The new upstream APIs expand the
uncovered source surface; full library scope remains open.

The upstream delta adds Data.CFTA.Refinement.Symbolic and
Data.CFTA.Gen.Refinement.Derive. Generic now exposes Description constructors.
Existing implementation bodies are unchanged within this delta. Compared
with new main, the package tree retains only the earlier Equality/Operations
traversal repair and its changelog entry. New source bridges include value/
formula class agreement, partial measure reads, metadata/codec coherence,
placeholder totality, annotation validation/order, SCC/depth unfolding,
atomic-conjunct movement, recipe/rank correspondence, and named measures.
The existing Generic and combinator proofs do not prove these new APIs.

`lean/repro/DerivedAnnotationBoundaries.hs` verifies two source limits with
public APIs. Equal annotationFormulas projections omit named measures and
produce filtered cardinalities two versus one. A documented Strict{}
invariant on a constructor with !Integer throws the placeholder field-read
error. These source behaviors remain unchanged. The initial package-name
probe selected a hidden package; the corrected exact-unit invocation verifies
both limits. Final log: `/tmp/mcfta-derived-boundaries-final-20261015.log`.

Current proofs derive actual running-cell survival, exact started-request
identity, native step validity, and dynamic normalized-field closure.
FieldsThrough follows from initial normalized physical fields, compiled
continuations, StateValid, and native-only InputsThrough. Native physical
inputs, word bounds, and semantic finish receipts remain explicit. Structural
running-cell survival does not supply the semantic receipt. Normalized fields
do not prove sidecar storage coverage. Open finite-context branch laws and
closed specialization are proved. The old NodeMeaning is vacuous on repeated
branches. General Mu correctness needs a candidate-parametric context law;
the finite seen-pair context fixes the very language that binder candidates
must vary. The actual least-language equation and scoped transport are proved.

Next derive native InputsThrough from original physical inputs and actual
compiled continuations. Combine request identity and running-cell survival
with semantic finish receipts and internal ranges. Establish candidate-
parametric Mu/repeated-pair context extension and sidecar allocation coverage.
Then derive general reached-child checks, class folds, reconstruction, both
gate memo families, guarded passes, recursive reduction, and original graph
construction. Global causal prehistory, pending equality thunks, cache/hash/
IntMap and signed adequacy, lifetime capacity, unsafe IO, GHC, general
completion, repeated fixed points, getAllAtPath, decision-model, new derived
frontend and named-measure bridges, parser/decoder bridges, and extraction
remain open. Keep older constructor/equality work. Sized exact classes,
finite execution, canonical sequence, distinct size order, and both signed
inverse implications remain separate contracts.

Strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 696 examples plus the golden suite. Fourmolu checks the
five changed source/test files and formats the standalone repro. Cabal-gild
and cabal check pass all four packages. Existing linker warnings and the
cabal-gild --input deprecation remain observations. The Lean audit passes
1,975 jobs and 50,686 dependency checks with only permitted axioms. The older
unused-input warning remains. The ten new Lean modules have no warnings.
Logs use `/tmp/mcfta-main-6fe34ab8-{build,tests,format-metadata,lean-audit}-20261015.log`.
The prior separate 205-rank example was not repeated; the new derived tests
check their source examples and ranks. These are component checks only.

Turn start: `/tmp/mcfta-native-validity-start-20261015-1539/` (2,613 files).
Pre-merge snapshot: `/tmp/mcfta-native-validity-checkpoint-20261015-1555/`
(2,624 files). Final snapshot: `/tmp/mcfta-main-6fe34ab8-checkpoint-20261015-1605/`
(2,629 files). All prior Lean definitions except additive Audit imports,
old repros, marked drafts, stashes, and other worktrees retain their hashes.
All three external intersection draft/limit files and the two superseded
scoped-receipt drafts remain. New main is an ancestor of the final branch.
Weekly allowance was 91% at 2026-10-15 16:03 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments.
Older source heads, validation counts, and next targets below are historical.

## Running-cell preservation and derived normalized fields

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Running cells and validity: `7ab3b4f7`. Field closure: `ad4f21de`.
Exact request identity: `4fa1fcfa`. Open laws and Audit: `b03d0d1f`.
Pull returned Already up to date. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-native-field-running-invariants.md`, then the
accepted-child, checked-provenance, native-demand, and allocation notes.
This supersedes the running-cell and field targets below. Full scope is open.
Fetched origin/main is now `6fe34ab8`. Preserve this proof checkpoint, then
review and merge its additive refinement frontend changes. The source base
for the proofs in this section remains `1eb4ab05` until that refresh.

NodeReadback derives actual direct, ready, and started calls with exact full
states and trace lengths. Running proves that actual completed clean source
bodies retain every enclosing running cell and both memo structures. It
includes actual checked edge-prefix effects. The original node/edge cell
survives to its own finish frame. No old completed-run transfer, semantic
receipt, or future validity is assumed. RequestExact derives literal actual
request equality from current checked validity, Ready, and explicit key bounds.

Validity derives checked native validity and physical/domain growth for all
actual step outcomes. StateValid also retains the full ready physical heap
and valid operation caches. Finite reached current checks compose all these
invariants and histories. Native Inputs checks current physical operands,
request Ready/KeySafe, and the actual evaluating cell plus semantic receipt
at each finish. These semantic finish receipts remain explicit obligations.

FieldHeap connects resident edge keys to normalized stored fields. Actual
optional-binder reconstruction retains this invariant through nested stored
substitution and both probes. CodeFields covers every compileNode branch,
ordered walks, and appended continuations. FieldClosure derives actual ready
prefix annotations from conjunction and preserves current field facts.
FieldExecution derives the old FieldsThrough plan from the initial normalized
heap, compiled annotation facts, StateValid, and native-only InputsThrough.
The native physical-input, word-bound, and semantic finish checks still need
derivation for general recursive code. Normalized fields do not establish
sidecar storage coverage. Missing-field blocking remains a distinct outcome.

OpenMeaning provides finite physical bound-name and seen-pair contexts,
local empty/self/swap/reset/repeated laws, environment transport, compatible
environments for closed physical bound readbacks, and exact closed/empty
specialization. It does not replace completed-cell NodeMeaning. The old law
is proved vacuous at every selected repeated branch. An exact checked
one-step reference-pair example disproves unrestricted ambient intersection.
The example does not prove every chosen state/domain is source-reachable.
General Mu correctness needs a stronger candidate-parametric domain law:
a finite seen-pair context fixes a pair language, while the least-language
binder equation must hold for every candidate. The actual binder equation
and scope transport are proved. That recursive extension law is open.

Next derive native InputsThrough from original inputs and actual compiled
continuations. Use exact request identity and proved running-cell survival
to derive semantic finish receipts. Retain internal word ranges. Establish
the candidate-parametric Mu/repeated-pair law and sidecar allocation coverage.
Then derive general reached-child checks and connect class folds,
reconstruction, both gate memo families, guarded passes, recursive reduction,
and original construction. Global causal prehistory, pending equality thunks,
cache/hash/IntMap and signed adequacy, lifetime capacity, unsafe IO, GHC,
general completion, repeated fixed points, getAllAtPath, decision-model,
named measures, parser/decoder bridges, and extraction remain open. Keep the
optimized interned core and older constructor/equality work. Sized exact
classes, finite execution, sequence, distinct size order, and both signed
inverse implications remain separate contracts.

The pinned audit passes 1,975 jobs and 50,686 theorem dependency checks using
only propext, Classical.choice, and Quot.sound. Focused endpoints pass 1,074
jobs. Logs: `/tmp/mcfta-native-field-running-audit-20261015.log` and
`/tmp/mcfta-native-field-running-focused-20261015.log`. The old unused-input
warning remains. The ten new modules have no warnings. No Haskell file changed.
Prior Nix, six-suite, format, metadata, and 205-rank checks were not repeated.
Starting snapshot: `/tmp/mcfta-native-validity-start-20261015-1539/` (2,613 files).
Closing snapshot: `/tmp/mcfta-native-validity-checkpoint-20261015-1555/` (2,624 files).
All earlier proofs except Audit imports, repros, marked drafts, stashes,
other worktrees, and Haskell sources retain their hashes. External unverified
intersection drafts, limit report, and superseded scoped-receipt drafts remain.
Weekly allowance was 92% at 2026-10-15 15:54 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments.
Older counts and next targets below are historical.

## Accepted native child execution and scoped receipts

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Trace proof: `c3896b48`. Accepted receipt proof: `ff2d49be`.
Fresh node and accepted self-child proof: `970ef848`.
Pull returned Already up to date. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-native-accepted-child-demand.md`, then the
checked-provenance, native-demand, checked-edge, payload, and memo notes.
This supersedes the accepted-child target below. Full library scope is open.

NativeDemandContinuation retains actual appended code through every control,
source error, constraint error, and blocked observation. Trace and TraceSplit
derive exact finite child/continuation traces and their shared full state.
WalkExecution derives ordered child runs from actual completed execution,
without a supplied child result or trace plan. Trace lengths remain exact.

AcceptedLanguage derives literal combined-constraint readback from actual
field loads and ready-prefix execution. Ordered child languages combine with
matching source symbols, equal arity, and actual PCS conjunction. ChildWalk
retains actual child traces and proved physical/language receipts. Its fold
derives final available children, histories, and exact output arity.
Checks refers to the actual reached calls. The rejected earlier draft's
unrestricted arbitrary-state premise has been replaced. Archived compiled
drafts remain outside Audit in `/tmp/mcfta-native-accepted-*-unrestricted-calls-20261015.lean`.
AcceptedReceipt composes the real prefix, ordered child fold, and final
constructor. It derives actual edgeBody completion, checked EdgeProduced,
heap Keeps, resident output, and literal children. Its child receipts remain
explicit proof obligations. AcceptedReadback derives the ordered child calls
and exact constructor from observed body completion. Each child's completing
bound is strictly below the parent bound. Its semantic theorem still requires
bounded receipts for walks anchored at the exact post-prefix state. This is
conditional accepted-body correctness, not a closed general fuel induction.

NodeCalls derives actual fresh pure/self/empty calls and warm completed hits.
Fresh pure calls yield twice and complete on instruction three. The older
four-instruction completion bound remains valid. Hits yield once and complete
on instruction two. Both retain the physical machine and operation state.
Fresh calls preserve the new checked native Valid invariant with explicit
word/key bounds. AcceptedSelfChild derives a five-instruction accepted body
for singleton original child lists with an actual fresh self call. It supplies
no child receipt or future validity premise. It does not assert an inhabited
accepted language. Checked NodeMeaning/EdgeMeaning still apply only to closed
inputs in the exact empty domain. Open contexts need a separate language law.

Next derive reached-child checks through general checked node branches and
continuations, preserving native validity, real completion frames, and word
bounds. Mu and repeated-pair branches need an open-context invariant. Derive
InputsThrough and FieldsThrough from original physical inputs, actual
constructor receipts, and dynamic constraint closure. Retain matched symbols
from the actual row join. Then connect class folds, reconstruction, both
gate memo families, full guarded passes, recursive reduction, and original
construction. Do not assume the eager Produced relation or replayed effects.
General completion, global unrelated prehistory, pending equality thunks,
cache/hash/IntMap and signed-index adequacy, lifetime capacity, unsafe IO, GHC,
open contexts, repeated fixed points, getAllAtPath, decision-model, named
measures, parser/decoder bridges, and extraction remain open. Existential
body witnesses are not complete causal history correspondence. Keep the
optimized interned core and older constructor/equality targets. Sized exact
classes, finite execution, sequence, distinct size order, and both signed
inverse implications remain separate contracts.

The pinned audit passes 1,965 jobs and 50,512 theorem dependency checks using
only propext, Classical.choice, and Quot.sound. Focused endpoints pass 1,069
jobs. Logs: `/tmp/mcfta-native-accepted-audit-20261015.log` and
`/tmp/mcfta-native-accepted-focused-20261015.log`. The old unused-input warning
remains. The ten new modules have no warnings. No Haskell file changed.
Prior Nix, six-suite, format, metadata, and 205-rank checks were not repeated.
Starting snapshot: `/tmp/mcfta-native-accepted-start-20261015-1511/` (2,602 files).
Closing snapshot: `/tmp/mcfta-native-accepted-checkpoint-20261015-1531/` (2,613 files).
All earlier Lean definitions except Audit imports, repros, marked drafts,
stashes, other worktrees, and the optimized Haskell core retain their hashes.
Both external unverified intersection drafts and the limit report remain.
Weekly allowance was 93% at 2026-10-15 15:29 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments.
Older counts and next targets below are historical.

## Checked native provenance and actual heap preservation

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Checked receipt proof: `af1c9d19`. Heap and outer-memo proof: `59c41d3a`.
Actual rejection and stopped outer-call proof: `20982f98`.
Pull returned Already up to date. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-native-checked-provenance.md`, then the native
demand, checked-edge, payload, identity, and completed-cell notes. This
supersedes the completed-provenance target below. Full library scope is open.

NativeDemandProvenance defines actual checked node-body and edgeBody execution
witnesses with original inputs, physical/domain growth, available results,
and independent language. NodeGood/EdgeGood and the new Valid do not use the
eager Produced relation. CellValidity derives publication, demand, growth,
completion, and exact ready-hit receipt laws. Word bounds stay explicit in
published key links. Ready reuse does not replay physical effects.
The language law applies only to closed inputs in the exact empty domain.
Other contexts can satisfy its implication vacuously. Existential body
witnesses do not establish a complete causal history for the original thunk.
Their initial native/operation validity and all internal ranges are not
asserted. Key links do not establish full lifetime capacity. Generic completion
requires a separately proved checked receipt. Arbitrary recursive step/execute
preservation of semantic Valid is not proved.

NativeDemandHeapPrimitives derives actual node/union/edge and optional-binder
heap effects from current physical operands. Open operands need no closedness
premise for these effects. NativeDemandHeap derives step and finite execute
Keeps on every outcome from current reached InputsThrough checks. These check
work operands or optional-binder bodies; they supply no future Ready/Keeps.
PartialNativeHeap derives current outer result-memo Sound from these heap
receipts and actual operation effects. Its normalized-field and current-input
plans remain explicit. No future Sound or eager execution is assumed.

MismatchReceipt and RejectedReceipt derive actual three-instruction standalone
bodies and five-instruction publication-to-completion observations. Both
retain the original selected handle, resident sentinel, actual heap Keeps,
and checked Valid in both native families. Mismatch language uses actual
forest arity for any guard evaluator without a cached-field premise.
Equal-arity rejection retains actual conjunction/accessor effects before
empty-field allocation. Original field loads, current Cached receipts, and
operation validity derive exact independent PCS empty-intersection language.
The rejection result retains valid growing operation caches. No child code
exists. PartialNativeStopped derives current outer Sound and Frame for fresh
mismatch and rejected calls without reached-path plans or future heap facts.
NodeShortcut derives actual empty/self body receipts and independent language.
Its generic pure-wrapper completion is not a fresh-miss totality theorem.

Next prove checked provenance through accepted recursive edge and node bodies.
Derive available child results/resident edges, InputsThrough from actual
compiled operands, and FieldsThrough from original constructor receipts plus
dynamic field closure. Retain matched-symbol facts from the actual row join;
matching arity alone does not imply matching symbols. Then connect class
folds, reconstruction, both gate memo families, full guarded passes, recursive
reduction, and original construction. Do not assume eager effect replay.
General caller completion, open contexts, repeated fixed points, getAllAtPath,
global unrelated prehistory, pending equality-operation thunks, native
cache/hash/IntMap adequacy, signed indexes, lifetime capacity, unsafe IO, GHC,
decision-model, named measures, parser/decoder bridges, and extraction remain
open. Preserve the optimized interned core and older constructor/equality work.
Sized exact classes, finite execution, canonical sequence, distinct size order,
and both signed inverse implications remain separate contracts.

The pinned full audit passes 1,955 jobs and 50,413 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Focused endpoints pass
1,093 jobs. Logs: `/tmp/mcfta-native-provenance-complete-audit-20261015.log`
and `/tmp/mcfta-native-provenance-focused-20261015.log`. The old unused-input
warning remains; the ten new modules have no warnings. No Haskell file changed.
Prior strict Nix, six-suite, format, metadata, and 205-rank checks were not
repeated. They retain their previous source evidence.
Starting snapshot: `/tmp/mcfta-native-provenance-start-20261015-1449/` (2,591 files).
Closing snapshot: `/tmp/mcfta-native-provenance-checkpoint-20261015-1507/` (2,602 files).
All earlier Lean definitions except Audit imports, reproductions, marked
drafts, stashes, and other worktrees retain their hashes. Both external
unverified intersection drafts and the limit report remain unchanged.
Repository modules are authoritative. Temporary validation notes and probes
stay outside Audit. Weekly allowance was 94% at 2026-10-15 14:48 CEST.
Refresh before work; stop work and owned workers at 1% or less. No board posts
or deployments. Older counts and next targets below are historical.

## Resumable checked native edge demand

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Field/code proofs: `c8d5d219`. Native interpreter: `c82daff4`.
Stopped-language, completion, outer-memo proofs, and audit: `f4687ad9`.
Pull returned Already up to date. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-native-checked-demand.md`, then the checked-edge,
payload, identity, and completed-cell notes. This supersedes the delayed
child-execution target below. Whole-library formalization remains incomplete.

ConstraintFieldLookup reads original stored fields without interning them
again. Actual original constructors and retained table growth derive lookup
success, Ready storage, and literal original readback. Missing live storage
is unavailable model representation. Malformed physical readback retains
its checked error. No cached semantic answer or reverse trie law is assumed.
NativeCheckedCode retains ordered original child requests and exact returned
fields/arity. Accepted code equals the older compiler only under actual
conjunction receipts. Rejected effects are not identified with that compiler.

SourceEqualityNativeDemand carries the complete native and completed equality
operation states in every observation. Non-edge instructions retain existing
node control. Edge misses publish and start their original thunk, then enter
an explicit edgeBody. Arity mismatch skips original field lookup. Equal
arities run actual raw conjunction and checked guards. Rejection demands the
sentinel empty field and creates no child code. Ready output creates ordered
child requests, whose actual returned operation states remain in execution.
Missing field storage retains edgeBody and its original completion handle.
Ready and busy hits retain the entire state. The generic five-step mismatch
receipt includes publication, demand, empty-field allocation, sentinel heap,
and original thunk completion. It needs no child callback or field lookup.
Bound splitting and stable complete/blocked observations retain exact state.
The represented open-edge path keeps captured operand order. The closed
same-symbol wrapper's outer swap and separate cache remain a boundary.

NativeDemandOperations proves valid growing operation caches and full atomic
interner traces on every finite outcome. FieldsThrough requires only current
normalized fields along actual reached controls, with no future Valid/Sound.
NativeDemandMemo retains structural Shape, prior completed request/result
cells in both native families, and prior published handles on every outcome.
Running cells can complete. Structural Shape is not completed semantic
provenance or word-key injectivity. NativeDemandMeaning proves mismatch and
actual checked rejection have no common accepted finite term. The proof
uses independent guarded record language before child demand.
PartialNativeDemand preserves surrounding recursive memo keys and cells from
actual receipts. Its Sound transport retains an explicit actual heap-Keeps
premise. General native execution has not derived that heap premise yet.

Next define completed native node/edge provenance from this interpreter's
actual checked execution and independent language. Earlier NodeGood/EdgeGood
use the eager kernel's Produced relation; do not assume it here. Prove actual
heap preservation and available original/results while retaining real handles,
source errors, unfinished observations, and explicit word ranges. Discharge
FieldsThrough from original constructor receipts and dynamic edge closure.
Then instantiate outer Sound transport and connect selected class folds,
reconstruction, both gate memo families, the complete guarded pass, recursive
reduction, and original construction. Do not assume replayed physical effects.
Global histories, pending equality-operation thunks, cache/hash/IntMap and
signed-index adequacy, lifetime reservation bounds, unsafe IO, GHC execution,
general caller completion, open contexts, repeated fixed points, getAllAtPath,
decision-model, named measures, parser/decoder bridges, and extraction remain
open. Preserve the optimized interned core and older constructor/equality work.
Sized exact classes, finite execution, canonical sequence, distinct size order,
and both signed inverse implications remain separate contracts.

The aggregate audit passes 1,945 jobs and 50,309 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Focused endpoints pass
1,083 jobs. Logs: `/tmp/mcfta-native-demand-audit-20261015.log` and
`/tmp/mcfta-native-demand-focused-20261015.log`. The old unused-input warning
remains; the nine new modules have no warnings. No Haskell file changed.
Prior strict Nix, six-suite, format, metadata, and 205-rank checks were not
repeated. They retain their prior source evidence.
Starting snapshot: `/tmp/mcfta-native-demand-start-20261015-1429/` (2,581 files).
Closing snapshot: `/tmp/mcfta-native-demand-checkpoint-20261015-1446/` (2,591 files).
All prior Lean definitions except Audit imports, reproductions, marked drafts,
stashes, and other worktrees retain their hashes. Both external unverified
intersection drafts and the limit report remain unchanged. Repository modules
are authoritative. Temporary validation notes and probes stay outside Audit.
Weekly allowance was 94% at 2026-10-15 14:43 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments.

## Checked edge allocation and native child-demand boundary

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Constructor proofs: `1fa17554`. Recursive integration and audit: `261627c4`.
Pull returned Already up to date. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-checked-edge-allocation.md`, then the earlier
payload, identity, and completed-cell notes. This supersedes the earlier
edge-conjunction and mkEdge prefix target. Full library scope remains open.

SourceEqualityConjoinAllocation combines raw stored physical fields and
merges original guards. It does not demand the full equality accessor.
Actual completed cache receipts derive Ready output, Cached normalized
classes, literal constructor readback, and valid growing operation state.
Original Cached fields still require actual normalized constructor receipts;
Ready alone is not asserted to imply globally normalized arbitrary lists.

SourceEqualityMkEdgeAllocation checks stored contradiction and Bottom before
accessor demand. The other branch retains actual full accessor allocations
and runs the existing signed arity test on represented natural paths.
SourceEqualityMkEdgeArity derives exact root bounds and actual acceptance
of every satisfying complete term at matching child arity. Ready supplies
the active-class premise. Actual build selects the original complete edge
or the empty-edge sentinel and retains the actual heap and equality effects.
The sentinel demands noConstraint, which can first allocate the canonical
empty equality key. Its completed operation tables remain intact. Only the
contradiction check itself has an unchanged-state guarantee.

SourceEqualityIntersectionEdgeAllocation checks arity mismatch before raw
conjunction and the checked constructor guard. It derives the exact source
branch and all reached allocations. Ready output retains literal Cached
constructor receipts. Children and callbacks are absent from this prefix.
The operand order is already selected; the closed worker's outer swap is
separate. PartialConjoinAllocation and PartialMkEdgeAllocation preserve
current full recursive result-cell Sound and Frame. The partial intersection
prefix and direct empty-edge continuation retain all cells without assuming
future Sound. Heap advances retain the domain and both native memo tables.
Full native Scope remains a separate invariant.

The full audit passes 1,936 jobs and 50,146 theorem dependency checks using
only propext, Classical.choice, and Quot.sound. Focused endpoints pass 1,077
jobs. Logs: `/tmp/mcfta-edge-allocation-audit-20261015.log` and
`/tmp/mcfta-edge-allocation-focused-20261015.log`. The old unused-input warning
remains. No new target has a warning. No Haskell file changed. Prior Nix,
six-suite, format, metadata, and 205-rank checks were not repeated.

Next connect these prefixes to delayed actual native child calls. Source
mkEdge can reject before child results are demanded. The older
SourceRecursiveIntersectionKernel.edge walks child callbacks before direct
makeEdge. Equality of those physical effects is not proved. Retain its
component proofs, but do not use them as complete source demand refinement.
Add completed-operation state and checked phases to native edge execution.
Retain actual operand order, both native memo families, errors, unfinished
observations, and ready child continuations. Then connect selected class
folds, reconstruction, both gate memo families, the complete guarded pass,
recursive reduction, and original construction. Do not assume replay effects.
Global histories, pending thunks, source cache/hash/IntMap adequacy, signed
indexes, the lifetime reservation bound, unsafe IO, GHC execution, general
caller completion, open contexts, repeated fixed points, getAllAtPath,
decision-model, named measures, parser/decoder bridges, and extraction remain
open. Optimized interned and older constructor/equality work remain intact.
Exact Sized classes, finite execution, canonical sequence, distinct size
order, and both signed inverse implications remain separate contracts.

Starting snapshot: `/tmp/mcfta-edge-allocation-start-20261015-1413/` (2,573 files).
Closing snapshot: `/tmp/mcfta-edge-allocation-checkpoint-20261015-1426/` (2,581 files).
All prior Lean proofs except Audit imports, reproductions, marked drafts,
stashes, and other worktrees retain their hashes. Both external unverified
intersection drafts and their limit report remain unchanged. Repository
proof modules are authoritative; validation notes and probes stay outside
Audit. Weekly allowance was 95% at 2026-10-15 14:24 CEST. Refresh before work.
Stop work and owned workers at 1% or less. No board posts or deployments.

## Actual equality allocation prefixes and recursive memo preservation

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Constructor/cache proofs: `ee8964d7`. Guard/precheck proofs: `b09fcb39`.
Recursive memo integration and audit: `bb35a074`. Pull is current.
Continue on `formalize` and push verified checkpoints. Read
`lean/notes-payload-allocation-receipts.md`, then the identity correspondence
and completed-cell notes. This supersedes the earlier constructor-prefix target.

SourceEqualityConstraintAllocation derives complete physical values, original
normalized-field receipts, exact class readback, and actual abstract interner
steps. SourceEqualityPhysicalPayloadCanonical proves literal equality from
coherent physical trie keys. SourceEqualityConstraintMemoAllocation retains
separate completed combination and descent caches with original arguments.
Validity checks exact payload computation and canonical Ready values. Empty
operation tables need no supplied cached answers. Hits preserve the full state.
Combination bypasses the memo only for contradiction or BOTH live empty.
Descent bypasses for contradiction or live empty. Other completed operations
derive literal existing payload results and retained allocation receipts.
Pending runtime thunks and concurrent schedules remain outside this model.

GuardAllocationPlan separates the pure Maybe syntax test from payload demand.
Demanded guard plans retain original Same normalization and right-fold steps.
Unsupported syntax performs no allocation. A contradictory first operand skips
the second payload. AccessorAllocation retains exact sourceEqualities classes.
Original normalized-constructor receipts give literal PhysicalPayload.own
readback. General reverse trie reconstruction is not inferred from WellFormed.
PrecheckAllocation preserves the full empty fast path and returns the exact
existing native branch. Its own-first combination can allocate a key that
never becomes an outer request.

PartialAllocationFrame preserves running requests, returned cells, current
Sound, and physical key links through actual constructor traces. The partial
accessor/precheck prefix composes concrete receipts at actual returned states.
PartialPayloadAllocation models inherited-before-own combination and actual
selected child descent. Contradiction makes no child request. The proof derives
exact output, child satisfaction, and existing source identity at preparation
without a new allocation. These proofs do not assume future Sound or equal
nonmemoized native effects. Full native Scope remains separate.

The aggregate audit passes 1,929 jobs and 50,083 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Focused integration passes
1,074 jobs. Logs: `/tmp/mcfta-payload-allocation-audit-20261015.log` and
`/tmp/mcfta-payload-allocation-focused-20261015.log`.
The existing unused-input warning remains. No Haskell files changed. Earlier
strict Nix, six-suite, format, metadata, and 205-rank checks were not repeated.

Next thread concrete allocation effects through the complete guarded native
pass. Start with actual edge conjunction and mkEdge arity/accessor effects.
Then retain selected class folds, native intersection calls, reconstruction,
original guard labels, and both gate memo families. Connect these effects to
the complete recursive worker and original graph-construction trace. Preserve
actual demand and short circuits; do not impose textual allocation order.
Global result-memo prehistory, pending operation thunks, source cache/hash and
IntMap adequacy, machine indexes, the lifetime reservation bound, unsafe IO,
and GHC evaluation remain open. Signed conversion keeps its capacity premise.
General caller completion, open contexts, repeated fixed points, getAllAtPath,
decision-model, named-measure/parser/decoder bridges, and extraction remain open.
Whole-library formalization is not complete. The optimized interned core,
older constructor/equality work, and all distinct Sized contracts remain.

Starting snapshot: `/tmp/mcfta-payload-allocation-start-20261015-1343/` (2,561 files).
Closing snapshot: `/tmp/mcfta-payload-allocation-checkpoint-20261015-1406/` (2,573 files).
Its preservation.json records exact hashes. All prior Lean proofs except Audit
imports, reproductions, marked drafts, stashes, and other worktrees are unchanged.
Both unverified intersection drafts and their limit report retain their hashes.
Validation notes and exploratory probes remain outside Audit. Repository proof
modules are authoritative. Weekly allowance was 95% at 2026-10-15 14:04 CEST.
Refresh before work. Stop work and owned workers at 1% or less.
No board posts or deployments.

## Physical identity correspondence and signed result-memo keys

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Proof and audit: `d851d5fb`. Pull is current with no upstream change.
Continue on `formalize` and push verified checkpoints. Read
`lean/notes-constraint-identity-renaming.md`, then the completed-cell note.
This section supersedes the earlier identity-interface next target below.

CacheRenaming relates canonical stored identities through shared complete
physical keys. Equality is preserved in both directions. Different counters,
unused reserved candidates, extra production-side constraint entries, and
independent permitted atomic growth are allowed. Shared-key interning retains
coverage and derives the actual returned identity pair.
SourceEqualityPartialConstraintRenaming lifts this to tagged payloads and
complete result-memo keys. Actual identification and preparation derive the
relation. Recorded payload transport retains ordered physical trie equality
and inherited satisfaction. Contradiction and live empty remain distinct.

SourceEqualityPartialMemoRenaming compares corresponding logical result cells
and publication histories. Actual preparation/publication preserve handles.
Lookup, demand, phase changes, and completion retain the original requests,
busy observations, and full returned values. The relation derives full second-
side table validity. Related.sound transports every completed-cell proof under
actual native heap preservation. No future Sound or equal replay effects are
assumed. This relation does not permit arbitrary extra pre-existing result
cells. It is not a complete process-global result-memo history refinement.

SourceEqualityPartialConstraintWords composes physical renaming with actual
signed identity conversion. A complete supply count within one full word
period preserves key equality. Count every lifetime reservation, including
losing insertion candidates and other callers. The bound is a premise.
It does not follow from resident entry counts or the current operation.
Negative identities are included. The existing full-wrap counterexample remains.
The bits parameter counts magnitude bits; a word with w total bits uses w-1.

The aggregate audit passes 1,918 jobs and 49,920 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Log:
`/tmp/mcfta-constraint-renaming-audit-20261015.log`.
The existing unused-input warning remains. No Haskell file changed. Earlier
Nix, six-suite, format, metadata, and 205-rank checks were not repeated.

Next derive actual allocation-capable payload receipts. Start with inherited/
local combination and child descent. Then extend through guard extraction
and native prefixes. The source can allocate entries that never become outer
requests. Retain actual demand and short-circuit behavior. Do not impose a
textual event order. Connect reached entries to represented physical keys and
apply the proved memo interface. Source cache/hash/IntMap adequacy, machine
index bounds, the global lifetime reservation bound, and unrelated global
result-memo history remain open. General caller completion, open contexts,
repeated fixed points, getAllAtPath, GHC scheduling, unsafe IO, native containers,
decision-model, named-measure/parser/decoder bridges, and extraction remain open.
Whole-library formalization is not complete. The optimized interned core,
older constructor/equality proofs, and all distinct Sized contracts remain.

Starting snapshot: `/tmp/mcfta-constraint-renaming-start-20261015-1329/` (2,556 files).
Closing snapshot: `/tmp/mcfta-constraint-renaming-checkpoint-20261015-1340/` (2,561 files).
Its preservation.json records exact hashes. All prior Lean proofs except
Audit imports, reproductions, marked drafts, stashes, and other worktrees are
unchanged. Both unverified intersection drafts and their limit report retain
their exact hashes. The source allocation-site audit and build logs are kept
in the closing snapshot. No external draft or probe is imported.
Weekly allowance was 96% at 2026-10-15 13:39 CEST. Refresh before work.
Stop work and owned workers at 1% or less. No board posts or deployments.

## Completed result-memo invariant and actual public language

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Frame and key proofs: `45d7249a`. Recursive semantic proofs: `51a5922c`.
Completed fixture and aggregate audit: `44d73de6`.
HTTPS pull succeeds with no upstream change. Main remains an ancestor of
`formalize`. Continue on this branch and push verified checkpoints. Read
`lean/notes-result-memo-soundness.md`, then the worker and upstream notes.
This section supersedes the older completed-cell next target below.

SourceEqualityPartialMemoFrame.run_frame preserves valid physical key links,
constraint and publication table growth, original running ancestor requests,
and all completed cells through every bounded worker observation. It covers
source errors and incomplete observations without a semantic callback premise.
SourceEqualityPartialMemoSound.Sound checks every actual cell at the current
native heap. Original requests remain resident, closed, and well formed.
Returned values remain resident and closed. Their independent language narrows
the original language and is exact under inherited constraint satisfaction.
Physical trie identity transport retains ordered ascending keys and coherent
resident node references. Native heap extension transports immutable meaning.

SourceEqualityPartialResultMemoProofs.run_verified derives final Sound and
the existing contextual NodeLaw by induction on the actual body bound.
It follows native prefixes, indexed children, rows, allocations, and actual
request completion. Reached check plans contain native word checks and
smaller actual receipts. They contain no future Sound or semantic oracle.
SourceEqualityPartialResultMemoSource.public_exact starts at actual closed
normalized source construction with empty tables. Successful checked execution
then gives final Sound, native Scope, heap preservation, resident closed output,
and exact original public language. Successful execution remains a premise.
The distinct ResultMemo module names preserve the older gate-memo proofs.

SourceEqualityPartialMemoReuse.run_ready returns the full stored value and
identical full state for a repeated completed original request at every body
bound, including zero. It does not replay native effects. The successful
SourceEqualityPartialMemoCompletedExample constructs p(a,a), shares the leaf,
and executes the actual cold worker. Kernel reduction verifies two returned
cells, their published keys, full receipts, and the reached check plan.
The source public theorem derives exact language and Sound for this run.
SourceEqualityOuterMemoCycleInvariant retains the actual original closed busy
fixture with two evaluating cells, valid tables, no other allocated cells,
and no completed answer at any key. It is a fixed finite observation, not a
GHC divergence theorem or an all-bounds failure theorem.

The aggregate audit passes 1,914 jobs and 49,869 theorem dependency checks.
Only propext, Classical.choice, and Quot.sound occur. Log:
`/tmp/mcfta-memo-invariant-audit-20261015.log`.
The existing unused-input warning remains. No Haskell source changed in this
checkpoint. The prior strict Nix build, all six suites (687 examples plus
golden tests), Fourmolu, Cabal-gild, metadata checks, and the 205-rank example
retain their earlier source evidence. They were not repeated.

Next relate the physical constraint interner to production EqConstraints
allocation up to identity renaming. Native prefixes do not yet expose every
production allocation event. Retain ordered physical trie equality, cache
validity and extension, and result-memo key links. Do not assume equality of
numeric IDs from independently allocated tables. The sequential adapter also
needs source demand/runtime correspondence. General successful completion,
open contexts, repeated fixed points, getAllAtPath, native containers, GHC
scheduling, unsafe IO, decision-model, named-measure/parser/decoder bridges,
and extraction remain open. The current solver preparation and all distinct
Sized contracts remain preserved. Whole-library formalization is not complete.

Starting snapshot: `/tmp/mcfta-memo-invariant-start-20261015-1258/` (2,543 files).
Closing snapshot: `/tmp/mcfta-memo-invariant-checkpoint-20261015-1324/` (2,556 files).
Its `preservation.json` records exact hashes and retained external drafts.
All older Lean proofs except Audit imports remain byte-identical. Reproductions,
marked drafts, stashes, and other worktrees remain unchanged. The optimized
interned core, equality code, Sized definitions, both unverified intersection
drafts, and their limit report retain their exact hashes. Exploratory probes
remain outside Audit; repository modules are authoritative.
Weekly allowance was 96% at 2026-10-15 13:23 CEST. Refresh before work.
Stop all work and owned workers at 1% or less. No board posts or deployments.

## Recursive result memo and current solver sort inference

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Solver preparation proof: `3e881cdb`. Recursive memo proof: `b07b8612`.
Current original-map API proof: `7366ee10`.
Main is an ancestor of `formalize`. Continue on `formalize` and push verified
checkpoints. Read `lean/notes-result-memo-worker.md` and
`lean/notes-main-1eb4ab05.md`. This section supersedes older source-head and
result-memo integration targets below.

SourceEqualityPartialMemoWorker threads the full native state, a physical
constraint interner, and typed result thunks through indexed children and
ordered rows. Its full key is inherited constraint identity plus source
NodeRef. Constraint interning compares ordered physical tries and ignores
cached path sets. IntMap readback requires valid ascending tries. Generic
cache theorems preserve stored keys, identity equality, and repeated lookup.
The worker publishes the original request before body evaluation. Ready hits
reuse complete stored values. Busy, source errors, exhausted bodies, unfinished
native stages, and pending constructors remain separate observations.

SourceEqualityOuterMemoWorkerCycle constructs the original closed R fixture
from cold tables. The actual recursive worker executes both native prefixes
and demands the running root cell. Kernel evaluation retains exactly two
allocated running requests, empty inheritance, the distinct wrapper, root key,
and full final state. observation_receipts derives the complete construction
and recursive execution equalities. This replaces the separate abstract thunk
trace as the fixture endpoint. It does not prove a GHC exception or divergence.

These constraint identities are reconstructed. Native prefixes do not yet
expose every production EqConstraints allocation event. Source correspondence
must relate the constraint tables up to identity renaming. The sequential
adapter does not prove the full Haskell row demand order. An exhausted body
has already published and started its thunk. A larger bound must restart at
the original input state; resuming those evaluating cells would observe busy.

The upstream solver now infers integer function sorts for undeclared applied
names. Application collection follows the complete source AST and actual
query/assumption order. Last occurrence selects the arity, including conflicts.
Five additive SourceAppliedDeclarations/SourceSolverAppliedPreparation/
SourceSizedLiquidAppliedAmbient/SourceSolverAppliedPublic/
SourceSizedFiniteKeysAppliedLiquid modules give current complete preparation,
exact full domains, encoded query meaning, public laws, and actual raw-map
Sized execution. Applications, casts, quantifiers, and ambient assumptions
remain supported. App-free/core compatibility preserves the old preparation.
Correct external responses and finite attempts remain explicit contracts.
Exact accepted terms per size, finite execution, canonical sequence, distinct
size order, and both separate signed rank/unrank implications remain covered.
Historical fixed-preparation wrappers retain historical meanings unless a
current wrapper or the proved app-free compatibility applies.

Generic constructor dispatch and decimal Integer/Int parsing also changed.
Their actual malformed-label/parser bridges remain open. The new measuredBy
named-measure frontend is not yet modeled. The lower formula semantics do not
by themselves prove its extraction, resolver, arity, or error precedence laws.
The interned core, equality operations, Sized definitions, older constructor
proofs, counterexamples, and repairs remain preserved.

The aggregate audit passes 1,902 jobs and 49,621 theorem dependency checks.
Only propext, Classical.choice, and
Quot.sound occur. The old unused inputs warning remains. Strict Nix builds
all packages, test and benchmark executables. All six Haskell suites pass:
687 examples plus golden tests. Fourmolu, Cabal-gild, and package metadata
checks pass. The new named-measure example agrees on counts and 205 ranks.
These checks do not establish whole-library correspondence. Logs are in the
two proof notes and `/tmp/mcfta-result-memo-audit-20261015.log`.

Next prove a completed-cell invariant for the actual memo worker. Retain the
original physical request, resident immutable result, and exact contextual
language under inherited satisfaction. Prove preservation through actual
children, rows, native effects, and successful completion. Ready hits must
reuse that proof under heap extension. Do not assume identical native effects
from replay without a memo hit. Then connect completed executions to the
existing caller graphs and public language laws. Keep the actual busy cycle.

Starting snapshot: `/tmp/mcfta-result-memo-start-20261015-1236/`.
Closing snapshot: `/tmp/mcfta-result-memo-checkpoint-20261015-1252/`.
All older Lean proofs except Audit imports remain byte-identical. Repros,
marked drafts, stashes, and other worktrees remain unchanged. Both unverified
intersection drafts and their limit report retain their exact hashes. The
first-demand scratch precursor remains superseded and unimported.

General caller completion, complete result-memo/source correspondence, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC scheduling,
decision-model, named-measure/parser bridges, and extraction remain open.
Weekly allowance was 97% at 2026-10-15 12:52 CEST. Refresh before work.
Stop all work and owned workers at 1% or less. No board posts or deployments.

## Actual outer requests and necessary first-child completion

Proofs: `7369264b`. Source: `TharkunAB/cfta`, main `239feb64`.
HTTPS pull is current. Main remains an ancestor of `formalize`. Continue on
`formalize` and push checkpoints. Read `lean/notes-outer-worker-demands.md`,
then `lean/notes-outer-caller-cycle.md`. This section supersedes the earlier
first-incomplete-worker target and unconditional physical-key rank targets.

SourceEqualityOuterCallerWorkerCycle runs the actual one-level outer worker
at the original closed normalized R. It retains the first incomplete callee
W(R), its actual inherited payload, and its full returned warm state. The
same worker at that W(R) call reaches R's original physical node reference.
Both payloads are literal EmptyConstraints. Both callers are distinct
ordinary nodes with one row. observation_receipts derives the original
construction and both complete worker-result equalities from execution.
No completed caller graph, future warm scope, or successful callback is given.

SourceEqualityPartialFirstDemand.first_required is a general one-row
necessary condition. With the actual one-level child receipt, any successful
body under any recursive callback requires that same child call to succeed
at that exact warm state. Native prefix, own readback, combination, and
indexed child control derive this law. It does not assume termination.
The fixture required theorem instantiates it at both callers. actual_pending
combines both necessary demands and full receipts with the existing typed
result-thunk trace. Repeated root lookup observes busy with neither result
complete. Busy is not a GHC exception, successful result, or fallback policy.

The Haskell audit distinguishes list-spine demand from child-result demand.
Equal-arity setChildren checks finite list spines. Edge interning then hashes
child identities, including on hits. For each verified unfinished one-row
body with a live payload and positive arity, this requires the first child
before body completion. A completed result-memo hit can return immediately.
No all-row eagerness or deep child normal form is asserted. The cached
hashable 1.5.1.0 source and its archive hash are recorded in the proof note.
GHC execution, containers, unsafe IO, and blackhole correspondence remain
separate. No production Haskell, reproduction, or package setting changed.

Next integrate the actual result memo with the recursive worker. Represent
its full key using inherited EqConstraints identity and node identity.
Retain trie-based equality of physical class keys; semantic denotation alone
is insufficient. Thread publication, running cells, completion, and memo
state through child, row, and native effects. Preserve busy, source errors,
and exhausted bounds distinctly. Compare completed executions with the
existing caller graph and exact-language laws. Do not invent a production
cycle policy or attempt an unconditional decreasing-key rank for this source.

The aggregate audit passes 1,894 jobs and 49,138 dependency checks with
only propext, Classical.choice, and Quot.sound. The older unused inputs
warning remains. Focused builds also pass. Logs:
`/tmp/mcfta-outer-worker-cycle-20261015.log` and
`/tmp/mcfta-outer-worker-cycle-audit-20261015.log`.
Exact source excerpts: `/tmp/mcfta-worker-demand-source-audit-20261015.txt`.
No Haskell tests, benchmark, Fourmolu, Cabal-gild, or metadata checks were
repeated because their files and definitions are unchanged. The earlier
six suites (687 examples plus golden tests) and Nix checks remain evidence
for their prior source checkpoint, not proof of whole-library correspondence.

Starting snapshot: `/tmp/mcfta-worker-demands-start-20261015-1218/`.
Closing snapshot: `/tmp/mcfta-worker-demands-checkpoint-20261015-1234/`.
All starting Lean proofs except Audit imports, retained repros, marked drafts,
stashes, and other worktrees remain unchanged. The optimized interned core,
older constructor and equality work, and Sized exact classes, finite size
execution, size order, and both distinct rank inverses retain their source
definitions. Both earlier unverified intersection drafts retain their hashes.
The scratch first-demand precursor is retained as
`/tmp/mcfta-one-row-demand-pre-integration.lean.draft`. Repository modules
supersede its old namespace dependencies. No theorem is imported from it.

General caller completion, full result-memo correspondence, open contexts,
repeated fixed points, getAllAtPath, native containers, GHC scheduling,
decision-model, and extraction remain open. Weekly allowance was 97% at
2026-10-15 12:33 CEST. Refresh it before work. Stop work and owned workers
at 1% or less. No board posts or deployments.

## A closed source input repeats the actual outer caller key

Prefix proof and reproduction: `eed062bd`. Typed result-thunk proof:
`6e4d477d`. Source: `TharkunAB/cfta`, main
`239feb64`, merged at `b3d06a08`. Upstream comparison checkpoint:
`83f20c4c`. Main is an ancestor of `formalize`. Continue on `formalize`
and push checkpoints. Read `lean/notes-outer-caller-cycle.md` and
`lean/notes-main-refresh-20261015.md`. This section supersedes unconditional
caller-rank targets and older source-head statements below.

Use W(n)=w(n), B=mu r.(a | p(W(r),W(r))), C=p(W(B),W(B)),
A=mu r.(a | p(W(r),W(C)) [0=1]), and R=p(W(A),W(C)) [0=1].
The live source checks A intersect B=A, C intersect B=C, A intersect C=R,
and actual root-prefix children [W(R),W(R)]. The selected endpoints are
closed ordinary wrappers. Both actual inherited descents are empty.

SourceEqualityOuterCallerCycle constructs closed normalized source syntax,
runs the concrete native root prefix, then runs the wrapper prefix at its
actual returned warm state. Kernel evaluation identifies the returned node
reference with R and both physical payloads with literal EmptyConstraints.
The observed child-to-parent physical-key dependencies form the cycle
(empty,R) -> (empty,W(R)) -> (empty,R). not_wellFounded proves that this
observed relation is not well founded. A physical-key rank cannot strictly
decrease across both calls. Outer Haskell memo/runtime correspondence and
the absence of every finite monadic graph are not asserted by this theorem.

The Haskell result memo returns the same stored unfinished thunk on a hit.
modifyNode and edge interning demand child identities before a node can
return. The retained reproduction checks its finite identity certificate
and prints Just True. Both warm and fresh cold full-pass demands time out
after three seconds. This is observed timeout evidence, with a separate
exact cycle certificate and source demand analysis. No particular runtime
exception is claimed. Only the false finite-traversal comment is corrected.
No production algorithm is repaired.

SourceEqualityOuterCallerMemoCycle reuses FlatMemoThunk. In the actual
empty-inherited fiber, distinct root and wrapper requests are published and
demanded before completion. Repeated root lookup returns its original handle.
Demand observes busy, with neither result in the completed projection.
actual_pending instantiates this logical trace with the checked source cycle.
Busy is not a claimed GHC exception, source return, or fallback policy.
The demand order still needs an adequacy proof from actual outer operations.

Next drive SourceEqualityPartialWorker until its first incomplete child call.
Retain the actual child and returned warm state, then do the same at the
wrapper. Connect these outer worker constructor demands to the typed
result-thunk trace. Extend source comparison beyond the empty-inherited fiber.
Keep GHC correspondence separate. A total intended reduction needs an explicit cycle policy and a
finite-progress argument. Pending-key fallback alone does not rule out an
infinite sequence of distinct keys. Do not resume an unconditional decreasing
key-rank proof for the unchanged source. Successful-worker, exact-language,
constraint-inventory, and equality-free Region proofs remain intact.

The aggregate audit passes 1,892 jobs and 48,855 dependency checks with
only propext, Classical.choice, and Quot.sound. The older unused inputs
warning remains. The retained reproduction compiles with -Wall -Werror.
Fourmolu and all four Cabal-gild checks pass in Nix. Logs:
`/tmp/mcfta-outer-caller-cycle-*-20261015.log` and
`/tmp/mcfta-outer-caller-memo-*-20261015.log`. The earlier merged strict
build, all six suites (687 examples plus golden tests), benchmark build,
and package metadata checks pass. They were not repeated for a comment edit.

Starting snapshot: `/tmp/mcfta-main-refresh-start-20261015-1153/`.
Closing snapshot: `/tmp/mcfta-outer-caller-memo-checkpoint-20261015-1216/`.
Backup: `backup/formalize-before-main-239feb64-20261015-1154`.
Pre-refresh Lean proofs except Audit imports, repros, marked drafts, stashes, and
other worktrees remain intact. Both earlier unverified intersection drafts
retain their original hashes. The source comparison preserves the optimized
interned core and older constructor/equality work. Sized exact classes,
finite execution, size order, and both distinct rank inverses are unchanged.

General caller completion, the outer memo operational bridge, open contexts,
repeated fixed points, getAllAtPath, native containers, GHC scheduling,
decision-model, and extraction remain open. Weekly allowance was 97% at
2026-10-15 12:15 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. No board posts or deployments.

## Upstream main refresh at 239feb64

Merge `b3d06a08` retains formalization parent `0c9afd41` and upstream main
`239feb6477ecf352c696ed4d63a450fb4008e1ac`. Main is an ancestor of
`formalize`. Continue on `formalize` and push checkpoints. Read
`lean/notes-main-refresh-20261015.md`, then `lean/notes-origin-boundaries.md`.
This section supersedes older source-head statements below.

Core and generator source files and tests are unchanged. All 2,314 Lean-tree
files were byte-identical before documentation updates. The starting snapshot
`/tmp/mcfta-main-refresh-start-20261015-1153/` contains 2,514 files, both
unverified intersection drafts, and their limit record. Backup branch:
`backup/formalize-before-main-239feb64-20261015-1154`. Existing proofs,
repros, marked drafts, stashes, and other worktrees remain intact.

Upstream adds decision-model and moves Data.CFTA.GHC.Session into its
library, with session options and expression compilation. These APIs remain
outside formal source coverage. Core and Sized correspondence retain their
source definitions. Preserve exact size classes, finite execution, size order,
both distinct rank inverses, the optimized core, and older constructor and
equality work.

The strict Haskell build passes for all libraries, tests, and benchmarks.
All six test suites pass: 687 examples plus the hole-fit golden suite.
Fourmolu, all four Cabal-gild checks, and all four package metadata checks
pass in Nix. The aggregate Lean audit passes 1,890 jobs and 48,594 dependency
checks with only propext, Classical.choice, and Quot.sound. The older unused
inputs warning remains. Logs: `/tmp/mcfta-main-refresh-*-20261015.log`.

Next derive a rank or finite dependency argument for actual constrained
outer child continuations, including native narrowing, inherited combination
and descent, Mu cleanup, and stopping at Mu and union inputs. The retained
height, inherited-closure, and physical-absorption counterexamples still
apply. Do not assume a future finite node inventory, completed caller graph,
or successful receipt to prove general existence. General caller termination,
the outer memo table, open contexts, repeated fixed points, getAllAtPath,
native containers, GHC scheduling, decision-model, and extraction remain open.
Weekly allowance was 97% at 2026-10-15 11:53 CEST. Refresh it before work.
Stop all work and owned workers at 1% or less. No board posts or deployments.

## Source boundaries for inherited payloads and physical node factors

Proofs and reproductions: `b163ddd4`. Source: `TharkunAB/cfta`,
`origin/main` at `33148e6d`. HTTPS pull succeeded; main is unchanged and
is an ancestor of `formalize`. Continue on `formalize` and push checkpoints.
Read `lean/notes-origin-boundaries.md`. This section supersedes the generic
node-factor and inherited-closure candidate bounds below.

One fixed normalized local constraint uses `0 = 1.0.0` and `0.1 = 1.0.1`.
Actual own readback has maximum path length 4. Repeated actual combination
with that payload and physical child-1 descent gives kernel-checked maximum
lengths `[0,3,4,5,6]`. Every finite prefix completes with well-formed tries.
The first descended readback, lifted to a complete Top constraint, lies
outside the entire conjunction closure of that original local constraint
and Top. That closure has exactly those two values. The retained Haskell
probe checks exact classes through seven steps and lengths through 9.
These facts do not prove an infinite set of inherited states or an actual
outer caller trace that reaches every step.

Fixed closed unary inputs A and B give B, B intersect A, and its next
intersection with A with physical graph counts `(2,3,3)`, `(4,6,7)`, and
`(12,19,26)`. The retained Haskell reproduction checks distinct identities,
closure, and matching actual local equality-prefix children. A set of
distinct source factors is not a canonical physical key. This is a finite
two-step observation, not infinite growth or a nontermination result.
The attempted kernel identity proofs remain explicitly unverified at
`/tmp/mcfta-intersection-growth-boundary-draft-20261015.lean` and
`/tmp/mcfta-intersection-growth-first-kernel.lean`. Exact live handles were
stopped after more than three minutes and thirty seconds, respectively.
The snapshot includes these drafts and their limit record. No unverified
identity theorem is imported by Audit.

Completed normalization schedules now have an exact source receipt theorem.
A small completed reference receipt identifies the actual array result;
an incomplete receipt retains the actual source call. No evaluation axiom
or production change is added. The finite physical constraint inventory
remains proved. Inherited records and their lifted readback are separate.

Next derive a decreasing rank or finite dependency argument for actual
constrained outer child continuations. Include narrowing, physical payload
combination and descent, Mu cleanup, returned ordinary children, and stopping
at Mu and union inputs. The repeated probe products are not an actual outer
trace. Do not assume original ordinary height, inherited literal closure,
physical factor absorption, a future finite node inventory, a completed
caller graph, or successful receipt to prove general existence. General
constrained caller termination, the outer reduction memo table, open
contexts, repeated fixed points, getAllAtPath, native containers,
GHC scheduling, and extraction remain open.

The audit passes 1,890 jobs and 48,594 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-origin-boundaries-20261015-audit.log`.
Both retained Haskell probes, Fourmolu, and all three active Cabal formatting
checks pass in Nix. No production Haskell changed. Earlier 650-example,
benchmark-build, and metadata checks were not repeated. Starting snapshot:
`/tmp/mcfta-origin-boundaries-start-20261015-1131/`.
Closing snapshot: `/tmp/mcfta-origin-boundaries-checkpoint-20261015-1148/`.
Older proofs except audit imports, counterexamples, marked drafts, stashes,
and other worktrees remain unchanged. Weekly allowance was 98% at
2026-10-15 11:46 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
older constructor and equality work. No board posts or deployments.

## A fixed finite inventory for recursive source constraints

Proof: `3ef4f2e1`. Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
Authenticated HTTPS pull succeeded; main is unchanged and is an ancestor
of `formalize`. Continue on `formalize` and push checkpoints. Read
`lean/notes-constraint-inventory.md`. This section supersedes the finite
derived-constraint target below.

Actual source conjunction preserves original path geometry through input
preparation, component completion, every congruence step, and actual array
normalization. Original literal paths supply fixed anchors, bounded path
segments, and a child-index alphabet. Every generated class list has at
most anchors.length components. Each path lies in the fixed word domain
of length at most gap * (anchors.length + 1). Canonical classes have no
repeated paths. Explicit bounded lists contain every generated equality
payload. The inventory also retains original payloads and contradiction.
It accounts for paths that normalization creates.

Original guard atoms give a finite list of canonical subset conjunctions.
Unchanged noncanonical literal fields remain included. The finite product
of equality and guard inventories contains every actual derived complete
constraint. The actual own-payload accessor has a finite image of this
inventory, including failures. Original normalized syntax derives all
literal checks, initial scope, closed availability, and inventory membership.
Every checked successful public return retains physical membership throughout
the heap and returned-value annotations, both source gate memo receipts,
physical histories, exact public language, and stable identical full-state
replay. Successful execution and reached native checks remain explicit.

Next inspect actual narrowed-child node origins. Test whether original node
occurrences and finite constraints can bound actual constructor outputs.
Prove that bound or retain a focused counterexample before using it in a
rank. Include physical combination and descent of inherited payloads.
Finite annotations alone do not prove finite node construction, finite
caller states, or termination. Do not assume a future finite node inventory,
decreasing height, caller graph, or successful receipt to prove existence.
The ordinary-height counterexample still applies. General constrained caller
termination, the outer reduction memo table, open contexts, repeated fixed
points, getAllAtPath, native containers, GHC scheduling, and extraction remain
open.

The audit passes 1,888 jobs and 48,536 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-constraint-inventory-20261015-audit.log`.
No production Haskell or retained reproduction changed. Earlier focused
height, formatting, 650-example, benchmark-build, and metadata checks were
not repeated. Starting snapshot:
`/tmp/mcfta-constraint-inventory-start-20261015-1118/`.
Closing snapshot: `/tmp/mcfta-constraint-inventory-checkpoint-20261015-1129/`.
Older proofs except audit imports, counterexamples, marked drafts, stashes,
and other worktrees remain unchanged. Weekly allowance was 98% at
2026-10-15 11:27 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
older constructor and equality work. The read-only HTTP board search could
not connect. No board posts or deployments.

## Original constraint origins through actual outer recursion

Proof: `228203dd`. Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
The authenticated HTTPS upstream refresh is current. Main is an ancestor
of `formalize`. Continue on `formalize` and push checkpoints. Read
`lean/notes-recursive-constraint-origins.md`. This section supersedes the
outer constraint-origin target below.

Mutual graph induction carries conditional constraint closure through the
actual local native prefix, physical combination and descent, recursive
children, literal edges, returned row tails, and indexed child walks.
Resident Mu probes derive an unchanged constructor heap after smart cleanup.
Both modifyNode branches retain the actual returned row heap. Actual child
effects derive every later scope. No future origin heap, returned scope,
recursive preservation law, or unconditional property of arbitrary
conjunction operands is assumed.

Original normalized syntax derives a finite complete literal inventory,
including raw and smart binder bodies. Checked bounded public success then
derives its caller graph, final physical guard origins, and annotations
throughout the returned value. Each guard is a literal, source Top, or
actual source conjunction. Both source gate memo receipts, recursive Scope,
physical histories, closed available output, exact public language, and
stable identical value/full-state replay remain proved. Successful worker
receipt and reached native checks remain explicit. This is not a theorem
that every caller succeeds. Only the literal inventory is proved finite;
its conjunction closure is not proved finite or decreasing. The retained
ordinary-height counterexample still rules out that proposed measure.

Next derive a finite inventory for actual derived constraint values, or
retain a focused counterexample to any proposed bound. Inspect canonical
equality normalization and actual guard conjunction. Then study a valid
outer termination measure that accounts for constrained bodies below
ordinary endpoints and actual native narrowing. Finite constraints alone
would not prove finite node construction or caller termination. General
constrained caller termination, the outer reduction memo table, open
contexts, repeated fixed points, getAllAtPath, native containers,
GHC scheduling, and extraction remain open.

The audit passes 1,884 jobs and 48,465 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-recursive-constraint-origins-20261015-audit.log`.
No production Haskell or retained reproduction changed. Earlier focused
height, formatting, 650-example, benchmark-build, and metadata checks were
not repeated. Starting snapshot:
`/tmp/mcfta-recursive-origins-start-20261015-1111/`.
Closing snapshot: `/tmp/mcfta-recursive-origins-checkpoint-20261015-1116/`.
Older proofs except audit imports, counterexamples, marked drafts, stashes,
and other worktrees remain unchanged. Weekly allowance was 98% at
2026-10-15 11:14 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
older constructor and equality work. No board posts or deployments.

## Original constraint origins and the outer height boundary

Proofs: `c77bb8c4` and `56c94073`. Source: `TharkunAB/cfta`,
`origin/main` at `33148e6d`. Authenticated HTTPS pull succeeded; main is
unchanged and is an ancestor of `formalize`. Continue on `formalize` and
push checkpoints. Read `lean/notes-constraint-origins.md`. This section
supersedes the narrowed-child origin target below.

A closed normalized example refutes ordinary-height descent. The gate
accepts ordinary endpoints above raw unused binders. Intersection removes
the binders and exposes constrained bodies. The original root has height 2;
its children have maximum height 1; actual narrowed children have maximum
height 3. Kernel evaluation proves these values for the source guarded-edge
worker. The retained Haskell reproduction reports `(2,1,3,4)` and `Just True`
for local and complete public execution. Both new children retain nonempty
inner equality. This refutes a proposed measure, not source termination.

Conditional constraint closure now follows actual native intersection,
captured targets, shared edits, selection, required paths, class folds,
final propagation, and literal reconstruction. Conjunction needs the property
of its two actual operands. No unconditional property of arbitrary guards or
future heap is supplied. Original source syntax gives a finite literal
inventory, including raw and smart binder bodies. Initial construction and
the finite closed warm native prefix derive every emitted guard from an
original literal, source Top, or source conjunction. Exact contextual public
language, both source gate memo receipts, recursive Scope, physical histories,
and stable six-stage replay remain available under reached word checks.
Only the literal inventory is proved finite. Its conjunction closure is not
proved finite. Origin derivations are not a decreasing measure.

Next carry this original inventory through the actual outer recursive graph.
Use the real local prefix, physical combination and descent, returned child
scopes, Mu cleanup, row tails, and modifyNode. Connect the invariant to checked
bounded caller success. Then study a valid measure that accounts for
constrained bodies below ordinary endpoints. Do not assume a future origin
heap, caller graph, caller success, structural height decrease, or initial
finite Mu inventory to claim general existence. General constrained caller
termination, the outer reduction memo table, open contexts, repeated fixed
points, getAllAtPath, native containers, GHC scheduling, and extraction remain
open.

The audit passes 1,882 jobs and 48,456 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. Log: `/tmp/mcfta-constraint-origins-20261015-audit.log`.
The retained Haskell fixture compiles and passes in Nix. Fourmolu and all
three active Cabal formatting checks pass. No production Haskell changed.
The earlier 650 examples, affected benchmark build, and metadata checks were
not repeated. Starting snapshot:
`/tmp/mcfta-outer-origins-start-20261015-1045/`.
Closing snapshot: `/tmp/mcfta-constraint-origins-checkpoint-20261015-1109/`.
Older proofs except audit imports, counterexamples, marked drafts, stashes,
and other worktrees remain unchanged. Weekly allowance was 98% at
2026-10-15 11:08 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
older constructor and equality work. No board posts or deployments.

## Finite exact native prefixes at arbitrary closed warm scopes

Proofs: `6cef0487` and `438393a0`. Source: `TharkunAB/cfta`,
`origin/main` at `33148e6d`. Authenticated HTTPS pull succeeded; main is
unchanged and is an ancestor of `formalize`. Continue on `formalize` and
push checkpoints. Read `lean/notes-closed-warm-completion.md`. This section
supersedes the closed gate and warm local completion targets below.

Path-length induction constructs actual closed node queries, indexed child
lookups, ordered short circuit, classes, and selection. Each returns the
original constructor heap. The two actual source memo receipts follow
without an open-unfolding cost heap or original construction history.
Predicate memo coherence remains explicit for arbitrary initial memos.

Selection and required paths now complete at each actual closed warm heap.
Their real returned state supplies the native fold and final propagation.
Every source precheck branch therefore derives finite local execution from
IdleReady, closed availability, and reached word ranges. No completed prefix,
fold, worker success, sufficient bound, GateRank.Node, or future scope is an
input. Native word ranges remain explicit.

The actual guarded-edge entry derives its physical own payload from current
annotations. Literal reconstruction retains the original symbol and full
constraint. The result has both source memo receipts, recursive Scope,
physical histories, closed resident children, stable identical value/full-state
replay at all sufficient six-stage bounds, and eventual array agreement.
Its public language narrows the input and is exact under inherited satisfaction.
Full residual guards remain intact.

Next study general constrained outer graph existence with a valid measure
or a focused closed normalized counterexample. Examine actual narrowed child
outputs and source-constraint origins. Gate rejection of constrained Mu is
proved, but does not itself prove caller termination after narrowing. Do not
assume structural smaller children, cached-depth decrease, an initial finite
Mu inventory, a future Region, a completed caller graph, or caller success.
General outer recursion, the outer reduction memo table, open contexts,
repeated fixed points, getAllAtPath, native containers, GHC scheduling, and
extraction remain open.

The audit passes 1,876 jobs and 48,215 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. Log: `/tmp/mcfta-closed-warm-edge-20261015-audit.log`.
Starting snapshot: `/tmp/mcfta-closed-gates-start-20261015-102828/`.
Closing snapshot: `/tmp/mcfta-closed-warm-checkpoint-20261015-1038/`.
Older proofs except audit imports, counterexamples, marked drafts, production
source, stashes, and other worktrees remain unchanged. No Haskell source
changed. The earlier 650 examples, affected benchmark build, formatting,
and metadata checks were not repeated. Weekly allowance was 99% at
2026-10-15 10:37 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
older constructor and equality work. No board posts or deployments.

## Finite equality-free source calls for arbitrary inherited payloads

Proofs: `32994d94` and `e4d26e69`. Source: `TharkunAB/cfta`,
`origin/main` at `33148e6d`. The upstream refresh is current. Continue
on `formalize` and push checkpoints. Read
`lean/notes-inherited-plain-completion.md`. This section supersedes the
arbitrary-inherited-payload completion target below.

Empty own classes select unchanged, contradiction, or the actual live empty
class list. Selection, required paths, the fold, and final propagation stay
explicit. Each local output is the original forest or literal empty slots.
Actual edge readback derives the smaller structural child alternatives.
No native intersection word request is reached. Physical combination and
child descent use the actual arbitrary inherited payload.

Mutual structural induction constructs the complete outer graph for each
closed available Region and every inherited payload. Original normalized
closed source syntax with empty equality readback derives that Region and
initial scope. The resulting finite run has both source gate memo receipts,
all physical invariants, and stable identical value/full-state replay above
a common seven-bound threshold. Output always narrows input and is exact
under inherited satisfaction at the independent guarded syntax language.
No inherited well-formedness, completed graph, successful receipt, sufficient
bound, recursive termination law, or future scope is an input premise.

Next prove finite source gate selection for closed available forests from
path length and actual child lookups. Closed calls cannot take open-binder
unfolding. Reuse actual closed memo receipts without adding or inferring
an open-unfolding cost heap. Compose required-path and native-fold completion
at arbitrary warm scopes under actual word ranges. Then study general outer
graph existence with a valid measure or a focused counterexample. Native
intersection can increase ordinary depth. General selected-narrowing
termination, the outer memo table, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC scheduling, and extraction remain open.

The audit passes 1,869 jobs and 48,204 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. Log: `/tmp/mcfta-inherited-plain-20261015-audit.log`.
Snapshot: `/tmp/mcfta-inherited-plain-checkpoint-20261015-0950/`.
Older proofs except audit imports, counterexamples, marked drafts, production
source, stashes, and other worktrees remain unchanged. No Haskell source
changed. The earlier 650 examples, affected benchmark build, formatting,
and metadata checks were not repeated. Weekly allowance was 99% at
2026-10-15 09:46 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, and the optimized interned core.
No board posts or deployments.

## Finite exact public execution for equality-free original syntax

Proofs: `ee4cd6da` and `347a988f`. Source: `TharkunAB/cfta`,
`origin/main` at `33148e6d`, integrated by `af4a2b87`. Continue on
`formalize` and push checkpoints. Read `lean/notes-plain-completion.md`.
This section supersedes the equality-free finite-existence target below.

Upstream now contains the same retained-cycle repair in `c292354b`.
The merge leaves all traversal source and regression bytes unchanged.
The local fresh-probe changelog note is retained. Hoogle+ data now uses
its public sublibrary. Sized and existing proof definitions are unchanged.
The old canonical ordering comparison remains valid for those definitions.
Backup: `backup/formalize-before-retained-main-20261015-0925`.

Region follows actual ordinary children and stops at Mu and union branches.
Each ordinary row has the actual empty physical equality payload. Literal
empty native prefixes retain the original structural children and reach no
native word request. Actual physical combination and descent stay empty.
Mutual structural induction constructs the complete outer graph at each
closed available scope. Actual smaller child and literal edge effects derive
every returned warm scope and history. Mu uses its real cached probes and
resident hit. No future scope or completed caller graph is supplied.

Original source annotation checks derive Region from the actual constructed
heap. Closed normalized source syntax with empty equality readback therefore
derives finite public execution, both source gate memo receipts, exact
independent guarded least language, all physical invariants, and stable
identical value/full-state replay above a common seven-bound threshold.
No successful worker receipt, complete outer graph, native word-range
hypothesis, or sufficient bound is an input premise. Full residual guards
remain intact. This does not prove general constrained outer termination.

Next extend equality-free region completion to arbitrary inherited payloads.
Retain actual contradiction and empty selected-class branches, concrete
prechecks, physical combination and descent, and final empty propagation.
Derive finite local execution and returned scope before structural recursion.
Then study general selected narrowing with a valid measure or a focused
counterexample. Native intersection can increase ordinary depth. General
constrained outer success, the outer reduction memo table, open contexts,
repeated fixed points, getAllAtPath, native containers, GHC lazy scheduling,
and extraction remain open. Do not use cached input depth as the measure.

The audit passes 1,863 jobs and 48,189 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. Log: `/tmp/mcfta-plain-completion-20261015-audit.log`.
All 650 Haskell examples pass after the new public Hoogle+ library is built
first. The initial unstaged run failed on its missing installed unit.
The affected GHC benchmark compiles; no benchmark was run. Fourmolu,
all three active Cabal formatting checks, and all three metadata checks pass.
Logs: `/tmp/mcfta-retained-main-20261015-{tests,staged-tests,format,metadata}.log`.
Snapshot: `/tmp/mcfta-plain-completion-checkpoint-20261015-0937/`.
All older proofs except audit imports, counterexamples, marked drafts,
stashes, and other worktrees remain unchanged. Weekly allowance was 99%
at 2026-10-15 09:35 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, and the optimized interned core.
No board posts or deployments.

## Actual source gate memos through recursive public reduction

Proofs: `29ce7e5c` and `51f5f888`. Source: `TharkunAB/cfta`,
`origin/main` at `c351674e`, integrated by `79f2e38e`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-recursive-memos.md`. This section supersedes the warm
recursive gate-memo target below. The Sized comparison remains current.

Closed available source gate inputs cannot take the open-binder unfolding
branch. Actual node, child, path, and class traces therefore retain the
unchanged unfolding memo and every concrete predicate memo lookup or
insertion. Both returned tables are coherent at the actual selected heap.
Physical facts, availability, and closure suffice. No unfolding-cost heap
or original gate history is assumed. The older StageMemos certificate has
an extra cost-heap field. The new closed-call receipt proves actual calls
and table coherence without asserting that extra invariant.

Concrete guarded native prefixes derive these receipts at any closed warm
scope. Mutual graph induction then carries both source memos through every
actual native prefix, recursive child, and returned row tail. All later
scopes come from actual proved effects. Actual checked bounded public
success now derives its graph, both memo receipts, exact public language,
all physical invariants, and stable identical value/full-state replay.
Original normalized closed construction derives the initial scope. No
Callback law, recursive memo law, completed outer graph, or future heap
invariant is an input premise. Native word checks remain explicit.

Next prove finite single-pass existence for equality-free ordinary regions
above opaque Mu and union boundaries. Use actual empty prechecks, physical
payload combination and descent, literal edge requests, and structural
smaller child calls. Carry returned scopes and histories. Then study the
general selected-narrowing case with a valid measure or a focused
counterexample. Native intersection can increase ordinary depth. General
outer success, the outer memo table, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
open. Do not use cached input depth as the termination measure.

The aggregate audit passes 1,857 jobs and 48,168 dependency checks with only
propext, Classical.choice, and Quot.sound. Only the older unused inputs
warning remains. Log: `/tmp/mcfta-recursive-memos-20261015-audit.log`.
Snapshot: `/tmp/mcfta-recursive-memos-checkpoint-20261015-0922/`.
All older proofs except audit imports, counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. No
Haskell source changed after the upstream checkpoint. Its 650 examples
and formatter checks were not repeated. Weekly allowance was 99% at
2026-10-15 09:19 CEST. Refresh it before work. Stop all work and owned
workers at 1% or less. Preserve Sized exact classes, finite size execution,
size order, both distinct rank inverses, the optimized interned core, and
all older artifacts. No board posts or deployments.

## Upstream canonical enumeration and checked recursive success

Source: `TharkunAB/cfta`, `origin/main` at `c351674e`, integrated by
`79f2e38e`. Proofs: `d4f945dd` and `fa9f89ed`. Continue on `formalize`
and push checkpoints. Read `lean/notes-canonical-upstream.md` and
`lean/notes-checked-recursion.md`. This section supersedes the older
worker-to-graph targets and source base below.

The complete canonicalClasses implementation is byte-identical after its
move to the core package. Sized changes only that import. Its reference,
solver-decided, and optimized query sequences retain all existing exact
node-count classes, finite size execution, size order, and both distinct
rank inverses. The new UVar canonical order and Hectare program order are
separate. No equality with the Sized sequence is claimed.

Reached recursive check plans retain actual descended payloads, native
word ranges, local prefix receipts, physical payload calls, and returned
warm states. Traversal induction derives the complete recursive graph from
actual checked bounded success. It assumes no global Callback law, binder
law, completed outer graph, or future heap invariant. Any two such successes
return the identical physical value and full native state. Public composition
from original closed normalized construction derives exact public language,
all physical invariants, and stable replay at all sufficient seven bounds.
Errors and incomplete observations remain unchanged.

Next derive source gate memo evidence for every reached warm recursive
prefix from its actual scope. Retain both memo tables and the concrete
source predicate. Then study general outer graph existence with a valid
measure or a focused counterexample. Native intersection can increase
ordinary depth. General outer termination, the outer memo table, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain open. Native word checks remain explicit.

The audit passes 1,850 jobs and 48,149 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All 650 existing Haskell examples pass in Nix: 293 core, 210
generator, and 147 refinement. Fourmolu and active Cabal formatting pass.
Logs: `/tmp/mcfta-checked-recursion-20261015-audit.log` and
`/tmp/mcfta-canonical-main-20261015-{tests,format,lean}.log`.
Snapshot: `/tmp/mcfta-checked-recursion-checkpoint-20261015-0910/`.
All older proof bytes except audit imports, counterexamples, marked drafts,
stashes, and other worktrees remain unchanged. All five retained repair
patches have identical added and removed lines relative to old and new main.
Backup: `backup/formalize-before-canonical-main-20261015-0902`.
Weekly allowance was 100% at 2026-10-15 09:07 CEST. Refresh it before work.
Stop all work and owned workers at 1% or less. Preserve the optimized interned
core and all older artifacts. No board posts or deployments.

## Recursive completed graphs and replay with changing callbacks

Proofs: `109dd0f8`, `623de23e`, and `72e32aeb`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. The upstream refresh is current. Continue on
`formalize` and push checkpoints. Read `lean/notes-recursive-graphs.md`.
This section supersedes the mutual graph and changing-callback targets below.

ReduceNode, ReduceRows, ReduceChildren, and WalkChildren now retain actual
recursive calls, Mu request receipts, checked concrete native prefixes, physical
payload calls, child indexes, literal edges, and modifyNode branches. Scope
carries native readiness, normalized guard annotations, and filtered probes.
Mutual graph induction derives full output scope, histories, availability,
closure, public narrowing, and exact public meaning under inherited equality
satisfaction. No generic binder law, recursive Callback law, complete row law,
or supplied future heap invariant is assumed. Structural arity proves that
source setChildren always takes direct equal-arity interning.

Every completed graph now has a common sufficient bound for traversal and all
six native stages. All sufficient bounds return the identical values and full
native state. Actual recursive child induction proves replay when traversal
fuel and the recursive callback change. node_unique derives complete physical
determinism. Original normalized closed syntax derives the initial scope and
available closed value. Every completed public graph at empty inherited
constraints therefore has exact public language and stable actual bounded
execution. Existence of that outer graph is not assumed to be proved.

Next prove the reverse direction from successful bounded worker execution to
these recursive graphs. Define a reached-check plan that retains each actual
native word check, completed local prefix, physical payload call, actual child
entry, and returned tail state. Walk checks pass the actual descended payload;
row checks supply child checks only after the actual local native prefix and
successful physical combination. Prove worker-to-graph by traversal-bound
induction using this plan, without a global Callback premise. Reuse local
native worker/graph lemmas and preserve exact error/incomplete observations.
Keep existing gate-memo evidence at source correspondence boundaries. Then
compose with the new semantic and replay theorems. General caller termination,
outer-graph existence for every input, the outer Haskell memo table, open
contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain open. Native intersection can increase
ordinary depth; original cached depth is not a termination measure.

Ten new proof modules pass focused builds. The aggregate audit passes
1,845 jobs and 48,140 dependency checks with only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-recursive-graphs-20261015-audit.log`.
Snapshot: `/tmp/mcfta-recursive-graphs-checkpoint-20261015-0852/` (2,258 Lean-tree files and four root documents).
All older proofs except audit imports, counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. The earlier
645 Haskell examples and formatter checks were not rerun on unchanged source.
Weekly allowance was 100% at 2026-10-15 08:52 CEST. Refresh it before work. Stop all work
and owned workers at 1% or less. Preserve Sized exact classes, finite size
execution, size order, both rank inverses, the optimized interned core, and
all older artifacts. No board posts or deployments.

## Filtered Mu probes through actual native equality execution

Proofs: `a93cc716`, `e5aaebde`, and `e1916030`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. The upstream refresh is current. Continue on
`formalize` and push checkpoints. Read `lean/notes-filtered-probes.md`.
This section supersedes the probe-invariant propagation target below.

InternedFreshOrdinaryProbeHeap derives the physical invariant for both cached
Mu probes through actual repaired source execution, including pending outcomes.
It needs no original-call history for earlier records. Actual stored substitution,
optional binders, native compiled calls, memo hits, started bodies, completion
frames, exposure, head reads, required paths, projection, general comparisons,
retention, merging, captured targets, first forcing and reuse, shared edits,
class folds, gate selection, one-pass branches, and guarded interning retain it.
Every intermediate scope comes from actual source effects. No final heap
invariant or whole-operation preservation law is supplied.

SourceEqualityPartialProbeEntry.guarded_mu connects the complete concrete native
pass to the actual outer Mu branch. Every available Mu in its returned heap
has both fixed filters, a resident cache hit, exact smart cleanup, identical
full native state, and exact independent guarded meaning. Original closed
construction derives the initial probe heap. IdleReady remains unchanged;
the new invariant is explicit and must be carried through recursive calls.

Next assemble mutually recursive completed graphs for the outer node, ordered
rows, and indexed inherited children. Retain the actual checked local native
prefix, payload combination, Mu request receipts, and modifyNode branches.
Prove scope, annotations, probe preservation, narrowing, and contextual exactness
by graph induction using each actual child induction hypothesis. The existing
Callback quantifies all IdleReady scopes, which do not contain the new probe
invariant. Do not assume that unrestricted callback law. Then connect these
graphs to SourceEqualityPartialWorker.run by traversal-bound induction and prove
replay when traversal bounds increase and recursive callbacks change. Retain
actual reached word checks. General caller finite execution remains unproved;
native intersection can increase ordinary depth. The outer Haskell memo table,
open contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain separate obligations.

All sixteen new proof modules pass focused builds. The aggregate audit passes
1,835 jobs and 48,053 dependency checks with only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-filtered-probes-20261015-audit.log`.
Snapshot: `/tmp/mcfta-filtered-probes-checkpoint-20261015-0833/` (2,247 Lean-tree files and four root documents).
Older proof bytes change only in audit imports. All counterexamples, marked
drafts, production source, stashes, and other worktrees remain unchanged.
No Haskell source changed, so the earlier 645 examples and formatter checks
were not rerun. Weekly allowance was 100% at 2026-10-15 08:33 CEST. Refresh it before work.
Stop all work and owned workers at 1% or less. Preserve Sized exact classes,
finite size execution, size order, both rank inverses, the optimized interned
core, and all older artifacts. No board posts or deployments.

## Actual outer step, ordered rows, and cached Mu reconstruction

Proofs: `6aa6c341`, `94860ace`, and `1ec8eb87`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. The upstream refresh is current. Continue on
`formalize` and push checkpoints. Read `lean/notes-partial-node.md`.
This section supersedes the outer node/row and Mu targets below.

Actual original probe calls derive both filtered Mu probes. Filtering either
cached probe again returns the identical value and heap. Coherent residency
then forces a complete request hit at the stored key. Smart cleanup preserves
availability, free names, and exact public guarded meaning. It is not node
identity. Original closed construction supplies this exact bounded Mu branch
from an actual stored record. No generic binder language law is supplied.

The actual ordered row worker runs each native edge pass and inherited child
continuation at its returned warm state. Complete graphs have uniform stable
six-stage bounds for a fixed node callback. Reached word checks derive the
reverse worker/graph direction. Pointwise proofs derive row scope, annotations,
narrowing, and exact public union meaning under inherited satisfaction.
Source modifyNode compares ordered interned identities. Coherence recovers
complete row equality on its unchanged-node fast path. Changed rows use the
literal source node constructor. Both branches have exact row-union meaning.

The bounded outer worker now retains every source branch, source Rec errors,
actual Mu reconstruction, row observations, and traversal exhaustion. One
successful outer step has the full local callback conclusion under explicit
smaller-call, reached-word, and filtered-probe premises. This is not yet a
recursive Callback theorem. The outer Haskell memo table is not modeled here.

Next prove the filtered-probe heap invariant through every actual native and
source constructor effect. Original source origins derive it, but IdleReady
does not contain it. Preserve it explicitly; do not infer it from IdleReady or
assume a binder language law. Then discharge the smaller recursive callback
by traversal-bound induction with actual reached word checks. Prove replay
when traversal bounds increase and callbacks change. Existing row stability
fixes the callback, so it does not supply that result. General caller finite
execution remains unproved; native intersection can increase ordinary depth.

The audit passes 1,819 jobs and 47,971 dependency checks with only propext,
Classical.choice, and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-partial-node-20261015-audit.log`.
Snapshot: `/tmp/mcfta-partial-node-checkpoint-20261015-0819/` (2,230 Lean-tree files and four root documents).
All older proofs except audit imports, counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. No Haskell
source changed, so the earlier 645 examples and formatter checks were not
rerun. Weekly allowance was 100% at 2026-10-15 08:19 CEST, after a reported reset.
Refresh it before work. Stop all work and owned workers at 1% or less.
Preserve Sized exact classes, finite size execution, size order, both rank
inverses, the optimized interned core, and all older artifacts. Open contexts,
repeated fixed points, getAllAtPath, native containers, GHC lazy scheduling,
and extraction remain separate obligations. No board posts or deployments.

## Concrete inherited edge continuation and indexed child descent

Proofs: `55fd6fed`, `0f8c72b5`, and `07410acf`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-inherited-edge.md`. This section supersedes the inherited
payload and child-continuation targets below and earlier audit counts.

SourceEqualityDescend follows actual trie descent, the existing structural
two-path test, lazy ascending path-set reconstruction, and source class sorting.
It does not normalize again. Actual record construction derives ascending trie
maps. Coherent fields, ascending maps, and nontrivial classes form the inherited
payload invariant. Descent preserves it and denotes exactly the surviving
same-child equality pairs. Parent satisfaction supplies every child obligation.

Actual inherited/local combination derives finite coherent physical readback
and exact conjunction. The bounded array adapter keeps timeout as incomplete;
every sufficient work bound returns the identical combined payload. Complete
source guard readback supplies the local payload and satisfaction without a
supplied guard-to-payload law. The supported path domain remains nonnegative.

The indexed child worker retains actual callback receipts, zero-based indexes,
returned warm states, errors, and incomplete observations. Complete graphs and
successful workers agree in both directions. Arity is preserved, so source
setChildren takes direct interning. A pointwise graph induction derives native
scope, histories, annotations, narrowing, and exact forest meaning under the
parent equalities. It uses one explicit local recursive-node induction hypothesis;
it does not assume a whole-child-forest preservation law.

Concrete local native edge narrowing now composes with this actual inherited
continuation. Source payload combination, indexed traversal, and original-label
edge allocation derive exact contextual public edge meaning. Worker/graph
agreement holds in both directions. Six native stage bounds are stable for a
fixed recursive node callback. This is not a complete reducePartially theorem:
the outer node recursion must still derive that callback law and its execution.

All six new modules pass focused builds. The aggregate audit passes
1,812 jobs and 47,884 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-inherited-edge-20261015-audit.log`.
Snapshot: `/tmp/mcfta-inherited-edge-checkpoint-20261015-0801/` (2,222 Lean-tree files and four root documents).
Older proofs except audit imports, all counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. The earlier
645 Haskell examples and formatter checks apply to unchanged source and were
not rerun. Weekly allowance was 15% at 2026-10-15 08:01 CEST. Refresh it before work.
Stop all work and owned workers immediately at 1% or less.

Next build the actual ordinary node/row traversal around
SourceEqualityInheritedEdgeWorker. Derive its recursive node Callback by
traversal-bound induction. Retain modifyNode's unchanged-edge fast path and
literal source node construction. The Mu branch must reuse actual cached
probes and perform smart cleanup; do not replace it with node identity or a
supplied binder language law. Resident keys and existing finish_exact support
that proof. Preserve all incomplete/error scopes. General caller termination
remains unproved: local finite passes do not imply it, and native intersection
can increase ordinary depth. Open contexts, repeated fixed points, getAllAtPath,
native containers, GHC lazy scheduling, and extraction remain open. Preserve
Sized exact classes, finite size execution, size order, both rank inverses,
the optimized interned core, and all older artifacts.

## Exact public language of the complete concrete guarded native edge pass

Proofs: `5680b122`, `062ec3e5`, and `5c15f84c`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-public-native-edge.md`. This section supersedes the complete
one-pass output annotation target below and earlier audit counts.

Actual general source merging now preserves physical annotations. The proof
includes allocating repaired comparisons, ordered cover and retention scans,
identity filtering, both retained-union branches, ordered recursive children,
the four-row threshold, original small-row guards, and literal large-row Top.
It derives every intermediate scope from actual source effects.

Captured target projection and merging, the first-seeded native right fold,
shared first forcing and reuse, and simultaneous shared edits retain that
same invariant. Fresh class captures use each actual tail-returned forest.
Closed gate selection uses its proved unchanged constructor heap. Required
paths, selected class folds, the single final propagation, checked one-pass
branches, and literal guarded-edge reconstruction derive final annotations.
No future annotation heap or whole-merge language law is supplied.

SourceEqualityPublicNativeEdge.language proves unconditional public narrowing
and exact public input/output meaning when the inherited constraints hold.
All controls are concrete source controls. Actual PCS constructor laws and
normalized annotations discharge guard readback on both sides. It assumes no
generic public conjunction law on arbitrary malformed raw stored constraints.
source_edges starts with original normalized syntax and derives finite actual
execution, both source memo certificates, final idle validity, histories,
residency, closed children, literal full labels, stable six-bound results,
and eventual bounded-array results. Only reached native word checks remain.
The singleton-storage counterexample and all previous proof boundaries remain.

All seven new modules pass focused builds. The aggregate audit passes
1,806 jobs and 47,797 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-public-native-edge-20261015-audit.log`.
Snapshot: `/tmp/mcfta-public-native-edge-checkpoint-20261015-0742/` (2,215 Lean-tree files and four root documents).
Older proofs except audit imports, all counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. The earlier
645 Haskell examples and formatter checks apply to the unchanged source and
were not rerun. Weekly allowance was 15% at 2026-10-15 07:42 CEST. Refresh it before work.
Stop all work and owned workers immediately at 1% or less.

Next connect the actual inherited reduceChildren and reducePartially caller.
Read PartialReductionCaller and lean/notes-partial-reduction-caller.md. Derive
actual combined-payload and eqConstraintsDescend readback. Follow literal
indexed child traversal, original-label setChildren, modifyNode, and the Mu
smart-constructor branch with actual returned caches. Use this concrete edge
theorem instead of supplying generic EqualityReduction.Laws. First retain
completed execution preservation and all incomplete/error observations. Do
not infer whole-caller termination from finite local passes or original cached
depth: native intersection can increase ordinary depth. Open contexts, repeated
fixed points, getAllAtPath, native containers, GHC lazy scheduling, and extraction
remain open. Preserve Sized exact classes, finite size execution, size order,
both distinct-term rank inverses, the optimized core, and all older artifacts.

## Public native intersection and physical annotations through path traversal

Proofs: `da6e72e7`, `ab156db1`, and `854bd6d3`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-native-annotations.md`. This section supersedes the native
annotation target below and earlier audit counts.

Actual compiled native calls now derive annotation continuation certificates.
Literal edge work checks its emitted guard. Node and union work emit no guard.
Optional binders use the existing actual stored-body construction theorem.
The Bounds induction follows actual direct calls, started bodies, memo hits,
completion frames, and later continuations. It derives the returned physical
annotation heap without assuming that heap or a final language law.

Concrete source native intersection preserves normalized annotations. Actual
Top and conjunction supply every emitted constraint check. The scoped native
product therefore has exact public input and public output meanings. Finite
completion follows from existing actual reached word checks. This closes the
public output readback boundary for this scoped native product only.

Actual repaired stored unfolding retains annotations even in pending outcomes.
Every bounded cold exposure retains them, including exhausted observations.
Complete head reads retain them after literal row-node reconstruction.
Required-node, child, and row graph inductions retain each original full guard.
General path projection retains annotations through selected children and the
actual final union: that union reads every operand before one node request.
Forest root, missing, and selected branches are included.

The complete equality pass still needs output annotation preservation. Do not
report public/public guarded-edge exactness yet. Next prove it through the
actual SourceMergedWorker comparison, retention, and merge requests. Lift that
proof through SourceEqualityTargetOperand, DemandTarget, shared first-force
and reuse, and SharedEditGraph. Retain original capture scopes, actual slots,
and all warm native state. Then carry annotations through source gate queries,
class folds, the one-pass worker, and literal guarded-edge reconstruction.
Use the proved PCS laws and derive public readback from each returned heap.
Do not assume a complete merge invariant, future heap, or whole-edge law.

All ten new modules pass focused builds. The aggregate audit passes
1,799 jobs and 47,752 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-native-annotations-20261015-audit.log`.
Snapshot: `/tmp/mcfta-native-annotations-checkpoint-20261015-0730/` (2,207 Lean-tree files and four root documents).
Older proofs except audit imports, all counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. The earlier
645 Haskell examples and formatter checks apply to the unchanged source and
were not rerun. Weekly allowance was 15% at 2026-10-15 07:30 CEST. Refresh it before work.
Stop all work and owned workers immediately at 1% or less.

Inherited descendant processing, reducePartially traversal, open contexts,
repeated fixed points, getAllAtPath, native containers, GHC lazy scheduling,
and extraction remain open. Preserve Sized exact classes, finite execution,
size order, both distinct-term rank inverses, the optimized interned core,
and all older proofs and boundary artifacts.

## Concrete PCS guard laws and normalized source annotation heaps

Proofs: `8fe4544e`, `50bdc097`, and `307f83be`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-normalized-annotations.md`. This section supersedes the
unrestricted guard-law target and earlier audit counts.

The existing independent PCS meaning now applies to complete source guards.
It equates distinct paths and treats trivial raw classes as vacuous. Actual
source normalization and combination preserve this meaning on all raw lists.
It agrees with public existence-sensitive indicators on active stored classes.
The singleton-storage boundary remains unchanged and still distinguishes the
meanings outside the source representation invariant.

Concrete Top, plain, and source conjunction have global laws at PCS meaning.
The native edge theorem fixes actual source predicates, Top, constraint
conjunction, and structural guard order. It supplies no generic guard laws.
Original closed construction derives stable finite guarded-edge execution,
both memo certificates, literal full labels, and exact independent PCS language
under inherited satisfaction and reached native word checks.

Annotated stored records have identical PCS and public guarded languages.
The proof includes ordinary nodes, unions, and independent least-language Mu
binders. A physical edge-record-key invariant derives all annotations from
linked available records. Safe constructor work preserves the invariant.
Original repaired construction derives it through all children, both probes,
fresh binder reservation, canonical hits, and complete or pending outcomes.
Stored-body encoding retains original guards. Actual optional source binders
therefore preserve the annotation heap without a supplied compiled-syntax law.

The normalized source entry derives own payload validity from original syntax.
It also derives exact public input readback. Its returned PCS edge language
equals the original public edge language in a satisfying inherited context.
Public readback of newly constructed outputs remains open. Do not report
identical public input/output meanings until native and shared-edit annotation
heap preservation supplies that output invariant.

All nine new modules pass focused builds. The aggregate audit passes
1,791 jobs and 47,684 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-normalized-annotations-20261015-audit.log`.
Snapshot: `/tmp/mcfta-normalized-annotations-checkpoint-20261015-0717/` (2,196 Lean-tree files and four root documents).
Older proofs except audit imports, counterexamples, marked drafts, production
source, stashes, and other worktrees remain unchanged. The earlier 645 Haskell
examples and formatter checks apply to the unchanged source and were not rerun.
Weekly allowance was 15% at 2026-10-15 07:17 CEST. Refresh it before work.
Stop all work and owned workers immediately at 1% or less.

Next prove annotation heap preservation through actual completed native calls
and shared edits. Use SafeWork for literal edge/node/union effects and the
stored-syntax optionalBinder theorem. Concrete conjoin always derives cached
output classes; source empty-edge Top is cached. Follow the existing native
Bounds.semantic_heap proof with an annotation-specific continuation certificate.
Retain actual compiled jobs, reached cache scopes, and memo hits. Then carry
the invariant through projections, required paths, target merge, and class edits.
Derive public output readback and public/public guarded-edge exactness. Do not
assume the output annotation invariant or a whole-edge language law. Inherited
descendant processing, reducePartially traversal, open contexts, repeated fixed
points, getAllAtPath, native containers, GHC lazy scheduling, and extraction
remain open. Preserve Sized exact classes, finite execution, size order, both
distinct-term rank inverses, the optimized core, and all older artifacts.

## Guarded-edge reconstruction and actual guard readback

Proofs: `5ac49f0a`, `dbd22112`, and `70d3e67c`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-guarded-edge.md`. This section supersedes the guarded-edge
reconstruction target and earlier audit counts.

Actual sourceEqualities now derives valid physical records from cached
normalized payloads. Complete guard acceptance implies their independent
own-class satisfaction, including residual guards. No guard-to-payload law
or completed pass is supplied. Source normalization, the empty shortcut,
combination, and the accessor derive coherent nontrivial canonical classes.

The guarded-edge worker runs the actual accessor and complete native pass,
then literal makeEdge with the original symbol and complete constraint.
Accessor errors, child errors, and incomplete child observations retain their
actual scope. Complete graphs and successful bounded workers agree in both
directions. Every complete graph supplies six stable stage bounds and an
additional eventual array bound. Results and full native states are unique.
Original closed construction derives finite execution, both source memo
certificates, final idle validity, histories, residency, and closed children.

The independent edge theorem narrows unconditionally. It gives exact language
under inherited satisfaction and the existing native guard-constructor laws.
Actual own validity and satisfaction come from the accessor. The new source
entry combines this theorem with finite original construction. The local
clear/top/conjunction contracts remain explicit; they are not yet discharged
for all actual reached source guards.

Concrete source Top, plain, and conjoinConstraints laws are now proved.
The conjunction and plain truth laws require normalized stored operands.
A checked singleton-storage boundary shows why the invariant matters:
normalization discards a malformed singleton's existence test. Therefore do
not instantiate the generic unrestricted guard laws with arbitrary raw
Constraint values. The concrete normalized laws do not establish those
unrestricted premises. This remains a source-correspondence obligation.

Kernel checks retain reflexive Same as residual, unchanged mixed children,
immediate inherited contradiction, original complete labels, actual final
edge allocation, and unchanged native memo counters. All ten new modules pass
focused builds. The aggregate audit passes 1,782 jobs and 47,576 dependency
checks using only propext, Classical.choice, and Quot.sound. Only the older
unused inputs warning remains. Log: `/tmp/mcfta-guarded-edge-20261015-audit.log`.
Snapshot: `/tmp/mcfta-guarded-edge-checkpoint-20261015-0704/` (2,186 Lean-tree files and four root documents).
Older proof bytes except audit imports, all counterexamples, marked drafts,
production source, stashes, and other worktrees remain unchanged. The earlier
645 Haskell examples and formatter checks apply to the unchanged source.
Weekly allowance was 16% at 2026-10-15 07:04 CEST. Refresh it before work.
Stop all work and owned workers immediately at 1% or less.

Next carry normalized stored-constraint invariants through original source
annotations, constructor-cache growth, shared edits, and native intersection.
Restrict generic language guard premises to actual reached guards. Use the
concrete constructor laws to discharge those premises at each actual prefix.
Do not assume unrestricted conjunction on malformed raw payloads. Then
compose inherited descendant processing and the complete reducePartially
traversal. Open contexts, repeated fixed points, getAllAtPath, native containers,
GHC lazy scheduling, and extraction remain open. Preserve exact Sized classes,
finite execution, size order, both distinct-term rank inverses, the optimized
interned core, and all older proofs and boundary artifacts.

## Complete guarded native one-pass worker

Proofs: `565ea4a4`, `b859a782`, and `ed3568fe`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-native-one-pass.md`. This section supersedes the combined
one-pass worker target and earlier completion counts.

An executable physical-record selector now produces exact actual query
receipts in source order. Its successful runs and the existing gate traces
agree in both directions. Every complete trace has finite stable query bounds.
Selected physical records retain original occurrences and exact source paths.

The combined worker now runs actual prechecks, physical record selection,
required paths, fresh class-local target captures, native right folds, and one
final propagation. Unchanged returns bypass propagation. Contradiction erases
all original child positions immediately. Checked errors and incomplete
selection, required, and narrowing results retain their exact observations and
full current scope. No enclosing-control resumption is asserted.

Checked successful workers and full pass graphs agree in both directions.
Every complete graph derives six independent stable bounds: gate, edit,
projection/required recursion, head reads, comparison, and native requests.
All larger tuples return the identical answer and full native state. Complete
answers are unique. Actual parent-array normalization supplies an additional
finite bound. At every larger array bound, its entry has the same stable
source answer. These are explicit worker/function graphs, not GHC extraction.

The pass retains native validity, semantic heaps, histories, and closed outputs.
Actual combined normalization rejects no term that satisfies both input
payloads. Under coherent nontrivial own records, independent language laws
prove output inclusion and preservation of every accepted forest term that
satisfies both original own and inherited payloads. Own payload validity is
still explicit; its derivation from the original guard accessor is next.

Original closed construction now derives complete finite one-pass source
execution for every precheck branch. Initial native validity comes from the
actual constructor heap. The live branch retains certificates for both actual
source gate memo call graphs and their returned cache validity. Only actual
reached native word checks remain explicit. No completed whole-pass or global
callback law is supplied.

Kernel checks retain immediate unchanged, contradiction, checked-error, and
live-empty behavior. A complete ordinary fixture uses a proved normalization
guard and actual selection, required paths, target demands, native work, and
final propagation. Larger bounds and repeated warm runs retain one native
node memo cell and identical full native states. A local cbv_eval lemma proves
the fixture entry equality; it avoids expanding a large normalization proof
inside the full fixture. General array agreement is proved for all sufficient
array bounds, rather than by one brute-force fixed-bound evaluation.

All eleven new modules pass focused builds. The aggregate audit passes
1,770 jobs and 47,483 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-one-pass-20261015-audit.log`.
Snapshot: `/tmp/mcfta-one-pass-checkpoint-20261015-0647/`
(2,175 Lean-tree files and four root documents). All older proof bytes except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees remain unchanged. The earlier 645 Haskell examples and
formatter checks apply to the unchanged source and were not rerun.
Weekly allowance was 16% at 06:46 CEST. Refresh it before work. Stop all work
and owned workers immediately at 1% or less.

Next connect actual guarded-edge rebuilding. Keep the original symbol and
complete guard in makeEdge. Derive the own physical class payload and its
validity from the actual Constraint.equalities/sourceEqualities readback.
Derive that accepted source guards imply the required own ClassSat facts;
do not supply a whole-edge language law or assume a guard-to-payload law.
Use SourceCompactGuards.sourceEqualities, positiveNormalized_support, the
normalization laws, record construction, and the complete one-pass language
bounds. Keep inherited satisfaction explicit as the surrounding context.
Then prove exact independent guarded-edge language and stable native edge
execution from original construction. Open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
open. Preserve exact Sized contracts, both rank inverses, the optimized core,
and all older constructor/equality work and boundary artifacts.

## Selected class right fold and final empty propagation

Proofs: `fe3c4cc4`, `b0c47ec2`, and `2d7eced9`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-selected-class-fold.md`. This section supersedes the class-fold
composition target and earlier completion counts.

Source correction: Equality/Operations.hs applies propagateEmptyNodes once
after the complete foldr reduceEClass. Earlier restart guidance incorrectly
placed it after each class. The new graph and worker retain the source order.
Each class captures the actual forest returned by the completed tail. It starts
fresh target slots and retains the same full warm native state. Returned target
slots are shared within that class. They are not reused by the next class.
Final literal empty propagation has no constructor or native effect and
preserves the complete independent ordered forest language exactly.

Actual-prefix range plans and local shared edit completion derive finite
class folds. No completed fold, future-cache law, or global callback language
law is supplied. Every completed graph derives five independent finite edit
and target bounds. Every larger tuple returns the same forest and full native
state. Checked successful workers and complete pass graphs agree in both
directions. Fold and fold-and-propagate results are unique. Incomplete class
observations retain the actual captured forest and shared worker stage.

Physical source selection now keeps the original aligned records, including
repeated clear occurrences. Their paths equal the selected query paths.
Required paths run on the original forest and return their actual heap.
Derived cache histories advance that heap in the same native state without
resetting domain or native memo tables. Native initialization derives idle
validity from the actual semantic constructor heap and empty domain cache.

The selected live branch now composes actual gate/required receipts, selected
physical class folds, and final propagation. It narrows the original forest
and retains every accepted term satisfying the selected classes. Under all
original class constraints, before and after forest membership are equivalent.
Original closed source construction derives finite complete selected processing,
actual source gate memo receipts, stable gate and required-path bounds, and
stable five-bound native fold execution from reached native word checks.
The final whole one-pass executable entry remains to be composed.

Kernel checks verify rightmost-first class order, fresh slots for each repeated
class, one retained warm native node cell, identical larger-bound results,
ordered repeated record selection, and final-only empty propagation. A repeated
class with zero projection bounds attempts its own first target demand even
when the native memo is warm. This distinguishes class-local sharing from
incorrect cross-class target reuse.

All fourteen new modules pass focused builds. The aggregate audit passes
1,759 jobs and 47,301 dependency checks using only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-selected-class-fold-20261015-audit.log`.
Snapshot: `/tmp/mcfta-selected-fold-checkpoint-20261015-0625/`
(2,163 Lean-tree files and four root documents). Older proofs are unchanged
except audit imports. Repros, counterexamples, marked drafts, production source,
stashes, and other worktrees are unchanged. The earlier 645 Haskell examples
and formatter checks apply to the unchanged source and were not rerun.
Weekly allowance was 16% at 06:24 CEST. Refresh it before work. Stop all work
and owned workers immediately at 1% or less.

Next implement the physical-record selection worker and connect the whole
one-pass native entry. Retain actual precheck/array normalization, unchanged
and contradiction fast paths, selection and its two memos, required paths,
class-local captures, the native right fold, and one final propagation. The
unchanged fast path must not propagate preexisting empty children. Derive
checked function/graph agreement and stable finite bounds for all phases.
Then prove exact original guarded-edge language with the guard unchanged.
Keep actual request word checks explicit. Full one-pass Haskell correspondence,
open contexts, repeated fixed points, getAllAtPath, native containers, GHC lazy
scheduling, and extraction remain open. Function/graph agreement is for these
explicit workers; it is not verified GHC heap extraction. Preserve exact Sized
contracts, both rank inverses, the optimized interned core, all older constructor
and equality work, and all boundary artifacts.

## Shared target closures through actual class edit leaves

Proofs: `c0aa73c6`, `cf98225d`, and `cb8b675a`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-shared-class-edits.md`. This section supersedes the
standalone shared-target forcing target and earlier completion counts.

Each class captures its original input forest once. A logical shared state
retains the actual full native state and a partial table of returned target
values. An empty slot is unforced. A first force runs the actual demanded
target graph at its current warm native state and stores its physical result.
A hit returns that same value and the identical full shared state. Construction
receipts derive closed target availability when each leaf reaches it. No eager
all-target scope or global callback language law is supplied.

Simultaneous edits retain this target table through every native request,
recursive head read, ordered child scan, row constructor, and final node.
Returned slots never change. Every later force of a returned slot must reuse
its exact earlier physical value. Native validity, idle warm tables, semantic
constructor heaps, captured scope, closed output scope, and cache histories
hold at each actual completed prefix.

Actual-prefix range checks derive first-force and native leaf completion.
Finite source control and general head completion derive finite edit graphs.
The executable edit worker has five independent bounds: edit recursion,
projection recursion, head reads, comparison, and native requests. Successful
checked runs and complete graphs agree in both directions. Every complete
graph has stable identical values and entire shared state at all larger bound
tuples. Completed graphs have unique values and full returned shared states.
Incomplete observations retain the actual stage; outer resumption is separate.

The actual signed source compiler stores original natural class paths as
leaf tokens. Coherent nontrivial classes derive valid supported original
paths. Independent language bounds show that every output term belonged to
the input forest. Every accepted original term that satisfies the class
survives. Under ClassSat, original and edited forest acceptance are equivalent.
The proof derives local target inclusion from actual first-force receipts.
It does not claim that one class edit enforces all original equalities.

Kernel checks use a coherent two-path class over two-row nodes. Four physical
leaves share two first-forced target slots and one warm native node memo cell.
Later row visits use the stored targets. A repeated batch completes with zero
projection, head-read, and comparison bounds, with identical full native state
and slots. Missing signed positions and ignored list-root callbacks force no
target. Cache hits work at zero bounds for all four target stages.

All eighteen new modules pass focused builds. The aggregate audit passes
1,745 jobs and 47,143 dependency checks with only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-shared-class-edits-20261015-audit.log`.
Snapshot: `/tmp/mcfta-shared-class-checkpoint-20261015-0611/`
(2,148 Lean-tree files and four root documents). Older proofs are unchanged
except audit imports. Repros, counterexamples, marked drafts, stashes, other
worktrees, and production source remain unchanged. The earlier 645 Haskell
examples and formatter checks apply to the unchanged tree and were not rerun.
Weekly allowance was 16% at 06:10 CEST. Refresh it before work. Stop all work
and owned workers immediately at 1% or less.

Next compose actual selected classes in their source ordered right fold.
Each class must capture the current forest returned by the later classes,
start its own unforced slots, and retain the same actual native state. Model
literal structural empty propagation once after the complete fold. Use the existing
class ordering, selected/required-path graphs, shared class completion, and
language bounds. Derive actual-prefix checks instead of assuming whole-fold
completion or a future cache law. Then connect the complete one-pass worker.
Full one-pass source correspondence, open contexts, repeated fixed points,
getAllAtPath, native containers, GHC lazy scheduling, and extraction remain
open. The shared slots are an explicit demand graph, not verified GHC heap
extraction. Preserve exact Sized contracts, both rank inverses, the optimized
interned core, all older constructor/equality proofs, and every boundary artifact.

## Demanded original class targets and constructed native edits

Proofs: `e38dc119`, `388f111b`, and `92d59cfd`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-demanded-class-targets.md`. This section supersedes the
standalone original class-target construction target.

A demanded operand now performs actual captured-forest projection and
general merging inside the existing full native state. Both stages retain
the actual domain and native memo tables. Local completion derives every
closed operand. Proper-path inclusion retains each accepted selected subterm.
The target graph interleaves these demands with actual native intersections.
It uses the source first path as seed and folds the remaining paths from
right to left. Left operands are demanded before their tails. The seed is
demanded at the base. It does not prepare all operands before the fold.

Actual-prefix FoldRanges and TargetRanges check native words only after
actual operand and recursive fold receipts. Local operand and idle warm
native progress derive complete finite target graphs. The executable worker
keeps projection, head-read, comparison, and native-request bounds separate.
Checked successful runs and complete graphs agree in both directions. Every
complete graph supplies stable identical targets and full native states at
every larger bound quadruple. Complete target results are unique. Incomplete
stage observations remain literal; outer control resumption is not asserted.

Original coherent nontrivial physical classes derive proper nonempty target
operand lists. Every target uses the ordered other original class paths.
Equality-satisfying original subterms remain accepted by their constructed
targets. Constructed receipt witnesses derive target availability and closedness
at a common retained edit base. Native class edits with those constructed
targets have finite stable execution from actual-prefix word checks. For terms
that satisfy the original class, edited forest acceptance equals original
forest acceptance. No whole-target language or global leaf law is supplied.

Kernel checks verify the empty target and the second/third/first operand
demand order. Three actual projections and merges on a constructed constant
feed two native intersections. One warm node memo cell remains. Larger bound
quadruples and repeated demand return the identical value and full native state.

The aggregate audit passes 1,727 jobs and 46,889 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs
warning remains. All twelve new modules pass focused builds.
Log: `/tmp/mcfta-demanded-targets-20261015-audit.log`.
Snapshot: `/tmp/mcfta-demanded-targets-checkpoint-20261015-0546/`
(2,129 Lean-tree files and four root documents). Older proofs are unchanged
except audit imports. Repros, counterexamples, marked drafts, stashes, other
worktrees, and production source are unchanged. No Haskell source changed.
The earlier 645 examples and formatter checks apply to the unchanged tree
and were not rerun. Weekly allowance was 16% at 05:46 CEST.
Refresh before work. Stop all work at 1% or less.

Next model the shared target closures through actual native edit leaves.
Capture each class input forest once. First force must run the demanded
target graph and store its physical value; later leaves must reuse that
value. Derive construction receipts at actual prefixes instead of assuming
all targets were forced before editing. Then compose the selected classes'
ordered right fold and structural empty propagation with the existing
selected/required-path graphs. Shared target forcing, full one-pass source
correspondence, open contexts, repeated fixed points, getAllAtPath, native
containers, GHC lazy scheduling, and extraction remain open. Keep word checks
explicit. Preserve exact Sized contracts, both rank inverses, the optimized
interned core, and all older proof and counterexample artifacts.

## Finite general repaired comparison and merge execution

Proofs: `bee799da`, `752b5b91`, and `f45607e6`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-merged-finite.md`. This section supersedes earlier general
comparison and merge completion targets and older module header comments.

Every successful actual comparison now retains the fixed maximum Mu degree.
It either reduces the finite vector of unfinished Mu degrees or returns the
identical cache. The general reader derives this progress. Ordered stages
compose it through actual prefix states. Allocating prefixes reduce that
vector. Unchanged prefixes let a fresh ancestor pair reduce the finite
issued-pair allowance. This measure derives general recursive comparison
completion without Prepared, NoNewMu, a future-cache run, or a supplied
whole-comparison completion law. Every larger comparison bound returns the
identical Boolean and complete actual cache. Successful results are unique.

Actual general child selection, retained columns, small and large rows,
ordered groups, and final nodes now have stable finite bounds. Ordinary
height derives all recursive merge calls. Every closed available input has
finite SourceMergedWorker execution. It retains SemanticReady, both cache
histories, and a closed available result. Increasing either proof bound
preserves every completed value and full actual cache. SourceMergedAPI
combines completion with independent input-language inclusion. Original
closed construction derives every premise. Merge inclusion remains distinct
from the exact child-selection union language. No whole-merger law is given.

A kernel check constructs five rows with one nested-Mu child and four
ordinary children. Actual selection allocates a Mu record. The result keeps
one merged edge and its five-member recursive union boundary. Increasing
both bounds returns the identical value and complete cache.

The aggregate audit passes 1,715 jobs and 46,736 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs
warning remains. All twelve new proof modules pass focused builds.
Log: `/tmp/mcfta-merged-finite-20261015-audit.log`.
Snapshot: `/tmp/mcfta-merged-finite-checkpoint-20261015-0529/`
(2,116 Lean-tree files and four root documents). Older proofs are unchanged
except added audit imports. All repros, counterexamples, marked drafts,
stashes, other worktrees, and production source remain unchanged. No Haskell
source changed. The earlier 645 examples and formatter checks apply to the
unchanged tree and were not rerun. Weekly allowance was 17% at
05:29 CEST. Refresh before work. Stop all work at 1% or less.

Next construct actual original equality-class targets from getPath, general
merging, and the first-seeded native intersection list. Derive retained
equality-satisfying subterms and captured physical target availability from
actual returned caches. Reuse SourceMergedAPI.complete/source and actual
projection inclusion. Connect NativeClassEdits to actual selected classes,
the ordered class right fold, and empty propagation. Keep shared lazy target
forcing explicit. Full one-pass source correspondence, open contexts,
repeated fixed points, getAllAtPath, native containers, scheduling, and
extraction remain open. Preserve exact Sized classes, size order, both
distinct-term rank inverse laws, the optimized interned core, and older proofs.

## General repaired comparison and successful merge coverage

Proofs: `ebb463b7`, `a58070e7`, and `4522dd07`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-merged-general.md`. This section supersedes earlier targets
for independent merger inclusion and semantic cache preservation.

The actual repaired comparison now preserves all semantic heaps and both
constructor histories on every successful closed available call. A true
comparison implies independent guarded least-language inclusion. Induction
on finite term height justifies visited pairs. Ancestors retain coherent
physical witnesses through every actual intermediate cache. No Prepared,
NoNewMu, unchanged-cache, or whole-comparison language premise is supplied.

Actual child selection retains every original closed Mu operand. Any removed
child has an original retained cover. Identity deduplication retains complete
coherent payloads. The returned list has exactly the original union language.
SourceMergedWorker uses this actual repaired filter. It keeps source group
order, complete symbol and arity classes, the four-row threshold, full small
row guards, large Top guards, and singleton and recursive union boundaries.
Every successful bounded merge preserves SemanticReady, cache histories,
closed availability, and independent input-language inclusion. Ordinary
recursion derives its local certificates. No whole-merger law is supplied.

Original closed construction derives all entry premises. Actual getPath
followed by a successful merge retains each accepted selected subterm at its
literal source path and actual returned cache. Merge coverage is inclusion.
The child-selection union language is exact. These are separate contracts.

Finite completion and stable identical results and full caches for the
GENERAL repaired comparator and merger remain open. Older
MergedColdMergeSoundness completion requires Prepared Mu bodies. It cannot
close this general obligation. A kernel example constructs a nested binder
whose demanded comparison read allocates a new Mu record. Further kernel
checks verify the four/five-row threshold and zero ordinary-fuel exhaustion.
The older MergedFreshOrdinarySelection.lean.incomplete draft is unchanged.

The aggregate audit passes 1,703 jobs and 46,553 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs
warning remains. All fifteen new proof modules pass focused builds.
Log: `/tmp/mcfta-merged-general-20261015-audit.log`.
Snapshot: `/tmp/mcfta-merged-general-checkpoint-20261015-0514/`
(2,103 Lean-tree files and four root documents). Older proofs are unchanged
except added audit imports. Repros, counterexamples, marked drafts, stashes,
other worktrees, and production source remain unchanged. No Haskell source
changed. The earlier 645 examples and formatter checks apply to that unchanged
tree and were not rerun. Weekly allowance was 17% at 05:14 CEST.
Refresh the allowance before work. Stop all work at 1% or less.

Next prove finite general repaired comparison completion and stable bounds.
Retain actual read order, fresh Mu allocations, visited physical pairs, and
full returned caches. Use the existing complete general cold reader and its
replay laws. Do not replace the actual worker with an eager future-cache run,
and do not assume whole-comparison or whole-merger completion. Then derive
finite stable SourceMergedWorker execution by ordinary height. After that,
construct original class targets from getPath, merging, and first-seeded
native intersection lists. Connect captured native class edits to actual
selected classes, the ordered class right fold, and empty propagation.
Shared lazy target forcing, full one-pass source correspondence, open
contexts, repeated fixed points, getAllAtPath, native containers, scheduling,
and extraction remain open. Preserve exact Sized classes, size order, both
distinct-term rank inverses, the optimized interned core, and older proofs.

## Scoped simultaneous native edits and original class paths

Proofs: `b2e5fd76`, `f110cc11`, `6dc38a2b`, and `8cc092ee`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`, with retained
traversal repair `61f2c939`. Continue on `formalize` and push checkpoints.
Read `lean/notes-native-edits.md`. This section supersedes the scoped
simultaneous edit traversal and captured-target class edit targets.

Native node, child, row, and list graphs now retain the full native state.
Leaves execute actual checked native intersections with captured physical
targets. Every head, edge, and node effect advances the same state. Domain
and both memo tables remain at their actual values. Scoped graph induction
derives native validity, idle memos, all semantic heaps, cache histories,
closed available values, and resident complete row payloads. Captured target
availability follows from its actual earlier base cache through Keeps.

Independent language is exact input language intersected with retained
physical-target conditions. Actual native leaf language and complete
constructor readback derive this law. No global callback LeafLaw or
whole-worker language law is supplied. The older conditional theorem remains.
Signed missing positions, root-list callback suppression, full guards,
row order, and actual recursive head normalization remain in the graph.

Actual-prefix NodeRanges, ChildrenRanges, and RowsRanges state native word
checks only. Later checks use actual completed earlier graphs and their
full returned states. They supply no callback or edit completion law.
Local idle warm progress, complete heads, and finite control derive complete
edit graphs from these checks. The machine-word premises remain explicit.
The native worker separates recursion, head-read, and native-request bounds.
Checked successful workers and complete graphs agree in both directions.
Every complete graph supplies stable identical values and full native states
at every larger bound triple. Completed node and list graphs are unique.
An incomplete native leaf retains its exact observation; outer-worker resume
and native lazy scheduling are not asserted.

The actual signed right-fold compiler derives captured scope from original
edit pairs. Nonoverlapping nonroot pairs have exact original complete-path
readback. Coherent nontrivial physical classes derive those path premises.
NativeClassEdits.class_complete derives finite stable class edits and exact
conditions at the original natural paths for already captured physical
targets. It does not yet construct those targets from getPath and merging.
Shared lazy target forcing remains a separate implementation obligation.

The aggregate audit passes 1,688 jobs and 46,352 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All eleven new modules pass focused builds. Kernel checks cover
leaf/list priority, missing signed positions, raw self normalization, both
exhausted traversal bounds, and one actual warm memo cell reused by two edit
positions and a later repeated batch.
Log: `/tmp/mcfta-native-edit-20261015-audit.log`.
Snapshot: `/tmp/mcfta-native-edit-checkpoint-20261015-0443/`
(2,087 Lean-tree files and four root documents). Older proofs are unchanged
except added audit imports. All repros, counterexamples, marked drafts,
stashes, other worktrees, and production source remain unchanged.
No Haskell source changed. The earlier 645 examples and formatter checks
apply to the unchanged tree. Weekly allowance was 17% at
04:43 CEST; refresh before work. Stop all work at 1% or less.

Next derive actual mergeAlternatives independent-language inclusion and
SemanticReady preservation. Reuse existing MergedColdMergeSoundness finite
prepared common-cache graph proof, but derive the independent-language and
closed source entry connection. Do not supply a whole-merger law. Then derive
actual class target construction from getPath, merging, and the first-seeded
native intersection list. Establish retained equality-satisfying subterms and
captured target availability. Connect NativeClassEdits to the actual selected
classes, ordered right fold, and empty propagation. Full one-pass source
correspondence, open contexts, repeated fixed points, getAllAtPath, native
containers, lazy scheduling, and extraction remain open. Preserve exact Sized
contracts, the optimized interned core, and the completed unary ancestor proof.

## Scoped warm native state and exact target intersection lists

Proofs: `69de4363`, `e03f2c4d`, and `e145fe27`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-native-target-fold.md`. This section supersedes first-request-only
native leaf completion and the general intersection-list target obligations.

IdleReady retains actual native validity, idle memo tables, and complete
semantic constructor heaps. Actual constructor growth advances this same
native state. It preserves the domain cache and both native memo tables.
Closed available operands derive Original syntax. Existing idle warm progress
supplies finite native leaf completion. Each successful request derives all
next-call premises, exact intersection language, closed available results,
and stable identical full native states at every larger request bound.

The source intersectList uses its first operand as seed and folds its tail
from right to left. Empty input returns EmptyNode. Its concrete graph and
worker now retain each actual intermediate native state. Completion follows
from finite list length and local warm request completion. Exact independent
language is the conjunction of all operands for nonempty lists; it is false
for an empty list. Checked worker execution and graphs agree in both directions.
Complete graphs have a unique result and full final native state. Captured
operands remain available from their actual earlier base cache through Keeps.

Word-range checks refer only to actual completed tail graphs and their returned
states. They do not require a law on unrelated caches or reset memo tables.
These machine-bound premises remain explicit. A common proof bound instruments
each native request; it is not a new API parameter or whole-fold resume claim.

General forest projection now advances this retained native state. All initial
and final cache premises, stable execution, and accepted-subterm inclusion
follow from the completed general getPath proof. Domain and both memo tables
remain equal across projection. Actual target-list construction followed by
one actual narrowing request derives exact input-and-target-conjunction
language and finite completion in the same native state. The graph describes
one target construction and application; shared repeated target forcing and
the full simultaneous edit traversal remain separate caller obligations.

The aggregate audit passes 1,677 jobs and 46,148 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All six new modules pass focused builds. Kernel checks verify empty
and singleton shortcuts, first-seeded right-fold order, and actual warm reuse
of one returned node memo cell across two- and three-operand folds.
Log: `/tmp/mcfta-native-target-20261015-audit.log`.
Snapshot: `/tmp/mcfta-native-target-checkpoint-20261015-0424/`
(2,075 Lean-tree files and four root documents). Older proofs are unchanged
except added audit imports. Repros, counterexamples, marked drafts, stashes,
other worktrees, and production source remain. No Haskell source changed;
the earlier 645 examples and formatter checks apply to the unchanged tree.
Weekly allowance was 17% at 04:24 CEST; refresh before work.
Stop all work at 1% or less.

Next carry scoped IdleReady and captured target availability through actual
simultaneous edit node, child, and row operations. Use actual native Step
receipts and advanceHeap for constructor effects. Preserve full native state
and actual leaf word checks. The global LeafLaw still quantifies unrelated
caches and is not an instantiation for arbitrary captured native targets.
Derive actual mergeAlternatives independent-language inclusion and semantic
cache preservation. Existing MergedColdMergeSoundness covers finite prepared
common-cache graph language, not this final independent language/caller law.
Then connect original class targets, class edit batches, ordered class folds,
and empty propagation. Full one-pass correspondence, open contexts, repeated
fixed points, getAllAtPath, native containers, lazy scheduling, and extraction
remain open. Preserve exact Sized contracts and the optimized interned core.

## General closed getPath execution and subterm inclusion

Proofs: `587c633a`, `eb094eb9`, and `3dd8ee3b`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-general-projection.md`. This section supersedes the general
closed getPath and forest-root union targets in the older edit note.

Actual closed source union reads nodeEdges for each operand, concatenates
its exposed rows, and makes one ordinary node. It does this even for a
singleton recursive operand. The proof retains every actual read and cache.
It does not replace this branch by createUnion or stored ordinary rows.
Each read and the whole closed union derive exact independent language,
semantic heaps, complete histories, resident rows, and closed results.

General signed getPath now has complete physical node, row, and forest
graphs. Finite path length and completed head normalization derive finite
execution on arbitrary closed available nested Mu/Union values. Original
source construction derives every initial premise. Successful bounded runs
and complete graphs agree in both directions. Each graph has one result and
full final cache. Every larger pair of worker and read bounds returns both
unchanged. Pending, unresolved, and the two exhausted bounds stay distinct.

Every existing subterm of an accepted original term is accepted by its
actual projection. Proper forest paths retain the original accepted child
forest. Forest root projection has exact union language. Projection discards
ancestor guards, so its general language contract is inclusion. Root node
lookup keeps source identity priority. Negative and missing signed positions
retain source behavior. Kernel checks cover bare references, missing forest
positions, the raw closed self binder, both exhausted bounds, and actual
singleton closed forest union.

The aggregate audit passes 1,671 jobs and 46,049 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All eleven new modules pass focused builds. No Haskell source changed;
the earlier 645 examples and format checks apply to the unchanged tree.
Log: `/tmp/mcfta-projection-20261015-audit.log`.
Snapshot: `/tmp/mcfta-projection-checkpoint-20261015-0413/`
(2,068 Lean-tree files and four root documents). The only older proof change
is added audit imports. All repros, counterexamples, marked drafts, stashes,
other worktrees, and production source remain. Weekly allowance was 17%
at 04:13 CEST; refresh before work. Stop all work at 1% or less.

Next derive scoped callback composition and actual merged/intersection-list
targets. Carry captured target availability from its real base cache through
Keeps. Retain the full native memo/domain state and checked word ranges at
each request. Reuse SourceEqualityNativeLeaf.done, complete, captured_target,
and the new general projection API. Do not instantiate the global LeafLaw
for arbitrary unrelated caches. Merge has inclusion; intersection is exact.
Then compose actual class edit batches, the ordered class right fold, and
empty-child propagation. Reuse the completed unary ancestor theorem.
getAllAtPath, open contexts, complete one-pass correspondence, repeated
fixed-point reduction, native containers, lazy scheduling, and extraction
remain separate. Preserve exact Sized laws and the optimized interned core.

## Exact edit languages, original paths, and native leaf effects

Proofs: `c6f33d9d`, `172ce399`, and `6359b4a4`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-edit-language.md`. This section supersedes the independent edit
language and nonoverlapping compiled-path readback targets.

Actual completed node, child, and row edit graphs now derive exact independent
language filtering from stored leaf completion and narrowing laws. The node
result accepts exactly its original terms that satisfy the retained leaf
conditions. Intermediate cache premises follow from verified graph effects.
Actual head normalization, complete edge guards, ordered children, and canonical
constructor readback remain. Signed negative and missing positions are no-ops.
The compiled list entry keeps its ignored root-leaf branch. Original closed
source construction derives stable execution and exact node/forest language.

Retained leaves have complete signed path readback. Nonoverlapping insertion
adds exactly one callback occurrence. Actual right-fold compilation preserves
every original occurrence for pairwise nonoverlapping edits. The independent
condition is therefore exactly each original callback condition at its existing
complete path. No arity or nonnegative-key premise is added. Coherent nontrivial
physical equality classes derive disjoint nonroot edit paths. Natural-to-signed
conversion retains both prefix and complete lookup readback. Raw prefix and
duplicate inputs still retain their earlier source shadowing behavior.

Actual checked native intersection requests now derive the immediate edit cache
invariants and exact input-intersection-target language. Closed available inputs
derive original syntax. The result retains semantic heaps, coverage, depth,
both histories, availability, and closedness in its actual returned native
state. The theorem covers successful warm requests. First requests also have
derived finite stable execution. Captured-target availability follows through
earlier actual cache growth. No runtime table conversion is added.

The generic LeafLaw still quantifies all semantic-ready caches. The concrete
native theorem has actual operand availability, native memo validity, and
checked word ranges. These premises are not interchangeable. A captured target
need not exist in an unrelated cache. Do not claim that the global LeafLaw
has been instantiated for arbitrary captured native targets. The next caller
proof must retain the target's cache scope and the actual native memo state.

The aggregate audit passes 1,662 jobs and 45,923 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All seven new modules pass focused builds. No Haskell source changed;
the earlier 645 examples and format checks apply to the unchanged tree.
Log: `/tmp/mcfta-edit-language-20261015-audit.log`.
Snapshot: `/tmp/mcfta-edit-language-checkpoint-20261015-0358/`
(2,056 Lean-tree files and four root documents). The only older proof change
is added audit imports. Repros, counterexamples, marked drafts, stashes, other
worktrees, and production source remain unchanged. Weekly allowance was 17%
at 03:58 CEST; refresh before work.

Next derive scoped callback composition through actual edit traversal. Retain
captured-target availability through Keeps, native memo/domain state, and word
ranges at every actual request. Reuse SourceEqualityNativeLeaf.done, complete,
and captured_target. Derive the actual getPath and merged-target contracts,
then intersection-list and original class edit callbacks. Keep merge inclusion
distinct from equality and preserve exact accepted terms. Compose the ordered
class right fold and empty propagation. Full one-pass correspondence, open
contexts, repeated fixed-point reduction, native containers, lazy scheduling,
and extraction remain open. Preserve exact Sized laws, older constructor and
equality proofs, and the optimized interned core. Stop all work at 1% or less.

## Finite signed simultaneous edit execution

Proofs: `5635846d`, `28bf4f0e`, and `96653514`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-edit-execution.md`. This section supersedes the edit compiler,
finite edit-depth recursion, and graph/execution agreement targets.

The actual signed Edits compiler now retains the source right fold,
empty-path replacement, ancestor-leaf shadowing, and duplicate-path priority.
Construction derives ascending unique maps and every retained leaf property
from original edit pairs. Independent leaf conditions apply only to present
term positions. Their ordered scan and the source signed right fold agree.
Negative and missing positions impose no condition.

Physical node, child, row, and list graphs retain actual callback equations,
head normalization, complete edge guards, and exact returned caches. Node
leaves execute before inspecting empty or reference inputs. List leaves
return unchanged without calling the callback. A below-node has no empty-map
identity shortcut. Every original row is rebuilt without an arity rejection.
The worker retains pending, unresolved, worker exhaustion, and head-read
exhaustion as separate outcomes. Native lazy scheduling remains separate.

Finite edit-trie size derives complete graphs from explicit leaf callback
completion contracts. Actual constructors and complete closed head exposure
derive every other cache premise. Successful bounded runs give exact graphs.
Every completed graph supplies stable worker and head-read bounds; every
larger pair returns the same result and complete final cache. Execution
uniqueness derives final semantic heaps, histories, and closed/resident outputs
for every successful graph. Original closed construction derives initial
premises for node edits and compiled source-edge list edits.

The leaf callback contract is still explicit. It includes its own finite
completion and actual semantic cache effects. Worker bounds do not bound
the callback's internal work. This is not yet a proof of the concrete
equality intersection/projection callbacks or the full reduction pass.
Kernel fixtures check the actual raw self binder, both exhausted bounds,
node/list leaf priority, and ignored negative/high child positions.

The aggregate audit passes 1,655 jobs and 45,879 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the older unused inputs warning
remains. All nine new modules pass focused builds. No Haskell source changed;
the previous 645 examples and formatter checks apply to the unchanged tree.
Log: `/tmp/mcfta-edit-execution-20261015-audit.log`.
Snapshot: `/tmp/mcfta-edit-execution-checkpoint-20261015-0342/`
(2,048 Lean-tree files and four root documents). The only older Lean proof
change is added audit imports. Repros, counterexamples, drafts, stashes, and
other worktrees remain unchanged. Weekly allowance was 18% at
03:42 CEST; refresh before work.

Next derive the actual edit language law from per-leaf narrowing contracts.
For a valid edit trie, closed available input, and semantic-ready cache,
prove meaning result term iff meaning input term and the independent
SourceEqualityEditMeaning.Matches condition edits term. Use node_verified,
children_verified, rows_verified, head_exact, and forest_zero. Do not supply
a whole-worker language law. Then connect compiled conditions to original
nonoverlapping edit paths and derive the actual intersection, getPath,
merged-target, and leaf completion contracts. Reuse existing physical proofs
and the completed unary ancestor theorem. Keep merge over-approximation
distinct from equality. Compose the class right fold and empty propagation.
Full one-pass correspondence, open contexts, fixed-point reduction, native
containers, lazy scheduling, and extraction remain open. Preserve exact Sized
contracts and the optimized interned core. Stop all workers and work at 1% or less.

## Exact required-path language and ordered selection composition

Proofs: `68128dd5` and `cfc38752`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-required-filter.md`. This section supersedes the complete
required-node filter and closed-source selection-composition targets.

Every completed physical required-node graph now satisfies:
meaning result term iff meaning input term and Matches needed term.
The trie is valid and recursively nonnegative. The input is closed and
available in a semantic-ready cache. Mutual graph induction retains exact
symbols, full guards, ordered children, and actual constructor readback.
Actual head normalization supplies recursive cases. Matching term arity
proves that rejected rows cannot discard a matching term. A semantic forest
bridge identifies the original-position child scan with the signed source
right fold. It uses the existing checked_row_exact theorem.

The compiled worker derives finite stable execution, final semantic heaps,
and exact forest filtering. Original closed construction derives all initial
premises. The top-level list entry ignores missing root positions. The
unconditional law therefore states requirements at present positions.
A root arity bound gives existence of every complete input path. Preservation
of an original term with all paths derives that bound from the term itself.
Both narrowing and preservation laws needed by the pure pass are proved.
A kernel fixture retains the missing-root boundary.

Actual class selection on a closed available forest returns the original
constructor cache. Closed Mu queries stop before unfolding; ordinary closed
records supply closed children. Thus every semantic-ready field after actual
selection follows without equating different Ready predicates. The following
required-path worker uses the ascending union of selected path sets, with
explicit natural-to-signed lookup readback. Both actual memo receipts and
finite stage bounds remain. Original closed source edges compose the actual
live precheck branch, physical ordered selection, and required-path execution.
The open-forest gate case is not covered by this cache-identity theorem.

The aggregate audit passes 1,646 jobs and 45,714 dependency checks using only
propext, Classical.choice, and Quot.sound. Only the old unused inputs warning
remains. All five new modules pass focused builds. No production Haskell
source changed; the earlier 645 examples and format checks apply to the
unchanged tree. Log: `/tmp/mcfta-required-filter-20261015-audit.log`.
Snapshot: `/tmp/mcfta-required-filter-checkpoint-20261015-0328/`
(2,038 Lean-tree files and four root documents). The only older Lean proof change
is added audit imports. All repros, counterexamples, marked drafts, stashes,
and other worktrees remain unchanged. Weekly allowance was 18% at
03:28 CEST; refresh before work.

Next derive the actual signed Edits compiler and simultaneous edit worker.
Retain the source right fold, empty-path replacement, prefix shadowing,
negative and missing positions, constructor-row head normalization, full
guards, and actual returned caches. Derive finite completion from finite edit
depth and completed head exposure. Prove node-callback and forest narrowing
and preservation, then derive concrete projection/intersection/merged-target
callbacks. Reuse existing physical operations and the completed unary ancestor
theorem. Do not replace merge over-approximation by equality. Full one-pass
source correspondence, open contexts, repeated fixed-point reduction, native
containers, lazy scheduling, and verified extraction remain open. Preserve
the exact Sized contracts, optimized interned core, all repairs and older
proofs. Stop all work and workers at 1% weekly allowance or less.

## Independent required-head language and semantic cache preservation

Proofs: `9fd64a7b`, `74df3d3b`, and `1bc034a6`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`, with retained traversal repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-required-head-language.md`. This section supersedes the actual
head-language and semantic-heap preservation targets.

Actual completed head normalization now preserves the full independent
guarded least language. A finite future cold-table trace is a proof witness
for the original root and every exposed child. Existing growth replay gives
exact returned alternatives in that cache. Cold-table soundness and budget
completeness give exact independent child languages. Actual row-node
construction therefore has exactly the input language. No conversion is
added to the runtime worker. Original closed source construction derives
finite complete head execution and exact source-expression language, with
all semantic cache premises derived. Raw retained binders and root unions
remain in scope.

Both independent semantic probe heaps now survive every complete required-node,
child, and row graph. Actual head and ordinary constructor effects supply
each step. Execution uniqueness derives complete intermediate list invariants.
The finite-worker Ready type and all earlier proofs remain unchanged. The
actual Needed compiler now also derives nonnegative signed keys at every
trie depth from normalized nonnegative paths. Raw negative keys remain explicit.

The audit passes 1,639 jobs and 45,676 dependency checks using only the three
permitted foundations. Only the old unused inputs warning remains. All six
new modules pass focused builds. No production Haskell source changed; the
previous 645 Haskell examples and format checks apply to the unchanged tree.
Log: `/tmp/mcfta-required-head-language-20261015-audit.log`. Snapshot:
`/tmp/mcfta-required-head-language-checkpoint-20261015-0313/`
(2,032 Lean-tree files and four root documents). The only older Lean proof
file change is added audit imports. Repros, counterexamples, marked drafts,
stashes, and other worktrees remain unchanged. Weekly allowance was 18% at
03:13 CEST; refresh before work.

Next derive the full required-node language filter law:
meaning result term iff meaning input term and Matches needed term, for valid
nonnegative Needed tries. Reuse head_exact, semantic graph preservation, and
the nonnegative compiler adapter. Prove actual child and row language readback,
then connect the signed adjustment fold through checked_row_exact. Retain
actual edge symbols, full guards, child order, and canonical readback. Do not
assume equal physical identities for outputs computed in different caches.
Then derive the compiled requireAll forest law and compose actual class
selection, deriving needed semantic-ready fields after gate effects. Actual
edit/narrowing, full one-pass correspondence, fixed-point reduction, native
containers, lazy scheduling, and verified extraction remain open. Preserve
exact Sized contracts, the unary ancestor theorem, and the optimized interned
core. Stop all work and workers at 1% weekly allowance or less.

## Complete physical required-path execution

Proofs: `ff6967ec`, `8c0774fd`, `a98f21e8`, and `17e59c87`. Source:
`TharkunAB/cfta`, `origin/main` at `f201deda`, with retained repair `61f2c939`.
Continue on `formalize` and push checkpoints. Read
`lean/notes-required-execution.md`. This section supersedes the finite
physical required-node execution target.

Actual edge and node reconstruction now derives complete cache readiness,
both histories, exact child payloads, closed results, and ordinary node heads.
Actual recursive head normalization has finite completion for all closed
available values, including raw binders and root unions. Successful head
bounds return one exact node and cache. The ordinary first-unfolding fast
path remains explicit.

The required-node, child, and row graphs preserve source branch priority.
Empty maps return first. The maximum-key row test rejects before child work.
Finite completion follows by strict finite Needed size and complete head
exposure, while automaton nodes can remain cyclic. Original source
construction derives all initial premises. The instrumented worker retains
pending constructors, unresolved references, worker-bound exhaustion, and
head-read exhaustion as separate outcomes. Graphs and successful execution
agree in both directions. Every completed graph supplies two sufficient
bounds; all larger pairs return the same value and complete final cache.
The compiled requireAll list entry derives every callback completion premise.

Kernel fixtures check the full worker on the raw self binder, both exhausted
bounds, and row rejection before an open child is visited. No production
Haskell source changed in this checkpoint. The previous 645 Haskell examples
and formatter checks apply to the unchanged production tree. The aggregate
Lean audit passes 1,633 jobs and 45,652 dependency checks using only the three
permitted foundations. Only the old unused inputs warning remains. Log:
`/tmp/mcfta-required-execution-20261015-audit.log`. Snapshot:
`/tmp/mcfta-required-execution-checkpoint-20261015-0259/`
(2,025 Lean-tree files and four root documents). All older proofs except added
audit imports, counterexamples, repros, marked drafts, stashes, and other
worktrees remain. Weekly allowance was 18% at 03:00 CEST; refresh before work.

Next prove independent output-language preservation. Start with actual head
normalization at the independent guarded least language, using existing cold
table soundness, budget completeness, and completed-read replay. A finite
future table may be a proof witness; add no conversion to the runtime worker.
Retain semantic probe heaps through the graph. Derive actual node/edge
language contracts, then apply checked_row_exact for normalized nonnegative
keys. Connect the compiled requireAll forest law to the physical selection
caller, deriving any additional ready-cache fields after its actual effects.
The logical call graphs do not prove native lazy scheduling or allocator
trace equivalence across different demand orders. Actual edit/narrowing,
full one-pass correspondence, fixed-point reduction, native containers, and
verified extraction remain open. Preserve exact Sized contracts, the unary
ancestor theorem, and the optimized interned core. Stop all work and workers
at 1% weekly allowance or less.

## Required-path trie, ordered child fold, and retained-cycle repair

Proofs: `06353eab` and `31868723`. Source repair: `61f2c939`. Upstream:
`TharkunAB/cfta`, `origin/main` at `f201deda`. Continue on `formalize` and
push checkpoints. Read `lean/notes-needed-head-repair.md`. This section
supersedes the Needed-construction and raw self-binder repair targets.

The signed finite child-map alter operation and the source right-fold Needed
compiler now have exact lookup, order, and validity proofs. Construction keeps
the exact prefix closure of all input paths, including duplicates and prefix
paths. Independent finite-term matching means existence of every complete
input path. Each insertion conjoins one requirement. The greatest-key row test
rejects no matching term. Raw negative keys remain explicit: that test alone
can pass a negative key, whereas signed lookup cannot. Normalized equality
classes derive nonnegative paths through the existing constructor validation.

The ordered child fold now has exact signed lookup and length proofs. It
keeps the source right-fold structure. Missing and negative positions leave
the list unchanged. Its forest theorem composes explicit exact node contracts.
The source arity check, normalized nonnegative keys, and original forest length
derive every selected child position. No whole-list law or term arity premise
is supplied. The actual recursive node contract remains to be proved. These
list results do not establish native lazy constructor scheduling.

The kernel checks that constructor-row exposure resolves the raw self binder
in two worklist steps. Rebuilding the empty row list leaves the cache unchanged.
Independent least-language semantics proves this binder equivalent to empty.
The source now uses that exposure before eight recursive traversals: required
paths, simultaneous edits, projections, single-path edits, child mapping, and
template restriction. It reuses nodeEdges and retains its ordinary fast path.
The old stutter proof and timeout reproduction remain unchanged. The old repro
expects failure; on repaired source it reports unexpected completion.

The aggregate audit passes 1,623 jobs and 45,488 theorem dependency checks.
Only the three permitted foundations occur. Only the old unused inputs warning
remains. All 645 Haskell examples pass in Nix: 289 core, 209 generator, and
147 refinement examples. The extended retained-cycle regression and format
checks pass. Audit: `/tmp/mcfta-needed-adjust-20261015-audit.log`.
Snapshot: `/tmp/mcfta-needed-adjust-checkpoint-20261015-0237/`
(2,014 Lean-tree files and four root documents). All older proofs except added
audit imports, counterexamples, repros, drafts, backups, stashes, and other
worktrees remain. Weekly allowance was 18% at 02:37 CEST. Refresh before work.

Next derive the repaired physical requireNode callback: empty-map identity,
maximum-key row rejection before child recursion, constructor-row exposure,
actual row-node and edge reconstruction, canonical cache hits, and returned
caches. The Needed compiler and ordered child-fold proofs are complete. Use
SourceEqualityNeededAdjustMeaning.checked_row_exact after deriving the actual
node callback contract. Derive finite execution from finite Needed depth and
complete closed exposure. Reuse MergedFreshOrdinaryColdTermination.read_closed
and exact physical head readback. Then derive actual edit/narrowing contracts.
The self-cycle fixture and conditional fold theorem are not a general physical
worker proof. Full pass correspondence, repeated fixed-point reduction,
native containers, lazy scheduling, and extraction remain open. Preserve the
exact Sized contracts, completed unary ancestor theorem, and optimized interned
core. Stop all work and workers at 1% weekly allowance or less.

## Physical class order, safe entry guards, and raw self-binder boundary

Proofs: `ae6a0141`, `ac7c1eaf`, `97f987a1`, and `a84343e3`. Source:
`TharkunAB/cfta`, `origin/main` at `f201deda`. Continue on `formalize` and push
checkpoints. Read `lean/notes-physical-class-order-entry.md`. This section
supersedes the physical class-order and early caller-guard targets.

The class input now follows the installed GHC 9.14.1/base 4.22 source sortBy.
It retains natural runs, fused three-way and four-way merges, short-list
branches, and special five-run and six-run reductions. Every occurrence is
preserved without a comparator-law premise. Physical trie subsumption has
exact strict-prefix readback. The source comparison keeps its reverse set
fallback. Supported path sets derive coherent trie/set records; normalized
constraints derive exact canonical payloads. A checked raw comparator cycle
shows that replacing the merge schedule can change source order. Haskell
confirms the cycle, exact class order, and normalization rejection.

The entry now executes empty and combined-contradiction guards before class
sorting. The unsafe accessor cannot see contradiction in the live branch.
Actual finite parent-array normalization derives sufficient work and exact
guard readback. Original construction derives finite complete physical
selection with both source memo tables. Early branches retain all caches.
The scalar source guard wrapper remains noncomputable. Native storage and
verified Haskell extraction remain separate obligations.

The next required-path primitive has a concrete raw-input boundary.
`createMuDontCleanup id` is closed and unconstrained, and unfolds to itself.
The gate clears its paths. Haskell reduction with the class `[[0,0],[1,0]]`
over two such children times out after two seconds. The kernel proves actual
repaired construction, closedness, a clear gate at every path, and exact
unfolding stutter. Repro: `lean/repro/RawClosedSelfRequire.hs`. A timeout is
runtime evidence, not a native nontermination theorem. Do not infer general
requireAll termination from the completed gate or the strict open-Mu rank.

The audit passes 1,617 jobs and 45,336 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-physical-class-order-entry-20261015-audit.log`. Snapshot:
`/tmp/mcfta-physical-class-order-entry-checkpoint-20261015-0213/`
(2,007 Lean-tree files and four root documents). All older proofs except new
audit imports, counterexamples, fixtures, marked drafts, repairs, backups,
stashes, and other worktrees remain. Weekly allowance was 19% at 02:13 CEST;
refresh it before work.

Next model the actual Needed trie and requireAll worker, then address the
closed raw self-binder stutter with a least-language-preserving repair.
Keep the full exported input domain; do not silently restrict to smart
constructors. Audit editAll and other same-path Mu readers for the same
boundary. Retain the optimized interned core and ordinary fast paths.
Reuse the completed gate, order, guard, and normalization proofs. Derive
actual required-path and narrowing contracts before claiming the whole
native pass. Repeated fixed-point reduction remains separate. Preserve the
exact Sized contracts and unary ancestor theorem. Stop all work and workers
at 1% weekly allowance or less.

## Complete ordered class selection and retained-cache readback

Proofs: `f3d27627`, `a93d1b35`, and `d0d8ac1f`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`. Continue on `formalize` and push checkpoints.
Read `lean/notes-ordered-class-selection.md`. This section supersedes the
earlier complete local-class filter target.

The actual ordered class filter now has finite complete execution. Every
class reads the original child list. A blocked class is discarded, then later
classes run. Each original occurrence has one ordered receipt with its actual
before cache, Boolean, and after cache. Repeated classes remain visible.
Every retained class has complete false path checks. Missing fuel and pending
construction remain separate from a Boolean decision. Graph and execution
correspond in both directions. More fuel retains the selected list and cache.

Both actual memo tables pass through the complete filter. Original source
construction derives initial cache premises and both empty memos. Memo
choices retain every class receipt, selected order, and final constructor
cache. The full gate now has a derived replay law: above a completed query's
final cache, the same query returns the same Boolean without constructor
effects. Every class receipt therefore replays in the full filter's final
cache. Derived total decisions in that cache give exactly
`EqualityReduction.selectedClasses`. The selected list also connects to the
existing one-pass forest theorem under its explicit primitive-operation laws.
No whole-cache observation law is supplied. This is retained-final-cache
readback, not arbitrary initial-cache equivalence or a native container proof.

The audit passes 1,609 jobs and 45,030 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-ordered-class-selection-20261015-audit.log`. Snapshot:
`/tmp/mcfta-ordered-class-selection-checkpoint-20261015-0152/`
(1,997 Lean-tree files and four root documents). All older proofs except new
audit imports, counterexamples, fixtures, marked drafts, repairs, backups,
stashes, and other worktrees remain. Weekly allowance was 19% at 01:51 CEST;
refresh it before work.

Next connect physical source constraint values to the ordered class input.
Model `unsafeSubsumptionOrderedEclasses`, `completedSubsumptionOrdering`,
its reverse structural fallback, and the actual source `sortBy` order. Keep
raw constructor payloads distinct from normalized consistent constraints.
Reuse the existing subsumption transitivity and irreflexivity proofs. Do not
assume a lawful comparator for arbitrary raw classes. Derive the empty and
combined-contradiction guards before selection, including why the unsafe
accessor cannot see `EqContradiction`. Then connect the actual required-path
and narrowing primitives to the one-pass laws. Do not infer fixed-point
termination from finite gate completion. Preserve exact Sized contracts,
the unary ancestor theorem, the optimized interned core, and native runtime
and extraction limits. Stop all work and workers at 1% allowance or less.

## Exact source crush semantics and both gate memos

Proofs: `0f5f465f`, `348e5adc`, and `9abb1aff`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`. Continue on `formalize` and push checkpoints.
Read `lean/notes-source-crush-both-memos.md`. This section supersedes the
earlier visited-fold and predicate-memo composition targets.

The actual visited source fold is true exactly when every physically reached
ordinary edge passes its local constraint test. A false result has a reached
failing edge witness. The proof derives closure, origins, and exact checks
through the actual changing visited sets. Canonical coherence handles repeated
identities. It includes arbitrary nested Mu and root unions. Bare references
stop. Mu traversal reads only the stored body, not either probe. No unrelated
cached edge must be plain. The concrete source test also gives the intended
always-accepting guard meaning under normalized original annotations.

Complete node, child, edge, path, and class graphs now carry both actual source
memo tables beside the constructor cache. Predicate receipts extend the
existing unfolding graphs. Each Mu read uses the proved concrete memo runner.
Actual unfolding growth preserves earlier predicate entries. False siblings
pass all returned tables onward. True siblings stop. Original construction
derives complete finite source executions and both empty initial memos.
Complete class graphs are equivalent to the original source graph. Memo
choices retain the exact Boolean and final constructor cache. No whole-fold,
whole-node predicate, whole-memo observation, or successful gate premise is
supplied. These are logical call graphs with exact actual runner equations;
they do not add an extracted executable memo backend.

The audit passes 1,603 jobs and 44,981 theorem dependency checks. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Only the old unused
`inputs` warning remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-source-crush-both-memos-20261015-audit.log`. Snapshot:
`/tmp/mcfta-source-crush-both-memos-checkpoint-20261015-0140/`
(1,990 Lean-tree files and four root documents). All older proof bytes except
audit imports, fixtures, counterexamples, marked drafts, repairs, backups,
stashes, and other worktrees remain. Weekly allowance was 19% at 01:38 CEST;
refresh it before work.

Next carry both memo tables through the complete ordered local-class filter
in `reduceEqConstraints`. Each class reads the original child list. Every
class runs, including those after a blocked class; only its internal `any`
scan stops early. Derive finite execution, exact retained class order, and
per-occurrence gate receipts in each actual intermediate cache. Then connect
this selection to `EqualityReduction.selectedClasses`. If that connection
compares decisions in different constructor caches, derive the required
growth/readback invariance; do not assume it. Keep missing fuel distinct from
a completed Boolean. Do not repeat completed rank, crush, or memo composition
proofs. Preserve exact Sized contracts, the unary ancestor theorem, the
optimized interned core, and native runtime/extraction limits. Stop all work
and workers at 1% weekly allowance or less.

## Complete memo gate graphs and concrete source predicate

Proofs: `c087a4ed`, `13b10b57`, and `3602e821`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`. Continue on `formalize` and push checkpoints.
Read `lean/notes-memo-gate-predicate.md`. This section supersedes the earlier
memo composition and supplied node-predicate targets.

Complete node, child, edge, path, and class graphs now carry the actual
unfolding memo and constructor cache together. Every source graph lifts to
actual coherent memo calls. Each Mu readback is derived from `run_complete`.
Erasure recovers the exact source graph. False siblings pass both returned
caches onward. True siblings stop. Complete class graphs are equivalent to
the source graphs under derived ready-cache and memo invariants. Certified
class decisions and final constructor caches do not depend on the starting
unfolding memo. Original construction derives all initial premises.

The source Boolean `crush` is now modeled directly. It skips empty records
and bare references. It marks canonical identities before source child visits.
Mu traversal visits only the body, not either probe. The structurally recursive
worker retains a distinct visited set bounded by the actual issued counter.
`SourceMemoGate` installs this concrete node read with the existing normalized
equality/residual edge test. Its source-derived node and class theorems take
no supplied whole-node predicate. `SourceUnconstrainedMemo` proves exact
predicate memo hits, misses, insertion, and preservation after cache growth.
The scalar normalization wrapper retains the existing noncomputable logical
source model. No executable extraction claim is added.

The audit passes 1,598 jobs and 44,916 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-memo-composition-source-predicate-20261015-audit.log`. Snapshot:
`/tmp/mcfta-memo-gate-predicate-checkpoint-20261015-0123/` (1,982 Lean-tree files).
All prior proofs, counterexamples, marked drafts, repairs, backups, stashes,
and other worktrees remain. Weekly allowance was 19% at 01:23 CEST; refresh it.

Next prove the full semantic characterization of the visited `crush` result
on actual coherent available records. It is true exactly when every ordinary
edge reached through stored bodies, ordinary children, and union members
passes `plain`. Include repeated canonical identities and root unions.
Bare references stop; do not follow them by unfolding. Use actual canonical
record coherence, not an assumed whole-fold law. Then carry the separately
proved predicate memo through the complete gate graphs beside the unfolding
memo. Do not repeat completed unfolding-memo composition or predicate call
laws. Preserve exact Sized contracts, the unary ancestor theorem, the
optimized interned core, and native runtime/extraction limits. Stop work and
workers at 1% weekly allowance or less.

## Ordered gate execution and coherent unfolding memo

Proofs: `ec56843a`, `512a386d`, and `8b5ec04e`. Source: `TharkunAB/cfta`,
`origin/main` at `f201deda`. Continue on `formalize` and push checkpoints.
Read `lean/notes-stateful-gate.md`. This section supersedes the earlier
ordered sibling-cache target.

The new worker threads actual constructor caches through original edge and
path order. A true result stops the scan. Every completed false query passes
its returned cache to the next sibling. Missing gate fuel and a pending
constructor request remain separate. Every node query and complete equality
class has a finite Boolean execution. Cache growth keeps later siblings'
original inputs available. Every returned cache retains semantic contexts,
depth heaps, payload coverage, weighted heaps, and both growth histories.
More fuel preserves the exact Boolean and final constructor cache.

Separate logical node, child, edge, path, and class graphs have no gate fuel.
Both graph/execution directions are proved. Node and class graphs are
functional in the Boolean and complete final cache. Original source
construction derives finite node traces and class traces for every original
outgoing edge. No completed construction or gate call is supplied.

The unfolding memo now has a derived coherence invariant. It uses actual
canonical references and immutable input records. Every hit or miss returns
exactly the actual repaired unfolding value and constructor cache. A miss
installs a coherent entry. Later growth preserves every saved entry. This
reuses the existing stored unfolding replay theorem in
`MergedFreshOrdinaryColdReplay`; no duplicate replay helper was retained.

The audit passes 1,591 jobs and 44,835 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-stateful-gate-memo-20261015-audit.log`. Snapshot:
`/tmp/mcfta-stateful-gate-checkpoint-20261015-0106/` (1,974 Lean-tree files).
All prior proofs, counterexamples, marked drafts, repairs, backups, stashes,
and other worktrees remain. Weekly allowance was 19% at 01:06 CEST; refresh it.

Next carry the coherent memo runner through complete ordered gate graphs.
Use `run_complete` for each actual hit or miss. Then derive the source
`unconstrained` read from `crush` over complete records and the actual edge
constraint test. Its Mu traversal reads only the body, not the probes.
The constraint predicate is still a supplied pure read in the current gate.
Do not repeat completed rank, stateful completion, or graph adequacy proofs.
Keep exact Sized contracts, the unary ancestor theorem, the optimized
interned core, and native runtime/extraction limits. Stop work and workers
at 1% weekly allowance or less.

## General repaired unfolding rank and gate completion

Proofs: `0871fb7a` and `40027d5f`. Source: `TharkunAB/cfta`, `origin/main`
at `f201deda`. Continue on `formalize` and push completed checkpoints.
Read `lean/notes-general-unfold-rank.md`. This section supersedes the earlier
prepared-plan retention and opaque-probe rank targets.

The prepared-plan retention bound is complete. It includes arbitrary open
nested Mu, root unions with Mu members, lexical shadowing, and nonempty
reconstruction of every original live edge sibling. Replacing the outer
reference with its open Mu retains each external body occurrence at no
greater cost. The exact source cost theorem transfers that bound to the
actual returned record. Every actual open Mu unfolding strictly decreases
minimum free-occurrence rank. Finite completion retains the complete
semantic contexts, depth heaps, payload coverage, weighted heaps,
availability, growth, and issued-name history. Original source construction
derives these premises. No shallow-body or successful-unfold premise remains.

The general certified read adapter carries each actual unfolding result and
its returned cache. Its concrete rank instantiates `ConstrainedRecursionGate`.
Every finite path has a finite instrumented evaluation equal to the total
decision. Every larger fuel amount gives that same decision. Original source
construction derives the adapter's initial node and finite gate evaluation.
The constraint predicate remains an explicit read parameter.

The audit passes 1,585 jobs and 44,758 theorem dependency checks. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Only the old unused
`inputs` warning remains. No production Haskell code changed. Audit log:
`/tmp/mcfta-general-open-unfold-rank-20261015-audit.log`. Snapshot:
`/tmp/mcfta-general-unfold-rank-checkpoint-20261015-0047/` (1,967 Lean-tree files).
All older proofs, counterexamples, repros, marked drafts, repairs, backups,
stashes, and other worktrees remain.

Next connect the ranked route adapter to the full ordered source gate with
shared memo effects across sibling edge and path queries. The current view
starts each child route in its parent's cache. Model ordered short circuit
and thread actual returned caches. Reuse the rank bound in every retained
cache. Derive a full source gate trace/readback law, or state the required
memo observation law precisely. Do not repeat the completed retention or
rank proof. Keep the completed Sized contracts, unary ancestor theorem,
optimized interned core, and runtime/extraction limits. Do not use the
closed-node dynamic Mu budget for an open Mu. Stop work and workers at 1%
weekly allowance or less.

## General occurrence costs in repaired source execution

The latest proofs are `efa2e558` and `d17e644b`. Continue on `formalize` in
`TharkunAB/cfta`, based on `origin/main` at `f201deda`. Push checkpoints
regularly. Read `lean/notes-occurrence-costs.md`. This section supersedes the
earlier weighted callback/probe next target.

The full actual source induction now derives every returned free-reference
cost and preserves the weighted recursive heap. It covers arbitrary nested
syntax, both probes, actual fresh bodies, canonical hits, discarded child
effects, and pending outer outcomes. Original empty-cache construction derives
the invariant. No whole-callback cost law or final weighted heap is supplied.
The comparison is exact pair membership, not list order or multiplicity.

Every stored Mu now has exact external body/ordinary-probe cost agreement.
Every free Mu occurrence has its exact predecessor in the actual ordinary
probe. The probe has a strict minimum-cost rank bound for an open Mu.
Actual repaired stored execution has the exact pure prepared-plan costs.
Finite stored execution and unfolding preserve the weighted heap and all
existing semantic contexts, depth heaps, coverage, availability, and growth.
An unfolding rank is separate from a Sized term rank; the glossary records it.

The audit passes 1,577 jobs and 44,674 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-general-fresh-occurrence-costs-20261015-audit.log`.
No production Haskell code changed. Snapshot:
`/tmp/mcfta-general-fresh-costs-checkpoint-20261015-0034/` (1,960 Lean-tree files).
All earlier proofs, counterexamples, repros, marked drafts, repairs, backups,
stashes, and worktrees remain. No owned proof worker remains.

Next prove the prepared-plan retention bound stated in the occurrence-cost
note. Each external original body occurrence must survive at no greater cost
when the outer reference is replaced by its actual open Mu. Include nested
Mu and root unions with Mu members. Derive nonempty reconstruction for live
edge siblings if needed. Reuse exact stored slot lookup and lexical shadowing.
Then use `execute_complete_costs`, `mu_cost_iff`, and the original minimum
witness to derive strict rank decrease for actual unfolding. The weighted
source correspondence is complete; do not repeat it. The probe's strict rank
is not yet a rank theorem for actual unfolding. Keep the completed Sized and
unary ancestor proofs and the optimized interned core. Preserve runtime and
extraction limits. Stop all work and workers at 1% weekly allowance or less.

## Guarded repaired unfolding and the cost replay

The latest proof is `6adcb38f`. Continue on `formalize` in `TharkunAB/cfta`,
based on `origin/main` at `f201deda`. Push checkpoints regularly.
Read the first section of `lean/notes-gate-unfolding-rank.md`.
This section supersedes the earlier opaque-body next-target statement.

`InternedFreshOrdinaryGuardedUnfold` proves actual repaired guard preservation,
completed unfolding, head rank zero, and strict head-rank decrease for a
source-filtered `HeadSafe` body. Constructor children can contain arbitrary
open nested binders. No shallow-body, marker, first-order, or successful-unfold
premise is supplied. Original empty-cache construction derives the cache
premises. Exact returned contexts, depth heaps, payload coverage, available
results, growth, issued-name history, and body filters are retained.
General repaired substitution also preserves body filters without `HeadSafe`.

`InternedFreshOrdinaryCostReplay` checks the exact earlier cost-boundary
expression with the repaired scheduler. Both probes now retain its external
body costs, and exact probe coverage holds for this replay. The old checked
failure remains unchanged. This does not establish a general cost invariant.

The audit passes 1,570 jobs and 44,569 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-repaired-guarded-cost-20261015-audit.log`.
No production Haskell code changed. Snapshot:
`/tmp/mcfta-repaired-guarded-cost-checkpoint-20261015-0013/` (1,952 Lean-tree files).
All older proof bytes, counterexamples, repros, marked drafts, repairs,
backups, stashes, and worktrees remain. No owned proof worker remains.

Next prove progress for opaque leading Mu bodies and root unions with Mu
members. Such unions can expose a Mu through singleton reconstruction.
Use actual repaired semantic origins, returned caches, and body filters.
The retention and separation lemmas may help the union case. For a cost-based
rank, first prove weighted source callback/probe correspondence through
actual cache hits. Reuse `InternedFreeOccurrenceExact` and normalization laws.
Do not infer the invariant from the finite replay. The closed-node dynamic
budget does not apply directly to open Mu. Preserve the completed Sized and
unary ancestor proofs, the optimized interned core, and runtime boundaries.
The Lava note remains relevant prior art. Stop work and workers at 1% weekly
allowance or less.

## Repaired gate progress and Lava

The latest proofs are `8e8cbc91` and `d513db2b`. Continue on `formalize` in
`TharkunAB/cfta`, based on `origin/main` at `f201deda`. Push completed
checkpoints regularly to `origin/formalize`. Read the first section of
`lean/notes-gate-unfolding-rank.md` and `lean/notes-lava.md`.
This section supersedes the earlier replay and pure-probe next targets.

The exact repaired replay of the old rank example gives head and minimum
free-reference ranks `[2, 1, 0, 0]`, cached depths `[2, 3, 3, 3]`, and no
first-unfold hit on the later representative. Its first step strictly
decreases both candidate ranks. The old executor's stutter remains checked
and unchanged. Neither result proves a general repaired rank.

Actual repaired execution now derives stored body filters, joint probe
opacity, and completed strict head-rank progress from one pure Depth probe.
The theorem uses the repaired stored executor and derives the representation
premises from original empty-cache source execution. No body-depth or
callback-completion premise is supplied. The repaired ordinary probe choice
remains `ordinaryLevel`; a pure Depth probe need not select level zero.

Matti supplied the local Lava paper. The paper note records its executable
function/logical graph correspondence method. Its monomorphic, structural,
call-by-value fragment does not close the opaque gate, lazy scheduling,
external solver, native capacity, or source-extraction obligations. No new
translator, dependency, or proof system was introduced.

The audit passes 1,568 jobs and 44,486 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-repaired-gate-lava-20261015-audit.log`.
No production Haskell code changed. Snapshot:
`/tmp/mcfta-repaired-gate-lava-checkpoint-20261015-0003/` (1,950 Lean-tree files).
All earlier proof bytes, counterexamples, repros, marked drafts, repairs,
backups, stashes, and worktrees remain. No owned proof worker remains.

Next prove progress for arbitrary opaque repaired probes. Use actual
FreshOrdinary source origins, body filters, and returned caches. The existing
dynamic Mu budget requires a closed node and cannot be applied directly to
the open-Mu gate. Cached maximum depth is not a strict measure. Keep the
completed Sized paths and unary ancestor root theorem. Do not resume the
archived unary draft. Do not claim general rank decrease from this finite
replay. Keep the optimized interned core and explicit runtime boundaries.
Stop all work and workers at 1% weekly allowance or less.

## Exact Sized paths from original closed source expressions

The latest proofs are `0e8b2265` and `dd240eb6`. Continue on `formalize` in
`TharkunAB/cfta`, based on `origin/main` at `f201deda`. Push completed
checkpoints regularly to `origin/formalize`. Read `lean/notes-source-closed-sized.md`.
This section supersedes the earlier cold reference/dispatch next target.

`SourceSizedNormalizedConstraints` derives complete normalized row annotation
invariants from original checked syntax through actual construction and cold
traversal. `SourceFreshOrdinarySizedEntry` follows actual physical open checks,
cold rows, public validation, and either original-map query path.
`Execution.change_dispatch` retains the exact complete result and final cache.
The correct entry derives both complete executions, all exact query laws at
the independent physical language, and the original FTA/residual error channels.
No validation success, final metadata, or rowwise annotation law is supplied.

`SourceClosedSized.reference_and_dispatch` derives construction itself, then
both actual query paths. Its successful complete API denotes the original
expression's independent guarded least language. `solver_decided` derives
construction and actual encoded bounded execution at the expression language
under ambient solver meaning and the signed node-count bound. No supplied
finished-construction equation remains. External attempt termination and
response correctness keep their explicit contracts. All three paths retain
finite exact distinct classes, size order, counts, and both term inverses.

The audit passes 1,564 jobs and 44,406 theorem dependency checks. Only the
three permitted foundations occur. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-source-closed-sized-20261014-audit.log`.
No production Haskell code changed. Snapshot:
`/tmp/mcfta-source-closed-sized-checkpoint-20261014-2343/` (1,945 Lean-tree files).
All previous proof bytes, repros, drafts, repairs, backups, stashes, and worktrees
remain. No background proof worker is active after this checkpoint.

Next resume the general opaque-probe constrained-recursion gate. Read the
last section of `lean/notes-gate-unfolding-rank.md`, `InternedReachableGateRank`,
and `InternedSourceRankStutter`. Replay the old example with the repaired
FreshOrdinary constructor and stored executor before applying its observations
to current source. Shallow reachable Mu and pure-probe ranks are already proved;
the general opaque case remains separate. Do not repeat the completed unary
ancestor edit or root loop. Preserve all marked drafts. Keep the optimized
interned core and the explicit runtime/extraction boundaries. Stop all work
and workers at 1% weekly allowance or less.

## General repaired cold conversion and complete encoded Sized entry

The latest proofs are `e7ab540a` and `4d1240dc`. Continue on `formalize` in
`TharkunAB/cfta`, based on `origin/main` at `f201deda`. Push checkpoints
regularly to `origin/formalize`. Read `lean/notes-general-cold-liquid-entry.md`.
This section supersedes the earlier cold-validation next target.

Root membership and child closure do not imply a ranked alphabet. The new
checked `FTAValidation.arity_boundary` counterexample records that boundary.
`SourceFreshOrdinaryColdValidated` derives both state invariants from actual
repaired traversal and reduces public conversion to the literal normalized
arity scan. Complete raw constraints and alternative order survive actual
map normalization. Only the real arity failure can reject a closed cold table.
No unconditional successful-validation claim is made.

`SourceFreshOrdinaryColdLiquid` derives the independent original physical
root language after normalized validation. `SourceFreshOrdinaryLiquidEntry`
follows physical free-variable checks, actual cold traversal, FTA validation,
and the encoded bounded solver fold. Open and invalid inputs return before
solver work. Conversion errors, raised failures, Unknown, and successful
query APIs retain distinct channels. `constructed_complete` derives finite
actual staged execution and all exact bounded query laws from actual general
repaired construction. It assumes no supplied validation success, final
metadata, prepared-cache restriction, native completion, or language equation.
External attempt termination and response correctness remain explicit.

The audit passes 1,560 jobs and 44,392 theorem dependency checks. Only the
three permitted Lean foundations occur. Only the old unused `inputs` warning
remains. Log: `/tmp/mcfta-general-cold-liquid-entry-20261014-audit.log`.
No production Haskell code changed. Snapshot:
`/tmp/mcfta-general-cold-liquid-checkpoint-20261014-2331/` (1,940 Lean-tree files).
All earlier proof bytes, repros, drafts, repairs, backups, stashes, and worktrees
remain. No background proof worker is active after this checkpoint.

Next connect original-map `sizedReference` and optimized `sized` to this same
actual validated normalized cold table. Derive raw active equalities from
original checked annotations through construction and traversal. Retain FTA
arity errors, Sized residual-guard errors, and complete query-record equality.
Reuse the cold constraint heap, normalized raw graph, and existing explicit-map
API laws. Keep the older cyclic-import entry and all constructor/equality work.
Stop all work and workers at 1% weekly allowance or less.

## Complete common query laws for all explicit-map Sized paths

The latest proof checkpoint is `221bb23a`. Continue on `formalize` against
`origin/main` at `f201deda` in `TharkunAB/cfta`. Push completed checkpoints
regularly to `origin/formalize`. The upstream and permission notes below
remain in force. This section supersedes their next proof targets.
Read `lean/notes-sized-api-laws.md`.

`SourceSizedFiniteKeysApiLaws` derives the common `Exact` query specification
for the original-map reference and optimized paths at the original guarded
language. `SourceSizedBoundedReference.classes_eq` proves that a complete-term
size guard preserves the exact canonical classes through a signed bound and
makes every later class empty. It includes negative bounds and size zero.
The certificate graph does not replace the actual source solver worker.
`SourceSizedBoundedApiLaws` identifies the complete fromClasses record with
that reference sequence. `SourceSizedFiniteKeysDecidedApiLaws` and
`SourceSizedFiniteKeysLiquidApiLaws` derive all common laws for actual bounded
and encoded raw solver traces. They retain occurrence work, varying replies,
Unknown, and exact error channels. Finite external outcomes derive finite
actual execution. External correctness and termination remain explicit.

The current audit passes 1,554 jobs and 44,359 theorem dependency checks.
Log: `/tmp/mcfta-unified-sized-api-laws-20261014-audit.log`. Only the three
permitted Lean foundations occur. Only the old unused `inputs` warning remains.
No production Haskell code changed. All older proof bytes, fixtures, and
marked drafts remain. Snapshot:
`/tmp/mcfta-unified-sized-api-checkpoint-20261014-2316/` (1,933 Lean-tree files).

Next connect the general repaired cold path to the encoded solver query
result. Derive root membership and child closure. Retain the actual arity scan;
successful validation also requires a ranked alphabet. Use `SourceFreshOrdinaryColdGuardedExact.trace_table_exact` for the
independent original root language, `sizedTable`/`sized_graph` for raw conversion,
and the new encoded exact query theorem. The old prepared/first-order liquid
adapter remains a narrower result. Preserve the optimized interned core,
all older constructor/equality work, and the explicit runtime/extraction
boundaries. Do not repeat the completed explicit-map query proofs.
Stop all work and workers at 1% weekly allowance or less.

## Upstream move and physical public entry

The repository is now `TharkunAB/cfta`. `origin` is
`git@github.com:TharkunAB/cfta.git`. Continue on `formalize` against
`origin/main` at `f201deda`. The old remote remains as `microecta-legacy`.
The user now authorizes regular pushes to `origin/formalize`. This overrides
older local-only and no-push instructions below. Do not deploy, post to the
board, or send messages.

The latest proof is `8a0eb5f9`. It adds actual physical-root entry control,
finite complete native execution, unique public reference results, independent
guarded root-language readback, and the complete public query specification.
Read `lean/notes-native-public-entry.md`. Empty and open roots return before
cold traversal or native callbacks. Only a nonempty closed root enters the
finite row phase. The key carrier remains internal to that branch.
`execution_correct` proves complete optimized/reference result equality,
including errors. `complete_exact` derives finite actual execution and exact
query laws. `constructed_complete` derives its initial invariants from actual
closed construction. Normalized original annotations and reached cache
capacity remain explicit. Final metadata, callback completion, and language
correspondence are derived.

`SourceSizedApiLaws.Exact` includes finite source class evaluations, exact
distinct accepted terms per node-count size, counts, signed rejection,
accepted-term rank coverage, size-major prefixes, and both rank/unrank inverse
directions. The physical reference and native paths satisfy the same record
specification at the original independent guarded root language.

The conflict-free rebase replayed 575 commits onto the new main. The upstream
changes remove the old ECTA packages and update URLs. They change no active
CFTA implementation. All 1,926 saved Lean-tree files and four root documents
retained identical bytes through the rebase. Proof `452b20b5` tracks the three
retained repro fixtures so the remote checkpoint includes them. All marked
drafts, earlier proofs, repairs, counterexamples, backups, stashes, and other
worktrees remain. Pre-rebase evidence is in
`/tmp/mcfta-cfta-origin-refresh-20261014-2306/`. The complete pre-rebase branch
is `backup/formalization-complete-before-cfta-main-20261014-2309`.
The former proof hashes and `origin/microcfta` references below are historical.

The post-rebase audit passes 1,549 jobs and 44,339 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-cfta-main-20261014-audit.log`. Only the old unused `inputs`
warning remains. The active Haskell trees differ from main only in a retained
four-line constructor changelog note. The previous 645 examples, five probes,
and formatter checks retain the same implementation and were not repeated.
Current snapshot:
`/tmp/mcfta-public-entry-cfta-main-checkpoint-20261014-2308/`.

Next apply the common query specification to the original-map reference and
optimized dispatch paths, then to bounded solver-decided classes. Reuse
`SourceSizedFiniteKeysPublic*`, `SourceSizedFiniteKeysDispatchApi`, and
`SourceSizedFiniteKeysNativeLiquid`. Preserve actual work, varying replies,
Unknown, exact errors, and empty classes above the bound. Keep all external
solver, concrete container, lazy scheduling, and extraction boundaries explicit.
Preserve the optimized interned core and older constructor/equality targets.
Check weekly allowance and stop all work at 1% remaining or less.


The earlier independent compiler snapshot is /tmp/mcfta-independent-guarded-checkpoint-20261014-1549/: 1,761 Lean-tree files, root restart documents, retained fixture, and audit evidence. Its preservation report compares all 1,754 previous checkpoint files. None is missing. Only audit imports, two coverage ledgers, and three component notes changed among those files. The six new semantic/compiler proof modules and their new component note are added. All earlier proof and marked-draft bytes remain. All preserving backups remain.

Inspect allowance, status, branches, worktrees, and stashes first. Preserve every local proof, source repair, counterexample, marked draft, backup, stash, and worktree. Preserve tracked lean/repro/NestedUnaryTwoAtom.hs, lean/repro/NativeProductRowCycle.hs, and lean/repro/UnionDiagonalRows.hs. Do not alter /tmp/mcfta-update-20261013 or its uncommitted review merge and evidence. If upstream moved, back up and rebase again. Verify preservation against a new manifest.

Read lean/notes-native-public-entry.md for the current target. The physical public entry and complete query specification are now proved. Do not repeat the precheck, cold trace uniqueness, complete native entry, or independent language readback proofs. Next connect SourceSizedApiLaws.Exact to original-map reference and optimized dispatch, then bounded solver-decided classes. Keep actual bounded work and errors. Reuse the existing component theorems. Historical next-target statements below are superseded.

The primary Sized source contract is proved: exact distinct accepted terms per node-count size, finite reference classes, size-major prefixes, and both rank/unrank inverse laws. SourceSizedFiniteKeys* derives the carrier from actual validated map keys even when the state type is infinite. nativeSized_eq proves exact raw-map optimized/reference query-record equality and errors. The finite synchronous product minimum gate is derived. This exact path retains the optimized interned core and does not depend on recursive interned intersection construction.

The new TablePositionCountBound.positions_congr proves that optimized bottom-up ranking reads no count above the input term's node count. This includes offsets for preceding transitions that reject the input term. TablePositionFiniteEvaluation.finite_rank constructs finite count inventories and child maps with the exact original rank or failure. SourceSizedFiniteKeysRankEvaluation.native_rank_laws identifies this finite result with the actual public optimized inverse and both signed inverse laws. The finite evaluator is a proof construction, not a replacement eager Haskell implementation. Concrete lazy heap scheduling remains a boundary.

SourceSizedFiniteKeysNativeLiquid.encoded_correct proves independent mixed-sort ambient logical acceptance and the canonical bounded sequence for actual raw folds. encoded_finite includes finite outcomes, Unknown, and unchanged exceptions. Replies may vary. External SMT correctness and completion remain explicit. Preserve the injective solver-name repair, ambient fresh-name repair, weighted midpoint repair, custom-key order qualification, and all retained examples. Preserve distinctions between terms, accepting runs, generator members, and PMF keys.

Warm native completion and the full actual ordered ambiguity scan are now proved. Idle permits suspended and returned memo cells but excludes evaluating cells. warm_node_complete derives successful stable execution without a supplied native completion. SourceFreshOrdinaryNativeCallback.Execution has the exact empty-exposure early return; only its nonempty branch collects rows and reads minima. complete, Execution.unique, and Execution.correct retain the exact Boolean, cache, and all next-call invariants. complete_keys derives finite exact callbacks from actual input-table metadata. SourceFreshOrdinaryNativeKeyScan.scan_complete and scan_correct derive finite actual all-row scans and the literal reference ambiguity Boolean. Nested Ranges checks only actual reached queries and continuing suffixes. No whole product-language equation or exact-row adapter is supplied.

Next compose the literal compiler result and its class/query laws. Preserve empty, open, constrained, ambiguous, and canonical branch precedence. Construct the cyclic input directly from actual raw rows and root membership. Derive guarded/structural row equality after the real constraint precheck. Use the completed native scan, then reuse the existing exact Sized classes, size order, finite execution, and both inverse laws. Do not repeat warm success, callback determinism, or the ordered scan. Read lean/notes-native-full-scan.md, lean/notes-native-key-callback.md, and lean/notes-package-rename.md.

The main Sized algorithms are complete at the stated source-model layer. The actual repaired first-order cold path also supplies exact guarded rows, finite size classes, native/reference equality, and encoded solver-decided composition. General output exposure and physical product language remain separate targets. Read HANDOFF.md for the full proof map. Preserve the completed control, stored rebinding, kernel, memo, native execution, input-view, bounded-terminal, and producer-history work.

Arbitrary-record source completion is now proved. 92746870 derives exact shapes from coherent available records, including mixed-union root alternatives. e543e630 proves the full source depth/deep heap induction with arbitrary captured records. The old literal driver is a specialization. cdcbb881 proves actual ordinary-level agreement from equal projected record shapes, follows both actual scoped routes, and excludes their required ordinary mismatch. InternedRecordDepthCompletion.source_complete returns the exact successful value and cache for arbitrary syntax and captured records, given Context, DepthHeap.Heap, and Covered []. No preparation or supplied termination premise is used. e4a011e8 composes this with actual maybeMu substitution and arbitrary stored leaves. complete_decoded derives successful execution, retained Context/depth heap/coverage, availability, growth, and issued history. Read lean/notes-record-depth-completion.md. Do not repeat the closed, literal, or arbitrary-record source proof. The alternative shorter-producer descent remains unclosed but is not needed for these results; retain all its evidence.

ec611802 proves semantic-heap preservation for actual emitted edge/node/union/optional-binder effects and every compiled branch. SourceRecursiveIntersectionNativeSemantic.Bounds.semantic_heap follows actual completed nested native evaluation, checked memo keys, and original completion frames. f7b842e4 derives actual unfinished body/continuation splits and excludes pending constructors by strong induction on the finite native bound. It uses completed body provenance and semantic heaps at each reached optional-binder site. A generic all-prefix semantic invariant is not required. NativeSuccessful.cold_node_complete combines this with the existing finite terminal bound to derive successful first execution for closed Original available inputs from a complete semantic cache, under explicit WordRanges. It retains exact returned caches, strong memo provenance, guarded kernel meaning, semantic heaps, complete coverage, and the identical value/cache at all larger bounds. constructed_node_complete derives the semantic/coverage premises from actual repaired closed source construction. Read lean/notes-native-successful.md. Do not repeat source completion, completed native semantic preservation, or first-run success for this stated scope.

018f1712 proves exact used lexical positions for actual returned free names, original stored-plan free support outside all local binders, and actual maybeMu free_support/pair_absent. Returned names belong to the original body and differ from the selected intersection pair. 2ac3ca41 proves that every captured leaf is closed or a reference, and every repaired substitution result free name comes from the replacement of an original free reference. execute_complete_decoded and unfold_complete_decoded derive arbitrary stored substitution and single unfolding without preparation, retaining exact caches, semantic heaps, coverage, availability, and histories. unfold_closed derives closed output from a closed available input. Read lean/notes-stored-free-unfold.md. These results do not prove termination of repeated cold-reader traversal or NoNewMu.

Recursive result scope and native output closedness are now proved. SourceRecursiveIntersectionKernelScope.execute_scoped follows every actual source branch and derives incoming seen-pair scope. The actual optional binder removes its current pair. NativeResultScope transfers this through exact guarded kernel meaning. OriginalOutput derives original payload syntax from coherent availability and proved closedness, with probe metadata excluded by the existing predicate. MergedFreshOrdinaryColdEffects.collect_verified and nodeEdges_verified retain complete semantic heaps, coverage, exact growth/history, resident edges, and closed children at every bound without preparation or NoNewMu. Pending construction and unresolved references are excluded; exhausted remains possible. NativeColdEffects.cold_node_read_effects supplies these premises from actual successful first native execution. Read lean/notes-native-output-cold-effects.md. Do not repeat these completed results.

6e9804df proves general repaired stored/unfolding replay, all bounded reader validity/growth, exact ordered-row replay after final-cache growth, and larger-bound stability. nodeEdges_replay_stable combines later caches and bounds. Only initial cache validity and an actual completed read are required. It does not supply a successful bound. 0534aad8 retains the source-built closed mu x. mu y. f(x,y) boundary: actual unfolding allocates a new Mu and increases cached depth from 2 to 3, but the reader still finishes. Live Haskell confirms that increase and successful reading. Do not retry initial Mu-inventory retention or descending cached depth as general measures. Read lean/notes-native-output-cold-effects.md for exact statements and logs.

c410bc0a adds SourceFreshOrdinaryColdSharedRows: its actual shared worklist calls MergedFreshOrdinaryExposure directly. Trace.finite and collect_trace connect finite relational and executable runs with identical tables and caches. of_prepared and Trace.to_prepared derive both bridges to earlier prepared traces. Trace.correct retains semantic heaps, coverage, row provenance, exact growth/history, and closed children for arbitrary actual finite traces without preparation or NoNewMu. cold_finite derives finite actual repaired prepared traversal without a supplied trace. SourceFirstOrderFreshColdSized.source_sized composes actual repaired empty-cache first-order construction and repaired shared traversal with exact finite node-count classes, distinct size order, bounded coverage, and both inverse laws. Read lean/notes-fresh-cold-shared-rows.md. The later 68e790f0 checkpoint proves general nested finite trace existence.

75c50b4d retains InternedStoredRawIdentityBoundary. Actual closed construction mu x. rawMu unused. f(x) has an open stored inner body. Identity substitution into that body changes physical identity and cached depth 1 to 0 because substitutionPlan rebuilds open Mu records with smart createMu. Free names remain equal. The earlier unqualified physical identity-substitution postcondition in Type.hs was false for this raw-binder case; upstream PR #121 now qualifies the comment. Live Haskell confirms (False,1,0). Runtime behavior was not changed. Do not use literal reconstruction identity for arbitrary raw binders. For substitution follow substitutionPlan, which intentionally does not use pattern-synonym matcher fast paths. See lean/notes-fresh-cold-shared-rows.md.

8598886f derives exact repaired source lexical dependencies and original free-binding restriction. InternedFreshOrdinaryDependencies maps agreement on actual used slots to equivalent full plans and retains exact outcomes and caches. Repaired stored execute_congr, execute_restrict, and execute_binding_replay cover arbitrary nested plans. InternedFreshOrdinaryBindingKeys derives full replacement equality from equal ordered optional physical identities in one coherent cache. execute_key and execute_key_replay derive exact computations and allocation-free replay. choices/keys supply a finite inventory for closed available replacements in the current cache, with at most nodes.next + 2 choices per binding. Future cache growth can introduce new closed values. This is not a proof of finite closure across reads. Read lean/notes-fresh-binding-keys.md.

7f1daf23 adds InternedStoredPlanBinderDepth. valueDepth ignores closed captures and counts maximum open Mu nesting; bodyDepth measures the actual stored Mu body plan. encode_depth proves exact equality with maximum binder nesting in the actual encoded source plan. Path.plan_depth_bound bounds actual callback crossings by the original plan depth. syntax_zero characterizes binder-free plans; execute_zero_noNewMu and unfold_zero_noNewMu prove the base case without preparation or semantic-cache hypotheses. These are static compiler and zero-case laws, not general unfolding progress. A completed exploratory run checked 1,336 generated closed expressions, every closed Mu in their constructed caches, and every newly allocated closed Mu after unfolding. No violation of the proposed strict bodyDepth decrease was found. File /tmp/mcfta-open-rank-probe.lean; log /tmp/mcfta-open-rank-probe-20261014.log. Read lean/notes-stored-plan-binder-depth.md. The later general progress theorem supersedes this exploratory target. Do not repeat the depth-one or general decrease proof. Account for canonical hits and fresh interned body names. Do not infer a runtime depth bound or literal rebuild identity. If this decrease holds, a dynamic rank-count budget can replace the old fixed Mu inventory; that budget has not been implemented.

262242f9 adds InternedStoredPlanBinderDepthBounds: coherent available records satisfy valueDepth ≤ cached depth and valueDepth ≤ actual repaired ordinaryLevel. Closed captures can make those bounds loose; they do not prove cached-depth progress.

1e28a69c adds actual ordinary normalization bounds, binder-free open-depth bounds, and InternedStoredPlanBinderDepthOne. build_new_zero follows all source plans of depth at most one from zero-depth lexical inputs. Each final Mu is an exact earlier record or has body depth zero. execute_new_zero retains this through actual stored substitution; unfold_new_zero derives it for closed available input with bodyDepth ≤ 1. unfold_one_decreases proves strict body-depth decrease for every newly allocated Mu when the original bodyDepth is one. The theorem covers the complete final cache and probe records. It requires Facts and availability, but no preparation, complete semantic heap, or supplied successful execution. Earlier Mu and closed captures can have arbitrary depth. This depth-one checkpoint is superseded by the general progress theorem below. Read lean/notes-stored-plan-binder-depth.md.

The temporary Haskell probe /tmp/mcfta-open-rank-native-search.hs checked 1,336 closed and 2,040 sentinel-capturing expressions. It found no stored body whose open depth exceeded the maximum open depth of its two probes. Two retained alias/stutter examples also have equal body/probe depths under the repaired live implementation. The later source induction proves the stronger body/Depth-probe equality. The corresponding staged Lean evaluation was stopped with exit 130 after exceeding its ten-minute cap and is inconclusive. Do not repeat that slow evaluation without a changed strategy.

482cc0e2 proves exact open-depth normalization and full actual source correspondence. InternedOpenDepthExecution.closed_heap and closed_probe_equal derive equality between each actual stored Mu body and its Depth probe, across raw/smart binders, closed captures, canonical hits, and probe allocations. The pure interpreter has exact external-renaming/probe invariance and a static syntax/input bound. build_bound and callback_bound connect it to actual returned values.

de322a41 proves InternedStoredPlanBinderDepthProgress. build_new_lower bounds every new Mu body strictly below the root source-plan depth from zero-depth lexical inputs. execute_new_lower follows the exact stored compiler. unfold_new_lower and unfold_decreases prove strict decrease for every new Mu after actual closed unfolding, including open probe records in the complete final cache. constructed_unfold_decreases derives all heap premises from actual empty-cache construction. No preparation, supplied successful outcome, or progress contract is assumed. execute_heap and unfold_heap preserve the body/probe equality for subsequent source work. The proposed positive-depth property is now proved for every depth.

6132e4f2 proves InternedMuDepthInventory and MergedFreshOrdinaryColdTermination. Canonical issued identities avoid duplicate reservations. collect_complete proves finite actual repaired closed worklists with a dynamic descending body-degree vector and structural pending work. New lower-degree Mu and open probe records are permitted. read_closed covers both public paths, exact effects and cache, retained heaps/coverage, closed resident edges, and all larger bounds. constructed_read_closed derives the premises from actual repaired empty-cache construction. No preparation, fixed future inventory, supplied trace, or external progress law is assumed. Do not repeat individual cold-reader termination.

68e790f0 proves general finite repaired shared traversal. InternedFreshMuUnfoldBudget counts unfinished canonical Mu by degree. Actual replay preserves settled calls. unfold_progress gives strict vector decrease or the identical cache. MergedFreshOrdinaryColdBudget propagates that result through every actual closed collector and public row read. SourceFreshOrdinaryColdSharedTermination.complete combines it with unvisited issued identities and pending length. cold_finite derives a finite actual trace and uniform stable outer/read bounds without preparation, a fixed future inventory, or a supplied trace. constructed_cold_finite derives all cache premises from actual closed empty-cache construction. General individual reader and shared-traversal termination are proved. Do not repeat them.

3dc8f856 proves SourceFreshOrdinaryColdTable. Its actual finite ascending final map has an exact distinct domain, declared nonempty children, and identical allocation-free final-cache replay for every row. cold_table retains complete heaps, coverage, growth/history, resident closed edges, and stable uniform bounds. Do not repeat finite traversal or structural final-table proofs.

9a0df4cb proves SourceRecursiveIntersectionOpenDepthEffects, OrdinaryWork, and NativeOpenDepth. Actual optional binders retain the body/probe heap through exact repaired compilation. All ordinary compiler jobs add no Mu. Bounds.open_depth_heaps follows actual nested evaluation, checked memos, source bodies, completion frames, and continuations. NativeColdTable.cold_node_table and constructed_node_table derive finite repaired output tables from actual successful first native execution, under the existing complete-cache, closed Original input, and checked WordRanges scope. No preparation, supplied trace, or finite future inventory is assumed. Native heap propagation and native-output termination are proved. Do not repeat them.

e70160d6 proves exact guarded final-cache language. MergedFreshOrdinaryGraph uses actual repaired stored unfolding. ExposureCertificate and ExposureCoverage derive complete repaired constructor coverage. ExposureOrigins derives every returned edge's actual repaired epsilon path in each later cache. ExposureLanguage.actual_exact gives exact origins and full guarded row language. SourceFreshOrdinaryColdTableLanguage.trace_table_language_final and cold_table_language identify the complete finite ascending table with the repaired graph in its actual final cache. Both native cold-table theorems now include that equation. Do not repeat this final-cache language proof.

b3008aba defines independent complete guarded meanings for actual stored records and full lexical source syntax. InternedGuardedLanguage proves positivity, ordered child runs, and the actual Mu least-language equation. Support.meaning_free derives semantic support from coherent cached free names, so closed captures are ambient-independent. InternedGuardedConstructors proves actual node/union normalization, unused/bare-self cleanup, and both finish paths. SelfFilter proves actual root-self filtering through real union reconstruction, with equal closed candidates and least languages. StoredPlan.encode_language proves the exact arbitrary nested stored compiler with coherent global lookup and nearest-local shadowing. execute_plan_language and unfold_plan_language specialize it to simultaneous replacement and outer-Mu plans. These compiler/normalization laws now compose with actual execution through e46d3f9e. No opaque execution contract is supplied. Do not repeat the independent semantics, free support, normalization, filter, or compiler proofs.

4457307a proves semantic support for complete lexical syntax from the existing profile and free-name analyses. Smart binders lower root-language bounds through closed candidates. Empty-child filtering accepts no finite term on deleted edges. Stored inputs satisfy these bounds from actual coherent metadata. Only surviving symbolic captures need freshness. The chosen ordinary probe and next reserved interned identity are fresh for those captures. Do not impose freshness for every supplied input; unused inputs may contain the chosen sentinel.

e46d3f9e proves actual repaired source execution and semantic probe-heap preservation together. InternedGuardedExecution.build_language covers all lexical branches, both probes, normalized fresh bodies, canonical hits, and pending heap retention. closed_language gives exact independent language of completed closed source syntax. closed_heap derives the invariant from the empty cache. InternedGuardedStoredExecution.execute_checked proves actual simultaneous replacement language; unfold_checked proves actual outer-Mu language preservation and heap retention for arbitrary available records. No preparation or assumed execution law is used. These theorems do not prove a literal reconstruction identity. Do not repeat them.

e1baab1e propagates the new semantic heap through actual repaired cold worklists, nodeEdges reads, and shared traces. SourceFreshOrdinaryColdSharedRows.constructed_cold_finite_guarded derives its initial invariant from actual closed construction and retains the heap in the finite final table. Do not repeat cold heap propagation.

650c3f05 proves actual growing-cache cold-read language soundness. Every returned edge denotes only independently accepted terms of an original root. SourceFreshOrdinaryColdGuardedSoundness.language_sound, graph_sound, trace_graph_sound, and trace_table_sound derive final-table/graph inclusion into independent root meaning. The visited check is sound for this direction. These are not completeness theorems.

b7201597 proves actual optional intersection binder least-language semantics and independent probe-heap preservation. Bounds.guarded_heaps follows all actual nested native branches. NativeColdGuarded.cold_node_table_sound and constructed_node_table_sound supply a finite stable native table whose accepted terms belong to the independent language of the returned value. Initial semantic heaps and coverage, checked WordRanges, closed Original inputs, source guards, and actual cache effects retain their existing scope. This is not yet an input-intersection language law. Do not repeat native heap propagation.

0258ae86 proves SourceRecursiveIntersectionGuardedInput.original_meaning and input_exact. Original payloads have equal independent stored and copied lexical meanings. Closed available original values have exactly the finite tagged input derivations from the existing input view. The proof uses actual Original syntax and cached payloads. No assumed copy-language contract is supplied.

e8f06e62 defines BinderBudgetLanguage and InternedGuardedBudget. Actual raw Mu steps consume one unfolding budget. Coherent free-name support, fixed-budget ordinary normalization, cleanup without a budget increase, and exact root-self filtering are proved. 19467e4a proves exact actual InputDerivation acceptance at each identical bound for closed available Original records, under every ambient environment. Erasing the budget gives independent stored meaning. This budget is separate from public distinct-term rank. Read lean/notes-unfolding-budget-language.md before new rank work. The later a7b5d94e checkpoint proves raw-to-smart inclusion and strict actual unfolding decrease. The source checkpoint below proves exact canonical budget readback. Do not infer remaining transport from ordinary language equality or the finite Haskell probes. The 600-program unfolding probe found no strict-decrease counterexample; the ordinary-probe check found no budget mismatch across 651 stored Mu records. Both are validation only. Temporary Lean generated-source probes were stopped during slow construction evaluation and supply no quantitative result. All workers are terminal.

9288ec6d proves InternedGuardedBudgetStoredPlan.encode_language and execute_plan_language. The exact arbitrary nested stored compiler retains raw unfolding budgets, canonical captured slots, nearest local shadowing, guards, and child order. unfold_plan_lower proves an accepted exact compiled outer-unfolding plan at a strictly smaller bound for every accepted Mu term. This is before execution. The raw lexical interpretation counts both binder flags as one step; it is not an exact model of smart runtime costs. The later a76a22f1 checkpoint below proves exact smart source execution and canonical budget readback.

50d79bef proves exact actual filtered and normalized binder budget choices. 35e07971 defines InternedGuardedSmartBudget from the existing depth shapes and proves positivity, upward budgets, arbitrary external-name renaming, complete root/free support, and actual captured inputs. a76a22f1 proves InternedGuardedBudgetExecution.build_language and closed_heap through actual complete source execution. The new canonical invariant retains both raw-Mu and empty-local ordinary-probe languages. The existing depth heap supplies exact smart branch selection. Both actual probes, fresh completion, canonical hits, and pending heaps are covered. InternedGuardedBudgetStoredExecution gives exact smart-plan meanings of actual substitution/unfolding and retains both heaps. No source/canonical budget contract is supplied at the closed source entry point. Read lean/notes-smart-budget-execution.md. Do not repeat these proofs.

a7b5d94e proves full raw-to-smart plan inclusion for actual consistent captured records and upward languages. The existing shape fields supply literal-root lower bounds and deep-change separation. InternedGuardedBudgetStoredRefinement.unfold_strict proves strict smaller budgets for actual returned outer-Mu unfolding. No literal reconstruction identity is assumed. 9ca74b4d proves cold/shared budget-heap propagation, available closed values along final epsilon paths, and graph completeness by the ordered measure (term size, unfolding budget, stored value size). SourceFreshOrdinaryColdGuardedExact.trace_table_exact gives exact independent root meaning; trace_table_input_exact gives actual tagged initial input language. SourceFreshOrdinaryColdSized.source_sized supplies general completed closed construction with finite exact node-count classes, size order, and both inverses without preparation or a supplied trace. 081ce3d1 proves native budget heaps and exact independent returned-value table language. Do not repeat these proofs. Read lean/notes-cold-budget-completeness.md.

2e6fb87a proves exact pointwise ordered replay, canonical ordinary row membership, full guarded child traces, and actual empty-child rejection. 6afdfe00 proves literal renamed synchronous row fields and normalized ordinary product membership/rejection. dac5f26b derives this interface from actual checked native ordinary execution at every larger bound and later valid cache. Closed native self-intersection returns the identical record and unchanged physical/domain machine. No kernel-execution or child-language contract is supplied at the native entry point. These results retain the actual domain-specific child map. Do not repeat them.

A live ranked witness refutes the proposed general functional Mu adapter. Read lean/notes-ordinary-product-rows.md and preserve lean/repro/NativeProductRowCycle.hs untracked. L = mu x. a | f(a | f(x | a)) and R = a | f(L | a) are original source states. An enclosing g(L) | g(R) node supplies overlapping alternatives. The actual intersect L R row child differs from the separate public closed intersection of the corresponding source children. Both smart/raw Mu reproduce it; alphabet arities are a:0, f:1, g:1. In one process the child identities were 19 and 20. Unary depths 0..24 still equal input intersection; finite checks are not an unbounded semantic proof or a runtime defect. No production repair follows from identity difference alone. Logs: /tmp/mcfta-product-row-cycle-counterexample-20261014.log and /tmp/mcfta-product-row-cycle-counterexample-current-20261014.log.

f04b8261 proves exact full finite-term language from local related physical rows, explicit deletion reasons, and diagonal product reuse. Functional normalized rows are a proved special case. 4d80735a derives local related rows from actual checked native ordinary calls at all larger bounds and later valid caches. NativeProductRowCycleReadout proves unbounded exact language of the explicit observed finite Mu transcript, distinct literal rows, and a formal obstruction to the general functional adapter. The live dump and focused Python table comparison validate this transcript; verified Haskell extraction remains open. ddef16e6 connects related rows and roots to the actual minimum callback, full ambiguity scan, exact reference compiler result, finite distinct guarded size classes, and both rank inverses. Physical relation closure and completed row extraction remain explicit premises. Read lean/notes-relational-product-rows.md. Do not repeat these proofs.

9b6d9014 proves actual ordered union child witnesses, allocation-free later-cache replay, and exact independent union normalization. It also proves the original Mu operand identities, exact extended key/domain, actual body representative, replayed optional binder, independent least language, successful-call language equations, and complete unfolding equation. 513d2824 derives these branch witnesses from actual checked native completion, both union orientations, and all three Mu branches. Native evaluation derives preservation of incoming semantic and independent-language probe heaps. No kernel-execution or product-language contract is supplied. Read lean/notes-union-mu-branch-readback.md. Do not repeat these proofs.

2083dadf proves exact repaired epsilon origins, complete union normalization origins, final caller-machine readback, and actual native union rows in both operand orders. Actual row membership is exactly successful final-cache member calls and their full edge origins. No product-language or row-shape contract is supplied.

5a8034f8 establishes that general exact RelatedRows.Readback is also too strong, even with multiple representatives. Preserve lean/repro/UnionDiagonalRows.hs untracked. X={a,b}, Y={b,c}, A=f(X)|f(Y), U=A|mu x.h(x). Actual intersect U A returns the identical A. The live cross row f((X,Y)) needs exact child language {b}, but returned children have {a,b} and {b,c}. UnionDiagonalRowBoundary proves no exact relation can describe this explicit graph and separately proves full correct root language. The graph has ambiguous f rows. The direct intersect call and original exposed roots were observed; a complete short-circuit ambiguity scan was not recorded. No semantic defect or refutation of an unambiguous-only interface is claimed. The transcript is validated, not verified Haskell extraction.

DirectionalRows proves language inclusion from local directional row coverage with complete guard implications and ordered children. Separate reverse coverage proves exact full language. Older exact related rows supply both directions. DirectionalProduct proves structural right projection and reverse diagonal copies from literal row inclusion; UnionDiagonalRowCoverage closes the witness without a language premise. 1f2aa0c6 connects both directional simulations to the actual native minimum callback, full ambiguity scan, exact compiler result, finite guarded size classes, and both rank inverses. The two physical simulations and completed extraction remain explicit premises. Read lean/notes-directional-union-rows.md. Do not repeat these proofs.

The full kernel/native product language is now proved. Read lean/notes-native-product-language.md. 3d9fd615 proves exact ordered hash joining, full actual branch selection, complete fuel induction in one final cache, original-view transport, exact closed original-input product language, and the actual checked native API law. The semantic bound is twice kernel fuel. No recursive-call, row-relation, or product-language premise is supplied at the native entry. 0f32ad39 derives finite stable actual native cold tables, constructed-source heap invariants, exact distinct node-count classes, finite class evaluation, size order, rank coverage, both inverses, finite minimum convergence, the least common structural size, and the raw-table productive Boolean.

Next compose the actual complete native overlap callback and finite source-key scan with the new language and minimum laws. First retain finite exact cold extraction after arbitrary completed warm native calls. native_product already covers these calls; the current existential cold-table wrappers start from initial memo state. Then connect the actual nodeEdges precheck in Gen/Internal/Automaton.hs to the root minimum. A present minimum yields an accepted term, so exact repaired exposure must have a root edge. An absent minimum gives false for either precheck result. Literal root-row equality is sufficient but not required. Derive source-key operand language from actual input cold traces and resident original closed values. Prove each callback Boolean, preserve the real constraint precheck and ordered scan, then reuse existing compiler and Sized sequence theorems. Do not assume whole product language or derive either refuted exact row adapter. Keep checked WordRanges, actual native validity, and the source extraction/runtime boundaries explicit. The primary finite-map reference, solver-decided, and optimized Sized proofs remain. Keep the optimized interned core. Follow actual substitutionPlan; raw-binder literal reconstruction identity remains refuted.

Retain checked WordRanges, Original syntax, full guards, exact source/domain effects, both memo families, publication before demand, ordered operands, shifted keys, reversed swaps, RecIntersect bypass, original finish frames, and yielded continuations. Universal PreparedWithoutMu preservation remains refuted. Native SCC/split readback, custom decoder order, general equality propagation, and concrete runtime correspondence remain open. Preserve all marked drafts and counterexamples.

After PR #122, all 208 generator and 145 refinement examples passed in Nix. The unchanged core retains its earlier 289 passing examples. Fourmolu passes for the changed synthesis module. Logs: /tmp/mcfta-synthesis-memo-refresh-20261014-tests.log and /tmp/mcfta-synthesis-memo-refresh-20261014-format.log. The active Cabal files did not change, so their prior gild checks remain applicable. Fourmolu and cabal-gild pass for the active microcfta packages. Logs: /tmp/mcfta-state-label-refresh-20261014-tests.log and /tmp/mcfta-state-label-refresh-20261014-format.log. The broader cabal-gild check reports existing formatting failures in the unchanged legacy microecta and microecta-generator Cabal files; leave those unrelated files unchanged. No new production test was added locally. Use the pinned Lean 4.34.1 binary, focused checks for changes, and the aggregate audit for completed modules. Do not repeat passing checks without a new reason. No sorry, native evaluation axioms, or project axioms. Handwritten models and test results do not establish verified Haskell extraction or whole-library completion.

Push completed checkpoints regularly to origin/formalize. Do not deploy, send messages, or post to the board. Keep the optimized interned core. Do not formalize benchmark programs, datasets, or workload specifications. Do not update memory or create an ADR without a request. Address Matti in English, timestamp every response, give brief material updates, and work without asking whether to continue.

Monitor weekly allowance before work and regularly afterward with python3 /tmp/mcfta-weekly-usage.py. Check observed_at. The script includes the next UTC date directory because logs can use the local date after midnight. The 32% reading at 08:32 CEST on 2026-10-14 is historical. Stop all work and workers immediately at 1% remaining or less. This latest explicit user threshold supersedes older 20% notes. Missing or stale usage is not permission to use credits.
