# Finite class scans with the current conjunction decision

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`2805ce87`. Proof commits are `79a00157`, `14fcff90`, `d03bced1`, and
`e103bb55`.
This update changes no Haskell implementation or test. Root FINDINGS.md
retains the Haskell fix handoff for external work.

## Actual physical traces supply the next conjunction call

SourceCurrentAllocatedNativeTraceEffects.effects starts from an actual
checked physical Trace and initial Good, SemanticReady, and stored costs.
Trace.plan supplies the reached physical checks through the final return.
The same literal result and checked state derive final Good, physical
conjunction Effects, and native Extension. No final invariant, semantic
result law, or completed child callback is an input.

SourceCurrentAllocatedConjunctionMemo uses the current allocated conjunction
Call at the actual constructor heap and equality-operation state.
Its finite endpoint needs no preceding native query or supplied decision.
The returned physical effects derive checked validity, SemanticReady,
stored costs, and Idle. Both native memo tables and the domain cache stay
literally equal. Existing contextual laws and syntactic scopes survive
because their returned cells stay equal. This does not admit a new model.

## Checked seeded queries retain actual allocation histories

SourceCurrentAllocatedSeededQuery.Operand records an actual Forest projection.
It advances the same native state and retains the equality-operation cache.
Fold projects its head, completes the remaining fold, and runs the literal
checked empty-domain request on the head and tail values. Seeded rotates the
first source path to the final seed position. It calls no merge operation.
The empty path list returns literal empty with the whole state unchanged.

Operand, Fold, and Seeded derive uniqueness of both the result and the
complete checked state. The graph constructors require no result law,
final invariant, completed native callback, or physical effect bundle.

FoldRanges checks only native WordRanges at actual completed projection
and tail prefixes. Tail completion is proved independently. These prefixes
are antecedents to checks. The plan does not assert that they complete.

Finite completion uses the false secondary gate's anchored path support.
Unrelated original children may remain open. Each projected operand is
closed and available. Earlier tail completion derives the same properties
for the tail result at its actual returned heap. Coherence then derives
Original syntax for both operands with closed_original. ScopeCompletion
derives the next actual native return, Scoped cache, Idle, and closedness.
The physical trace theorem derives loaded fields and stored costs there.
The same native tables and equality-operation state pass to the next step.
No native table is reset between requests.

false_class_complete includes the actual secondary gate's effects. It
returns one finite Seeded at that gate's returned anchor, plus Good,
physical Effects, native Extension, Scoped, Idle, and a closed resident
query. It supplies no input language model or exact intersection law.

## Current class Scan completes without a supplied Scan

SourceCurrentConjunctionClassScan.Scan records only reached original classes.
A false primary gate selects the class. A true primary gate runs the
current secondary gate. A true secondary gate skips the query. A false
secondary gate runs the checked Seeded and the CURRENT conjunction memo.
A false memo answer continues from its actual returned state and memo.
A true answer stops before the class suffix.

Selected records keep their order and repeated occurrences. On rejection,
they describe only the reached prefix. They are not a fully forced selected
partition. This matches the source partition and refused any schedule.

SourceCurrentConjunctionClassScanCompletion.finite derives the entire finite
reached Scan from initial Good, SemanticReady, stored costs, Scoped, Idle,
available original values, proper paths, correct fourth memo, and Ranges.
Ranges supplies only reached seeded native checks and recursive checks after
actual false memo answers. It supplies no future successful callback,
completed Scan, desired result law, or final invariant.

The result derives final readiness, physical Effects, original-value
retention, fourth-memo Correct, and preservation of earlier memo entries.
It uses the current conjunction decision on misses. The historical Scan
and its native-intersection emptiness body are not premises.

## Original allocation histories derive the current entry

SourceCurrentConjunctionClassHistoryEntry.constructed derives the new
Scan.Ready from one covered causal field history and actual source build.
The earlier original-entry theorem supplies Good and SemanticReady.
The existing construction theorem supplies stored costs. Empty native
tables derive Scoped and Idle. All components refer to the same literal
checked state and retained equality interner.

finite then constructs the current Scan without a supplied initial-ready
bundle or historical Scan. cold_finite also derives initial correctness of
the empty fourth memo. Source construction, field coverage, available
forest values, proper original paths, and reached ranges remain explicit.
Only the modeled native, domain, and completed operation tables start cold.
The equality interner is retained. No Haskell global reset is claimed.

## Remaining semantic and runtime obligations

The new Scan theorem proves finite physical execution. It does not prove
that rejection refutes a satisfied original class. Current memo soundness
excludes terms in its query. The caller must still show that the seeded
query contains every common satisfying subtree of the original paths.

The fixed-model contextual proof admits listed original operands. Physical
residency, closedness, and Original syntax do not imply validity in that
fixed model. Reanchoring the scope proof at the current heap is sound for
physical completion. It does not revalidate existing semantic cache laws
in a new model. The next proof must extend the input model and transport
earlier contextual laws, or derive an equivalent semantic cache invariant
from the actual history. Do not infer this transport from scope validity.

Then derive common-subtree inclusion and stopped-class soundness for this
current Scan. Compose actual allocated precheck records and their returned
operation state, the three global gate memo receipts, selected required
paths, and the general constrained outer caller. Arbitrary warm operation
tables, full cache admission, GHC forcing and publication, allocation order,
concurrency, concrete containers, and machine capacity remain explicit.
Every other full-library and separate Sized contract remains active.
Keep the optimized interned core and all older constructor/equality proofs.

## Validation and preservation

The pinned full Audit passes 2305 jobs and 56121 theorem dependency checks.
Focused validation passes 29 public axiom reports, 29 signatures, 28 kernel
examples, and one named kernel theorem with its additional axiom report.
Only propext, Classical.choice, and Quot.sound occur. Canonical builds replay
the existing unused-input warning. Independent reviews found no material
defect in the native effects, seeded completion, or current scan composition.

Evidence and frozen source copies are repository-local under
restart-evidence/20261016-conjunction-scan/. Failed intermediate logs stay
unchanged. The validation record identifies successful final logs.
All 3401 baseline files remain. All 2298 older non-Audit proof sources
retain identical bytes. Earlier unavailable external drafts are not claimed
recovered or reverified.

No Haskell source or test bytes change. Reuse the unchanged-source strict
Nix all-component build, 777 examples plus golden, five-file Fourmolu, and
four-package Cabal-gild evidence in root FINDINGS.md.
The full-library goal remains active. This checkpoint is progress.
