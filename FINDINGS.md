# Current formalization findings

## Haskell fix handoff for external work

Audited source main is `c0cc8a05`, merged into `formalize` at `896b0a1c`.
PR #64 adds drawn typing fields. PR #65 repairs the recursive field-pool
finding below with `FieldAtomOnDatatype`. The historical "confirmed, unfixed"
entry describes source before that repair. Its reproducer and earlier logs
retain their bytes. The earlier negative-bound and named-measure repairs
remain included. The optimized interned core and Sized implementation do
not change. No additional local Haskell behavior patch is added.
The only local Haskell-tree differences are the retained constructor
changelog entry and reproducer comment.

The current static native budget proof adds no Haskell change.
Reuse the source validation below for the unchanged source `c0cc8a05`.
For external handoff, record every later repair here with its failure,
executable reproducer, affected paths, commit, checks, and upstream status.
Keep current repair status before historical failure reports.

Current source validation is recorded in
`lean/restart-evidence/20261016-drawn-fields-local-worker/`.
The strict Nix all-component build passes with `-Werror`, tests, and benchmarks.
All six suites pass: 321 core, 240 generator, 180 refinement, 35 GHC-fit,
and 22 decision-model examples, plus the hole-fit golden check. This is
798 examples plus golden. All six incoming Haskell files pass Fourmolu.
All four active packages pass Cabal-gild and metadata checks. The unchanged
Chain reproducer now returns `Left (FieldAtomOnDatatype "Next" 0)`.
Read `source-validation.md` and `source-derive-self-field.log` in that directory.
Standalone `holds` still treats the supplied pool as opaque. The repair
rejects the invalid derivation configuration; it does not change that evaluator.
The current pinned Lean Audit passes: 2562 jobs and 59773 dependency checks.
These checks preserve the distinction between component proofs and the
remaining frontend and runtime correspondence. The new drawn-field states,
errors, validation order, and generator-specific rank order need adapters.
The previous audited source was `5399d310`, merged at `82d47236`.
Use the current source before applying an older repair. The entries below
separate a behavior fix from a remaining documentation change.

- **Recursive field-pool repair: merged and locally validated.**
  Repair `b9219b9e` is merged by PR #65 at `c0cc8a05`. For
  `data Chain = End Bool | Next Chain`, a child pool containing `End False`
  could generate `Next (End False)` while `holds` accepted an invariant
  that requires `End True` at each Chain node. The repair rejects a field
  pool whose field type is the datatype being derived. It returns
  `FieldAtomOnDatatype "Next" 0` for that example. It does not silently
  filter the supplied subtree. Affected paths are
  `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs`,
  `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive/Internal.hs`,
  `cfta-generator/test/Data/CFTA/Gen/Refinement/DeriveSpec.hs`, and
  `cfta-generator/CHANGELOG.md`. The new regression expects that error
  even with a trivially true invariant. The original executable counterexample
  remains in the preceding evidence directory, as recorded below.
  Local merge `896b0a1c` includes the repair. The strict Nix build and all
  798 examples plus golden pass. The unchanged original reproducer returns
  `Left (FieldAtomOnDatatype "Next" 0)`. Read
  `lean/restart-evidence/20261016-drawn-fields-local-worker/source-derive-self-field.log`.
  Its standalone `holds` checks remain `(True,True,False)`: this repair
  rejects the derivation configuration rather than validating opaque pool
  descendants. The new error and its validation order still need a source
  adapter. No additional local Haskell patch is added.
- **Negative typed-language bounds.** Upstream repair `443e3458` is included
  in PR #62 and main `999c04a5`. It changes
  `cfta-generator/src/Data/CFTA/Gen/Typing.hs` and
  `cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs`, with the corresponding
  entry in `cfta-generator/CHANGELOG.md`.
  Previously, `Nesting (-1)` and `Binders (-1)` could admit alternatives
  without subterm fields, as a zero bound does. The public
  `typingAutomaton` now rejects either negative bound with
  `NegativeBound bound` before it validates the node view. `fromTypingRules`
  uses that validation. Reproduce with `fromTypingRules @Arith
  (Typing bound [] [IntType] arithRules)`, where `bound` is `Nesting (-1)`
  or `Binders (-1)`. The regression "take a bound that is not negative"
  expects the corresponding error for both and no error for `Nesting 0`.
  The same commit corrects the environment-size documentation: with at most
  B binders in a field and nesting bound D, an environment has at most B * D
  binders. The three regression assertions pass in the current generator
  suite. No local repair is needed. The source adapter for this new error
  and its validation order remains open.
- **Recursive field-pool invariant: confirmed, unfixed.** Current main
  `999c04a5` accepts a field-specific pool for a field of the root datatype.
  The path was added in `d0966953`. With `data Chain = End Bool | Next Chain`,
  require `End True` at each Chain node and give Next's child the pool
  `[End False]`. `deriveLTAFrom @Chain 0` succeeds and enumerates
  `[End True, Next (End False)]`. The latter violates the independent
  all-node invariant, but `holds` returns `True`. The reproducer uses a
  lawful nonnegative `Literal Chain` encoding.
  Affected code is `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive.hs`
  (`fieldAtoms` and `evaluate`) and
  `cfta-generator/src/Data/CFTA/Gen/Refinement/Derive/Internal.hs`
  (`derivation` and `alternativeGenerator`). Field-pool generation bypasses
  recursive derivation; value evaluation returns `below=True` for that field.
  Run `nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc -package=cfta -package=cfta-generator lean/restart-evidence/20261016-frontend-node-view-refresh/derive-self-field-draft.hs'`.
  The successful terminal-zero output is in `derive-self-field-retry.log`
  in the same directory. The frozen file retains its historical draft comment;
  it was subsequently executed. This focused counterexample passes as a
  program; all 791 existing examples still pass.
  No repair commit or local patch exists. The advertised each-node contract
  and opaque supplied-subtree interpretation give different languages.
  Settle that contract before a behavior repair. The old type-wide atom also
  makes `holds` skip descendants, but the high-level derivation then rejects
  the root annotations as `UnknownConstructors`. The new field-local case
  keeps the root derived and succeeds. Do not conflate those two cases.
- **Named measures over open integer children.** Upstream repair `1b3ebf09`
  is included in PR #54 and main `eda6919b`. It changes
  `cfta-generator/src/Data/CFTA/Gen/Refinement.hs` and
  `cfta-generator/src/Data/CFTA/Gen/Refinement/Internal/Compile.hs`.
  Previously, `measuredBy` required an integer value for a child's named
  measure. A child built with `every` could therefore cause `InexactMeasure`.
  The repair retains symbolic measure terms and substitutes named reads
  before open-node counting. No additional local patch is needed.
  `cfta-generator/test/Data/CFTA/Gen/Refinement/DeriveSpec.hs` contains the
  regressions. Sorted lists of length three over keys zero through nine
  have cardinality 120 and match explicit enumeration. Keys zero through
  one million have cardinality 166666666666500000. The last rank decodes
  to `[999998, 999999, 1000000]`. Both regressions pass in the current suite.
  The complete source correspondence for this frontend remains open.
- **Finite typing metadata discovery.** `ca0e9a65` fixes
  `cfta-generator/src/Data/CFTA/Gen/Typing.hs`. Before the fix, two leaf rules
  could force the description of an unused non-regular field forever.
  The declaration-position walk now visits only constructor types present
  in the finite typing rows. It retains each type's full declaration indices.
  Upstream adopts the same implementation in `b3f4de44` and PR #53.
  The current file matches main. No additional patch is needed.
  `cfta-generator/test/Data/CFTA/Gen/TypingSpec.hs` now contains the regression
  "reads only the types of the rules, so a non-regular field that no rule uses
  does not stop it". Its expected result is `Right [Plain, Other]`.
  The declaration-order regression also checks `Right [Lit Z, Lit A]`.
  Standard `Bool` uses `False` before `True`; the old contrary comment is fixed.
- **Fresh recursive constructor probes.** Historical repair `fbc3097`
  (formerly `e0e1b37`) changes the old
  `microcfta/src/Data/CFTA/Interned/Type.hs`, now
  `cfta/src/Data/CFTA/Interned/Type.hs`. It selects a probe above captured
  ordinary references and uses the same observation in `matchMu`.
  The old protocol can demand an unfinished interning result on a closed
  nested expression. See `lean/notes-paired-pending-boundary.md` and
  `lean/notes-fresh-ordinary-candidate.md` for the counterexample and repair.
  The current implementation file matches main. The extra local changelog
  entry records this historical repair; it is not an outstanding code patch.
- **Constrained recursive equality endpoint.** The retained reproducer is
  `lean/repro/OuterCallerCycle.hs`. Current main includes the endpoint guard
  and emptiness checks. The only remaining local difference in
  `cfta/src/Data/CFTA/Equality/Operations.hs` is a comment that names that
  reproducer. Do not treat that comment as a separate behavior fix.

PR #55 (`47b06bbe`, merged at `8f85ddb6`) exposes `typingAutomaton` and
`fromConstructorAutomaton`. `fromTypingRules` now takes a `Typing` record.
At that checkpoint, nonempty root inputs and `Binders` returned
`NotImplemented`. PR #57 now implements inputs, and PR #59 implements
binder bounds and removes that error constructor. The finite
needed-type discovery repair remains in the new decoder helper. Existing
typing proofs retain their earlier interfaces; the new public wrappers,
validation order, and `Maybe Int` state representation need source adapters.

Validation at the earlier PR #55 refresh: the strict Nix build of all components
passes. All six existing suites pass: 321 core, 231 generator, 169 refinement,
34 GHC-fit, and 22 decision-model examples, plus the hole-fit golden check.
This is 777 examples plus golden. Five changed Haskell files pass Fourmolu.
All four active packages pass Cabal-gild. Evidence is in
`lean/restart-evidence/20261016-physical/source-pr55-strict-build.log` and
`lean/restart-evidence/20261016-physical/source-pr55-tests.log`.
No local test file is added or changed.
Inspect `git diff origin/main -- cfta cfta-generator cfta-ghc decision-model`
to identify an outstanding source patch. Add each later Haskell fix here
with its failure case, affected file, commit, checks, and upstream status.

## Current input-derived native reservation budgets

Audited source main is `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `fcb5fdeb`. Read lean/notes-current-native-budget.md
and lean/restart-evidence/20261016-constrained-native-budget/.
Six additive modules derive static budgets for one ordinary native query.
Proof commits are `6f53e07d` and `9f985068`.

NativeProfile computes uniform row and arity limits for all original operand
occurrences. With limits R and A, N(0)=1,
N(h+1)=1+R*R*(1+A*N(h)), and E(h)=1+A*N(h). Node and edge budgets use the
maximum original operand height. They contain no query execution or actual
request-count premise. The full expansion counts repeated subproblems.
Memo hits can skip their work. A swap retains the same budget.

NativeBudgetCode composes literal Work, recursive calls, ordered walks,
and finish frames. NativeBudgetCompile proves the actual node dispatcher,
joined rows, accepted child zip, and rejected sentinel fit their budgets.
NativeBudgetExecution retains remaining budget through every actual yielded
prefix. Fixed-source Origins identify the exact captured evaluating owner.
Only literal Work consumes the two constructor request counters.

Principal node/edge theorems derive the code certificates from initial
Good, resident finite ordinary operands, and initial Capacity. They bound
total actual constructor requests and both supply increments. Initial supply
plus the computed budget fitting the two key layouts derives Capacity at
EVERY yielded prefix. No completed query, future readiness, future capacity,
returned result law, or bound on the actual request list is supplied.
This result counts constructor requests. It does not bound instruction steps.

Next derive output row and arity envelopes at the same actual returned
state, including warm result hits. The existing domain/height certificates
are insufficient. The rejected sentinel has one Empty child even when the
input arity is zero. Then compose required, projection, merge, edit, class,
and outer cumulative budgets. Read next-outer-budget-review.md.
The root numeric plans remain explicit until that composition is proved.

The full Audit passes 2562 jobs and 59773 dependency checks. All 75 declared
public axiom/full-signature pairs and 20 integration pairs pass. Coverage
resolves nested Bound and ControlBound namespaces. Only permitted
foundations occur. Preservation retains 6768 starting files and 2555 older
non-Audit sources. Forty frozen manifests check 319 module entries. All
older repairs, drafts, counterexamples, stashes, other worktrees, and the
optimized interned core remain.

The current domain admits arbitrary guards and equality classes. It excludes
Mu, references, and explicit unions. General recursive progress, repeated
passes, current frontends, concrete Haskell execution, and full-pipeline
composition remain open. Retain the separate language, transformation, size,
count, order, both rank inverses, generator, and probability contracts.
Equality/sidecar/thunk supplies, host interleavings, losing concurrent
candidates, lazy forcing, and signed host counters remain separate.

No Haskell changes. Reuse strict Nix validation, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild and metadata checks. Repair
`b9219b9e` is already merged by PR #65. Root FINDINGS keeps the external
Haskell repair handoff first. Record every later repair there with failure,
reproducer, paths, commit, checks, and upstream status. The full-library
goal remains active.

## Current numeric ordinary root admission

Audited source main is `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `8b0a9fc1`. Read lean/notes-current-outer-admission.md
and lean/restart-evidence/20261016-constrained-outer-admission/.
Five additive modules lift numeric capacity plans through the whole
ordinary root. Proof commits are `9217348e` and `efb4338c`.

OuterNumericEntries.Plan contains only parent capacity at actual raw reached
edge bodies. Admission records the current Context, Stored, inherited
readiness, and resident domain inputs. Its inventory and global bundle can
change after an earlier prefix. Neither predicate assumes a completed
current or enclosing root.

OuterParentReads aligns a supplied parent return with its own constructed
strict producer. Whole-return uniqueness retains the result and every state
component. OuterRawReads constructs strict reads for all eight supplied raw
families. Mutual induction verifies smaller earlier graphs in literal order.
Their exact Post, domains, and structural certificates supply later entries.

OuterAdmission proves admission through the unchanged raw Step/Reach
relation. Only then does it derive the old OuterEntries.Plan from numeric
parent capacity. OuterNumericRoot uses the frozen strong rank theorem to
construct its own complete root graph, reads, Checks, full Post, structural
bound, independent language law, and stable literal execution. Constructed
and prepared roots derive their own source root and initial Context.
Static syntax counts add INITIAL capacity at that same constructed heap.
The imported warm-reuse kernel returns the same result and complete caller
at all ten zero worker bounds.

Numeric plans for later queries remain explicit. This closes the raw-Reach
admission gap. It does not derive a priori total reduction reservation
budgets from initial resources. Next bound native query requests from a fixed
input operand inventory. Then compose Target, merge, leaf, and rebuild
budgets. Count losing and intervening reservations. Keep equality-interner,
modeled packed-key, signed host-counter, and lazy forcing bounds separate.
Read next-budget-review.md in the evidence directory.

The full Audit passes 2556 jobs and 59607 dependency checks. All 22 declared
public axiom/full-signature pairs and 12 imported integration pairs pass.
Only the permitted foundations occur. Preservation retains 6682 starting
files and 2550 older non-Audit proof sources. Thirty-nine frozen manifests
check 313 module entries. All older repairs, drafts, counterexamples,
stashes, other worktrees, and the optimized interned core remain.

The finite ordinary domain admits arbitrary guards, equality classes, and
unequal path lengths. It excludes Mu, references, and explicit unions.
General recursive progress, repeated-pass convergence, current frontends,
concrete Haskell execution, and full-pipeline composition remain open.
Retain separate exact language, transformation, size, count, order, both
rank inverses, generator, and probability contracts.

No Haskell changes. Reuse strict Nix validation, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild and metadata checks. The
recursive field-pool repair `b9219b9e` is already merged by PR #65. Root
FINDINGS.md keeps the external repair handoff first. Add every later repair
there with failure, executable reproducer, paths, commit, checks, and
upstream status. The full-library goal remains active.

## Current numeric query capacity and reservation bounds

Audited source main is `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `a86c09dd`. Read lean/notes-current-constrained-capacity.md
and lean/restart-evidence/20261016-constrained-query-capacity/.
Thirteen additive modules derive causal numeric query plans and reservation
bounds. Proof commits are `baffd471`, `a66edeb5`, and `bb913e55`.

Capacity contains only current node/edge supply inequalities at width bits+2.
Target, Force, Leaf, simultaneous edits, Class, Pass, Scan stage, precheck,
and Parent derive existing range checks from numeric plans. Each suffix uses
only an earlier actual prefix return. Shorter-prefix induction derives its
checks before constructing or verifying that prefix. Complete worker
uniqueness identifies the same output and every returned state component.
Finite endpoints construct their own graphs, reads, receipts, domains, and
structural bounds. Numeric outer edge calls retain full Post, independent
language law, causal certificates, and stable literal execution.

Primitive Work observations count actual requests and cache misses. Exact
counter equations count every reservation, including losing atomic
candidates. Raw yielded native prefixes retain those equations without a
completed receipt or query. Their request-budget adapter still takes a
bound on the ACTUAL prefix request count. It is not a static total-work
bound for reduction. Equality-interner and host reservations remain separate.

Ordinary source construction has STATIC input-only bounds: node occurrences
bound node reservations and row occurrences bound edge reservations. It
constructs its own successful return from any heap and environment. Initial
Facts and resident domain inputs add the same result domain and residency.
Closed construction and field preparation derive complete initial Context,
three structural certificates, actual empty inherited identity, and initial
Capacity whenever the syntax counts fit. Later query capacity remains open.

The earlier whole-root endpoint still requires OuterEntries.Plan. Its raw
Reach relation needs a separate admission proof at every entry. Next verify
earlier raw graphs through all eight outer families, construct their reads,
and derive Context, domains, and Stored at each reached parent. Only then
can numeric parent plans imply the frozen global range plan. Read
outer-capacity-next-review.md. Do not use enclosing root completion or
future readiness to prove its own plan. Derive total reduction reservation
budgets from initial resources after that numeric composition.

The full Audit passes 2551 jobs and 59587 dependency checks. All 88 declared
public axiom/full-signature pairs and 39 imported integration pairs pass.
Public coverage includes indented mutual and noncomputable declarations.
Only the permitted foundations occur. Preservation retains 6528 starting
files and 2537 older non-Audit proof sources. Thirty-eight frozen manifests
check 308 module entries. Historical repairs, drafts, stashes, other
worktrees, and the optimized interned core remain.

General Mu/reference/union progress, repeated-pass convergence, current
frontends, concrete Haskell execution, and full-pipeline composition remain
open. Retain separate exact language, transformation, size, count, order,
rank/inverse, generator, and sampling contracts. No Haskell file changes.
Reuse strict Nix validation, 798 examples plus golden, six-file Fourmolu,
and four-package Cabal-gild and metadata checks. Root FINDINGS.md keeps
the external Haskell repair handoff first. Record every later repair there
with failure, executable reproducer, affected paths, commit, checks, and
upstream status. The full-library goal remains active.

## Current finite ordinary query word bounds

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `1bbb75c4`. Read lean/notes-current-constrained-query-words.md
for the current top-level objective, proof map, and missing areas. Evidence
is in lean/restart-evidence/20261016-constrained-query-words/.
Seven additive modules remove future word checks from one native query.
Proof commits are `ae8b53b5` (initial keys and raw actual prefixes) and
`ee54b123` (Scan checks, supplied reads, and bounded finite completion).

Recursive key certificates derive from initial resident ordinary records
and initial node/edge supplies. The static actual code requests only original
operand subrecords. Fixed-source memo origins retain captured operands in
all phases and place no condition on returned identities. Raw actual
Demand.Steps derive every reached word check without a completed physical
Trace, future readiness, or a final result premise.

Words.node/edge derive checked WordRanges from initial Good and recursive
operand keys. Their domain adapters use only initial supply bounds at width
bits+2. BoundedFinite constructs its own complete native Receipt and retains
final physical invariants, semantic readiness, structural tables, domain,
and both original height bounds. Initial Good, SemanticReady, Stored, Idle,
and resident domain operands remain explicit. No future WordRanges is input.

ScanRanges derives ordinary Scan-only checks. OuterVerification derives
Checks, full Post, structural bounds, and independent language laws for all
eight supplied actual strict read families. It verifies a supplied graph;
it does not construct the graph. The earlier constructed finite ordinary
root still requires its independently reached parent entry range plan.

Next derive numeric capacity at actual Target/Leaf query entries, then bound
primitive reservations from initial resources. Generated earlier results
need fresh identity bounds when used as later operands. Height and domain
alone do not give those bounds. General Mu/reference/union progress,
repeated-pass convergence, current frontends, concrete Haskell execution,
and full-pipeline composition remain open. Exact size, count, ordered rank,
both inverses, transformations, and sampling retain separate contracts.

The full Audit passes 2538 jobs and 59423 dependency checks. All 76 declared
public axiom/full-signature pairs pass. Imported kernels retain raw prefixes,
complete warm owners, initial counter boundaries, actual supplied-read
prefixes, and two constructed queries at the same actual warm return.
Only the permitted foundations occur. Preservation retains 6422 starting
files and 2530 older non-Audit proof sources. Thirty-seven frozen manifests
check 295 module entries. Older repairs, drafts, stashes, other worktrees,
and the optimized interned core remain.

No Haskell file changes. Reuse strict Nix validation, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
The field-pool repair b9219b9e is already merged by PR #65 and validated.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
every later repair there with failure, executable reproducer, affected paths,
commit, checks, and upstream status. The full-library goal remains active.

## Current constrained finite ordinary outer completion

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `f5a20d96`. Read lean/notes-current-constrained-outer-completion.md
and lean/restart-evidence/20261016-constrained-outer-structure/.
Eleven additive modules construct conditional finite ordinary root execution.
Proof commits are `4cd272b3` (source construction and causal admission),
`c7d0529e` (all eight completed structural families and finite edge calls),
and `bfa5504c` (entry checks, strong node induction, and constructed roots).

Source syntax constructs its own successful root and finite ordinary domain.
Actual field preparation derives history, full Context, the actual empty
inherited identity, and cold native/merge/outer structural certificates.
Warm callers retain their separate causal certificates and complete owners.
All eight actual strict read families retain domain and input-relative height
bounds at the SAME actual returned caller. Rows use narrowed parent results.

Entry controls require no result or enclosing completed graph. The range
plan checks each independently reached parent entry BEFORE its execution.
Completed earlier prefixes reach later siblings at their actual warm states.
This avoids the old success-conditioned WorkerRanges gap. Native machine
and allocation range checks remain explicit. No future readiness, successful
body, result law, or finite future-key inventory is supplied.

Strong Nat node-rank induction discharges the smaller-node interface.
The parent height bound makes each generated child strictly smaller than
its ORIGINAL edge. Node.finite constructs its own graph, strict reads,
Checks, full Post, structural certificates, and independent language law.
Root.constructed_root/prepared_root compose source construction and actual
preparation with stable literal root execution and full language equality.
Every larger tuple of all ten worker bounds returns the same result and
complete caller. This covers one ordinary constrained pass, conditional on
the entry range plan. Guards, equality classes, and unequal path lengths
remain unrestricted in this domain. Mu, references, and explicit unions
remain outside it. The old plain Region remains a separate proof domain.

Next derive the entry plan from concrete key/allocation bounds and machine
capacity. Read next-capacity-review.md in this evidence directory. General
Mu/union/reference progress, repeated-pass convergence, current frontends,
concrete Haskell execution, and full-pipeline composition remain open.
Retain all separate language, transformation, Sized, rank/inverse, generator,
and probability contracts and the older constructor/equality work.

The full Audit passes 2531 jobs and 59275 dependency checks. All 50 declared
public axiom/full-signature pairs pass. Imported integration probes retain
actual prefixes, cold admission, exact language/structure composition, and
all-zero-bound warm reuse. Only the permitted foundations occur.
Preservation retains 6259 starting files and 2519 older non-Audit proof
sources, with only named restart-authority changes and additive Audit imports.
Thirty-six frozen manifests check 288 module entries. Historical repairs,
stashes, other worktrees, drafts, and the optimized interned core remain.

No Haskell file changes. Reuse strict Nix validation, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
every later repair there with failure, executable reproducer, paths, commit,
checks, and upstream status. The full-library goal remains active.

## Current constrained finite ordinary parent bounds

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `9bff0326`. Read lean/notes-current-constrained-parent-bounds.md
and lean/restart-evidence/20261016-constrained-class-structure/.
Twelve additive modules prove actual class, local, and parent bounds.
Proof commits are `00484d33` (narrowing and owner certificates),
`373dd9cd` (metadata, Scan, receipts, and edits), `ea8b2e1a` (Class/Pass),
and `095e5f71` (actual local and stable parent composition).

Coherent finite ordinary records derive zero cached Mu depth and empty
free names. Every actual primary Scan is false at the same heap. The Scan
selects the complete source class list, returns no rejected class, and
retains the exact checked state and fourth memo. Strict reads retain the
same global bundle. No seeded query occurs on this domain.

Actual target/leaf receipts derive structural certificates without a
uniform future range plan. Shared-edit induction retains native results,
merge results, target slots, and positional Language.All₂ height bounds.
Class starts fresh slots. Its right fold captures the ACTUAL tail forest
and warm tables. Required paths and final propagation retain positional
bounds. Full guards, nonempty equality classes, and unequal path lengths
remain admitted by this finite ordinary stage.

Stage and Local derive their structural results at exact actual prefixes.
Parent.finite constructs its own graph, strict reads, full receipt, and
stable literal execution. Every larger nine-bound tuple returns the same
edge, full checked state, fourth memo, and merge memo. The returned edge
has domain children and height bounded by the ORIGINAL edge. Initial
readiness, semantic admission, causal warm tables, and reached ranges
remain explicit. No future body, successful worker, or result law is input.
Raw rejected_finite needs no original domain, child availability, field,
inherited readiness, or range plan.

Returned.Stored gives both outer result families conditional domain and
height certificates tied to their actual captured owners. Exact begin,
demand, advance, finish, warm readback, and strict returned-child rank
lemmas pass. Next prove structural preservation through all eight actual
outer families, then construct strong-rank finite recursion. Read
next-outer-completion-review.md. Lifecycle laws and stable parent execution
do not yet complete the outer caller. Machine-range derivation, general
Mu/union/reference progress, repeated passes, current frontends, concrete
Haskell runtime, and full-pipeline composition remain open. All separate
language, Sized, rank/inverse, probability, and transformation contracts
and older constructor/equality work stay in the full-library objective.

The full Audit passes 2520 jobs and 59190 dependency checks. Preservation
retains all 6103 starting files and 2507 older non-Audit proof sources.
Thirty-five frozen manifests check 277 module entries. Historical repairs,
stashes, other worktrees, and the optimized interned core remain.
No Haskell file changes. Reuse strict Nix validation, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
each later repair there with failure, reproducer, paths, commit, checks,
and upstream status. This is progress; the full goal remains active.

## Current finite ordinary target domains and shared leaves

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `c47ad331`. Read lean/notes-current-constrained-target-domain.md
for the top-level proof objective, proved contracts, and remaining areas.
Evidence is in lean/restart-evidence/20261016-constrained-target-domain/.
Eight additive modules close the current target-domain prerequisites.
Commits are `d9d86a5e` (actual memo-aware merge and literal worker),
`522a037a` (projection, required paths, and targets), and `7b60eca2`
(shared Force/Leaf and Audit imports).

Actual merge calls retain physical and structural cache certificates.
Each hit identifies its complete captured original. Each miss proves its
actual memo-aware body before it remembers and rereads the current winner.
Finite merge constructs literal success and every larger work/selection
bound at the same output, full physical state, and memo. It has no supplied
success, future body, or result-domain premise.

Actual projection and target folds derive finite ordinary result domain.
Target derives signed path support from its available captured forest.
Its finite endpoint constructs its own actual graph and full receipt.
Native and merge structural certificates survive every actual prefix.
Required paths preserve domain and height at each child position; rows can
be deleted. Guards and equality classes remain unrestricted in the finite
ordinary domain. Mu, references, and explicit unions are outside that domain.

Shared.Stored tracks native results, merge results, and target slots.
Actual Force derives domain from its warm slot or actual target miss.
Actual Leaf derives NodeNarrow relative to INPUT from the native bound for
its second operand. No target-height or equal-path-length premise is needed.
Finite Force/Leaf construct their own complete receipts and preserve all
three tables at the same returned state. Initial readiness, semantic
admission, domain facts, and reached WordRanges remain explicit.

Next compose positional bounds through actual shared edits, Class/Pass,
Scan, local reduction, and parent construction. Then construct a new finite
ordinary outer recursion proof with a certificate tied to each captured
node/edge owner. First derive zero cached Mu depth and the primary scan
fast branch. General refused scans need a separate seeded structural proof.
Read next-class-stage-review.md in the evidence directory.
The old plain Shape is too strong for generated intersected children.
General Mu constraint migration, unequal-length classes, repeated-pass
convergence, current frontend adapters, concrete Haskell runtime transfer,
and full-pipeline composition remain open. The full-library objective also
retains exact size classes, finite execution, counts, ordered ranks, both
inverses, probability, transformations, and older constructor/equality work.

The full Audit passes 2508 jobs and 59107 dependency checks. Preservation
retains all 5965 starting files and 2499 older non-Audit proof sources.
Thirty-four frozen manifests check 265 module entries. Historical repairs,
stashes, other worktrees, and the optimized interned core remain.
No Haskell file changes. Reuse strict Nix validation, 798 examples plus
golden, six-file Fourmolu, and four-package Cabal-gild and metadata checks.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
each later repair there with failure, reproducer, paths, commit, checks,
and upstream status. This checkpoint is progress; the full goal stays active.

## Current constrained finite ordinary native structure

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `d7ce6713`. Read lean/notes-current-constrained-structure.md
and lean/restart-evidence/20261016-constrained-structure/.
Eight additive modules prove finite ordinary native structural results.
Commits are `106e4123` (domain, warm certificates, local code), `5d54241d`
(compiled bodies), `a4506576` (actual traces and exact finish frames), and
`62f30089` (finite completion).

The domain includes Empty and ordinary nodes with all actual row children.
Guards and normalized equality classes have no restriction. Mu, reference,
and explicit union records remain outside it. Pure domain metadata is
unrestricted. Coherent available readback derives original syntax and
empty cached free-name lists.

Execution.node_trace and edge_trace derive domain closure and height
bounded by EACH original operand from their literal completed physical
trace. Strong trace induction proves each smaller body result before its
own finish. Full physical key readback identifies captured owners. The
exact evaluating cell survives to its original finish. Stored tracks
conditional certificates for actual returned cells in both memo families.
Empty seen lists are required. Nonempty seen lists can return recursive
placeholders, even for ordinary inputs. Arbitrary Code with unchecked
finish instructions cannot preserve this certificate.

Finite.finite constructs its own finite checked receipt and retains Idle,
SemanticReady, Stored, result domain, both height bounds, and closedness at
the SAME actual returned state. Initial physical Good, SemanticReady,
Stored, Idle, available domain operands, and reached WordRanges remain
explicit. Original syntax and operand closedness are derived. There is no
future body, successful execution, result law, or final invariant premise.
Cold tables derive Stored; arbitrary warm tables still need admission.

Next compose these structural bounds through actual target edits, shared
edits, class folds, and a generalized local/parent certificate. Warm class
slots and merge results need causal domain certificates. Closedness and
language narrowing do not imply finite ordinary structure. Read
next-class-progress-review.md in the evidence directory. This checkpoint
does not prove general constrained outer completion. Mu constraint
migration, unequal-length classes, and repeated-pass convergence remain
open. The full-library scope retains languages, transformations, exact
size classes, finite execution, counts, ordered ranks and both inverses,
probability, frontends, runtime, and full-pipeline composition. Preserve
all older constructor/equality work and the optimized interned core.

The full Audit passes 2500 jobs and 59028 dependency checks. Preservation
retains all 5837 starting files and 2491 older non-Audit proof sources.
Thirty-three frozen manifests check 257 module entries. Historical repair
records, stashes, and the three other worktrees remain. No Haskell file
changes. Reuse current source validation: strict Nix build, 798 examples
plus golden, six-file Fourmolu, and four-package Cabal-gild and metadata.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
every later repair there with failure, executable reproducer, paths,
commit, checks, and upstream status. Earlier sections are historical
checkpoints. This is progress; the full objective remains active.

## Current finite plain recursion and constructed root execution

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `8f063c09`. Read lean/notes-current-plain-recursion.md
and lean/restart-evidence/20261016-plain-recursion/.
Seven additive modules construct plain recursive execution. Commits are
`39a2925a` (induction interfaces), `99296e30` (exact prefixes), `57d517ce`
(terminals), `c2c3f694` (child loops), `99de70a4` (rows/descendants),
`06d7a970` (strong node induction), and `00abe685` (exact root composition).

PlainNode.finite constructs stable literal node execution, its own graph,
strict Reads, Checks, full Post, output availability, Stored after, and
NodeLaw from initial Context, inherited Ready, available Region input,
Stored, and active order. Strong node-rank induction discharges every
smaller-call callback. Each actual prefix derives the next Context and
Stored. Completed frames restore the original ancestor bound before each
suffix. Warm calls retain their exact captured owners and finish handles.

PlainRoot.constructed_root derives initial Context, Stored, and active
order from covered construction. It returns finite literal execution and
full language equivalence without a worker-success or future-range premise.
prepared_root also derives its actual ordered field History and Receipt.
Construction success and Region remain explicit inputs. Region stops at
Mu and union. Traversed rows use the complete effective own accessor.
Mu cleanup can remove its binder, so no returned-node Region is promised.

Next address general constrained progress outside Region. Read
next-general-review.md in the evidence directory. First prove constrained
finite-ordinary native domain closure and height bounds for each operand,
including structural certificates for actual warm producers. Then compose
class edits and a generalized parent certificate. This is an intermediate
stage; Mu constraint migration remains separate. Nonempty own classes can
change children beyond the plain Shape. Derive actual reached range checks
and an independent progress measure. Do not assume future
execution, future semantic answers, or a finite inventory of future keys.
Unequal-length classes and repeated-pass convergence remain open.
The full-library scope still includes languages, transformations, exact
size classes, finite execution, counts, ordered ranks and both inverses,
probability, frontends, runtime, and full-pipeline composition. Preserve
all older constructor/equality work and the optimized interned core.

The full Audit passes 2492 jobs and 58889 dependency checks. Preservation
retains all 5730 starting files and 2484 older non-Audit proof sources.
Thirty-two frozen manifests check 249 module entries. Historical repair
records, stashes, and the three other worktrees remain. No Haskell file
changes. Reuse current source validation: strict Nix build, 798 examples
plus golden, six-file Fourmolu, and four-package Cabal-gild and metadata.
Root FINDINGS.md keeps the external Haskell repair handoff first. Add each
later repair there with failure, executable reproducer, paths, commit,
checks, and upstream status. Earlier sections are historical checkpoints.
This is progress; the full objective remains active.

## Current plain parent and outer edge-call completion

Source main remains `c0cc8a05`, merged at `896b0a1c`. This checkpoint
starts at published `8906d5e6`. Five additive modules derive complete
plain parent ranges, returned-edge structural support, exact warm-owner
input transport, and finite literal outer EdgeCall execution.
Read lean/notes-current-plain-edge-completion.md and
lean/restart-evidence/20261016-parent-plain/.
Proof commits are `db438c0b` (full ranges), `b7fd0ee5` (returned domain),
`3f817e89` (parent completion), `96a1afee` (owner inputs), and
`6bbf2ee0` (outer edge-call completion).

ParentPlain derives its own stable parent execution, strict Reads, full
Post, and three-way child Shape from initial caller facts and the live
effective-own-empty condition. Shape allows original children, erased
slots, or the singleton Empty sentinel. It preserves child Region and
bounds height; it does not preserve arity. Stored tracks this Shape for
actual returned edge owners through begin, advance, and exact finish.

PartialPlainEdgeCall.finite constructs literal completion from initial
Context, inherited readiness, resident input, Plain, Stored, and the
active-owner bound. It returns its own graph, strict Reads, reached Checks,
full Post, result residency, Stored after, Shape, and EdgeLaw. A ready hit
uses its captured owner. A new evaluation finishes the selected handle
before descendants. No literal success, future body, range plan, or desired
result law is a public input.

Next construct node, rows, descendants, children, and walk completion in
plain Region. Thread actual returned Context and Stored through every
prefix. Read region-next-review.md in the evidence directory and the
node-rank induction outline in the note. The constructed-root exact theorem
still needs literal worker success. General constrained completion,
unequal-length classes, and repeated-pass convergence remain open.
The full-library objective includes languages, transformation contracts,
exact size classes, finite execution, counts, ordered ranks and inverses,
probability, current frontends, runtime, and full-pipeline composition.
Keep all older constructor/equality work and the optimized interned core.

The full Audit passes 2485 jobs and 58868 dependency checks. Preservation
retains all 5648 starting files and 2479 older non-Audit proof sources.
Thirty-one frozen manifests check 242 module entries. Historical repair
records, stashes, and the three other worktrees remain. No Haskell file
changes. Reuse current source validation: strict Nix build, 798 examples
plus golden, six-file Fourmolu, and four-package Cabal-gild and metadata.
Root FINDINGS.md keeps the external Haskell repair handoff first. Record
any later repair there with its failure, executable reproducer, paths,
commit, checks, and upstream status. Earlier sections are historical
checkpoints. This is progress; the full objective remains active.

## Current constructed root entry and active-owner progress

Source main remains `c0cc8a05`, merged at `896b0a1c`. The starting
published checkpoint is `a3b275f3`. Five additive modules derive the root
caller from construction and establish current progress prerequisites.
Initialization is `8443666c`; exact root composition is `083ad542`;
active-owner order is `fc31eae4`; completed active frames are `199965d5`;
and literal empty-own local completion is `6abcd365`.
Read lean/notes-current-constructed-root.md and the evidence in
lean/restart-evidence/20261016-root-entry/.

Covered allocation history and actual fresh original construction derive
all eight initial Context fields and a computed singleton inventory.
Empty inherited allocation uses the retained interner's actual canonical
identity and returned cache. constructed_root supplies the initial facts
to the existing literal successful-worker theorem. prepared_root derives
its own ordered field History and retains the actual preparation Receipt.
The same result has its own graph, strict Reads, reached Checks, full Post,
output support, and exact full-language law. Reached machine checks and
literal worker success remain explicit.

Current node/edge height ranks exclude busy and absent demand below active
owners. Actual begin protects other owners and admits smaller bounds.
Actual finish restores ancestor order. Every completed graph in all eight
families leaves no new evaluating owner. Its reverse frame transports
arbitrary active bounds and excluded handles after completed prefixes.
Separate forward frames retain protected earlier owners.

The current local worker completes at ALL bounds when the complete source
own accessor has empty effective equalities. It returns original or erased
children at the exact allocated prefix state with unchanged fourth/merge
memos. Positive guard extraction is part of that accessor. Empty stored
payload alone is insufficient. No historical execution is transferred.

Next derive current parent returned-height and structural support, then
construct actual outer completion with the active-owner order. Read
next-completion-review.md in the current evidence directory. The plain
Region is an intermediate domain, not the full objective. General
constrained completion, unequal-length classes, and repeated-pass
convergence remain open. Concrete runtime and shared warm initialization,
frontends, Sized, generators, rank/probability, solvers, random sources,
callbacks, codecs, full-pipeline composition, and older constructor/equality
work remain in scope. Preserve the optimized interned core.

The full Audit passes 2480 jobs and 58830 dependency checks. Preservation
retains all 5561 starting files and 2474 older non-Audit proof sources.
Thirty frozen manifests check 237 module entries. Historical repairs,
stashes, and the three other worktrees remain. No Haskell file changes.
Reuse the strict Nix build, 798 examples plus golden, six-file Fourmolu,
and four-package Cabal-gild and metadata checks for source `c0cc8a05`.
Root FINDINGS.md keeps the Haskell repair handoff first. Earlier sections
are historical checkpoints. This is progress; the full goal remains active.

## Current literal outer correctness and root language preservation

Source main remains `c0cc8a05`, merged at `896b0a1c`. The preceding
published checkpoint is `9d70eeff`. Four additive modules connect the
literal outer worker to its own strict source receipt. Supporting proof
commit is `695c6fb3`; the full Actual proof is `9dbafced`.
Read lean/notes-current-outer-actual.md and the current evidence in
lean/restart-evidence/20261016-outer-actual/.

Executable range predicates follow actual successful prefixes and returned
states. They contain only reached machine checks. Check composition covers
all sixteen raw constructors and aligns existential physical states through
finite graph realization and whole-return uniqueness. The parent leaf derives
its exact full caller and existing receipt from the literal parent observation.

All eight Actual endpoints derive the successful worker's SAME graph, strict
Reads, reached Checks, computed next inventory, full Post, output support,
and independent language law. Strong fuel induction threads each derived
prefix Context into the next actual call. No future graph, result law, final
invariant, or body completion callback is a public input.
PartialWorkerActual.root_exact applies the existing semantic root theorem
to that derived trace. Its execution premise is literal worker success,
not a supplied completed graph.

General completion is still open. Context permits evaluating owners, so
Context and reached ranges alone cannot imply success. Next derive public
root initialization and an independent progress domain with active-owner
exclusion. Read root-entry-review.md and progress-domain-review.md in the
current evidence directory. Unequal-length classes and repeated-pass
convergence remain open. Current reducePartially performs one pass.
Concrete runtime, frontend, Sized, generator, rank/probability, solver,
random-source, callback, codec, full-pipeline, and older constructor/equality
obligations remain in scope. Preserve the optimized interned core.

The full Audit passes 2475 jobs and 58753 dependency checks. Preservation
retains all 5484 starting files and 2470 older proof sources. Twenty-nine
frozen manifests check 232 module entries. Historical repairs, stashes, and
the three other worktrees remain. No Haskell file changes. Reuse the strict
Nix build, 798 examples plus golden, six-file Fourmolu, and four-package
Cabal-gild and metadata checks. Root FINDINGS.md keeps Haskell repairs first.
Earlier sections are historical checkpoints. The full objective stays active.

## Current literal parent and mutual outer execution

Source main remains `c0cc8a05`, merged at `896b0a1c`. The preceding
published checkpoint is `ade9584d`. Read lean/notes-current-parent-worker.md.
Seven additive modules implement literal checked parent execution and the
eight mutual outer worker families. Parent proofs are in `155da673`;
the outer definition is in `849d1509`, and completion/stability is in
`7d9d503d`. The current evidence directory is
lean/restart-evidence/20261016-parent-worker/.

Parent Actual constructs stable execution, its same graph, strict Reads,
language Receipt, and full caller Post from legitimate initial facts and
reached ranges. Resident input derives the actual field and child support.
Raw rejection needs no field or child premise. The outer worker retains
the stored winning request, exact finish handle, returned-edge descendants,
ordered rows, indexed child descent, literal Mu reconstruction, and every
failure's complete caller and lower diagnostic.

Completion derives ten sufficient stable bounds from every finite supplied
outer graph. Stability preserves successful output and the entire caller
under larger bounds; arbitrary successful bounds have the same full return.
These results do not prove that every intended call has a finite graph.
Next connect literal outer success to its same graph and strict Reads under
initial Context and reached checks, then apply the existing PartialActual
endpoints. root_exact still assumes a completed strict-read call.
Read outer-actual-next.md in the current evidence directory.

The full objective is implementation correspondence for languages,
transformations, exact size classes, finite execution, counts, ordered ranks
and both inverses, and probability laws. General constrained termination,
unequal-length path classes, repeated-pass convergence, current frontend
adapters, full-pipeline composition, and concrete runtime transfers remain.
Logical Reads do not establish GHC demand, publication, or the noConstraint
CAF. Preserve all older constructor/equality work and the optimized core.

The pinned full Audit passes 2471 jobs and 58623 dependency checks. Only
the permitted foundations and old unused-input warning remain. Preservation
checks retain all 5383 starting files and 2463 older proof sources.
Twenty-eight frozen manifests check 228 module entries. Historical repair
text, stashes, and the three other worktrees remain unchanged.

No Haskell file changes. Reuse the current source's strict Nix build,
798 examples plus golden, six-file Fourmolu, and four-package Cabal-gild
and metadata checks. Root FINDINGS.md keeps Haskell repair details first.
Earlier sections are historical checkpoints. The full goal remains active.

## Current literal local reduction and validated field-pool repair

Audited source main is `c0cc8a05`, merged at `896b0a1c`. The preceding
published checkpoint is `66013b03`. Eight additive modules implement
original-record Scan, required-path success stability, and the literal local
reducer with full caller receipts. Proof commits are `7f9db45e`, `ececc503`,
and `9e3f6174`. Read lean/notes-current-local-worker.md.

RecordScan projects to the frozen path Scan for every outcome, including
failures. It retains original records, order, and repeated occurrences.
Each reached gate/query runs once. Actual Retained graphs supply stable
literal bounds; supplied success derives that same positional receipt.
RequiredWorkerStability preserves successful literal requireAll results and
their complete constructor heaps under larger bounds without physical or
future callback premises.

LocalWorker runs precheck once with its actual returned operations. Early
unchanged and contradiction branches skip Scan and class work. Live Scan
stops before required children on a true emptiness answer. A no-stop return
requires the selected original paths on original children at the Scan heap,
then executes the existing literal class right fold and empty propagation.
Nine stage bounds remain distinct from the fixed conjunction budget.
Every failure retains its complete observation and state, including failed
class local slots. Success stability and whole-return uniqueness identify
the forest, Checked, fourth memo, and merge memo unconditionally.

LocalWorkerActual.finite derives stable literal execution, the same actual
graph, strict Reads, language Receipt, and full caller Post from initial
Context, actual same-cache field load, inherited EqReady, resident children,
and reached range plans. Receipt and Post share the computed inventory.
Final probes come from those same reads. verified handles any supplied
literal success. Unconditional narrowing and guard/inherited conditional
language equivalence remain explicit. No future graph, body law, or final
invariant is a public premise.

PR #64 adds drawn typing fields. PR #65 repair `b9219b9e` now rejects the
recursive field-pool example with `FieldAtomOnDatatype "Next" 0`. The
unchanged historical reproducer confirms that error. Standalone holds
still treats the pool as opaque. Root FINDINGS.md records the repair and
its actual validation first. No additional local Haskell patch is added.
New drawn-field states/errors, validation order, and generator-specific
rank order still need source adapters.

The pinned full Audit passes 2464 jobs and 58403 dependency checks. Only
the permitted foundations and old unused-input warning remain. The strict
Nix build, 798 examples plus golden, six-file Fourmolu, and four-package
Cabal-gild and metadata checks pass. Preservation retains all 5274 starting
files, 2455 older proof sources, the six historical repair entries, stashes,
and three other worktrees. Twenty-seven frozen manifests check 221 module
entries. Evidence is in
lean/restart-evidence/20261016-drawn-fields-local-worker/.

The full objective remains active. Read parent-worker-next.md in that
directory. Next implement literal parent construction, then the eight
mutual outer families. Raw parent rejection precedes field lookup and all
child work. root_exact still assumes a completed strict-read outer call.
General constrained termination, unequal-length path classes, and repeated
pass convergence remain open. Current reducePartially performs one pass.
Logical serial Reads do not prove GHC demand, host table events, lazy
publication, or the noConstraint CAF. All frontend, Sized, rank/probability,
solver, random-source, callback, codec, runtime, full-pipeline, and older
constructor/equality obligations remain. Preserve the optimized interned
core and every proof, counterexample, repair, and draft. No board posts or
deployments. Push verified formalize checkpoints regularly. Earlier sections
record historical checkpoints. This checkpoint is progress, not completion.

## Current literal seeded queries and class scanning

Audited source main is `5399d310`, merged at `82d47236`. The starting
published checkpoint is `e75e8c5c`. Twelve additive modules implement
literal first-seeded queries, current primary and secondary gates, and Scan
with full caller receipts. Proof commits are `8978d180`, `19f90e9c`, and
`2b26e442`. PR #63 adds qualified typing do-notation. No local Haskell
behavior repair occurs. Root FINDINGS.md keeps the external repair registry
first, including the confirmed, unfixed recursive field-pool contract gap.

Read lean/notes-current-scan-worker.md. SeededWorker projects without
mergeAlternatives. Head projection precedes the tail, then checked native
intersection uses the exact tail return. Three stage bounds remain distinct.
Completion derives stable bounds from finite graphs. Success stability and
whole-state uniqueness need no physical premise. Initial selected support
derives the same graph, physical facts, probes, and full caller Post at the
computed inventory. The language law preserves common selected subtrees.

GateWorker runs literal current policies with concrete source predicates.
Strict primary reads use the actual queried node. Scan retains five stage
bounds and a fixed conjunction budget. Primary false selects; secondary true
skips; a true current conjunction answer stops before the suffix. False uses
its exact returned checked state and fourth memo. Failed selected suffixes
retain their selected prefix. Order and repeated classes remain.

ScanCompletion constructs stable literal execution from every finite current
graph. ScanStability identifies the complete Result, Checked, and fourth memo
across successful bounds. ScanWorkerActual.finite derives execution and full
caller facts from initial Context, resident values, proper nontrivial classes,
and reached word bounds. verified derives the same facts for a supplied
literal return. Strict Reads, probes, original values, and stopped-class
exclusion belong to that same return. No future graph, body law, or final
invariant is a public premise. Only a no-stop completion reads the full class
partition. A stopped result retains the selected prefix it reached.

The pinned full Audit passes 2456 jobs and 58268 theorem dependency checks.
Only the permitted foundations and old unused-input warning remain. Current
strict Nix build, 793 examples plus golden, three-file Fourmolu, four-package
Cabal-gild and metadata checks pass. Preservation checks retain all 5135
starting files, 2443 older proof sources, six repair/counterexample entries,
stashes, and three other worktree records. Twenty-six frozen manifests check
213 module entries. Evidence is in
lean/restart-evidence/20261016-typing-do-seeded-worker/.

The full library objective remains active. Read local-worker-next.md in that
directory. Next compose literal local precheck/reduction, required children,
and class passes, then parent construction and the mutual outer worker.
root_exact still assumes a completed strict-read outer call. General
constrained termination, unequal-length path classes, and repeated-pass
convergence remain open. Current reducePartially performs one pass. Logical
global reads do not prove host demand, table events, lazy publication, or the
noConstraint CAF. All frontend, Sized, generator, rank, probability, solver,
callback, codec, concrete-runtime, and older constructor/equality obligations
remain. Preserve the optimized interned core and every proof, counterexample,
repair, and draft. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress, not goal completion.

## Current generator node views and source refresh

Publication readback at 13:14 CEST found remote main `5399d310` (PR #63,
qualified typing do-notation). It is fetched but not merged or validated.
The audited source below remains `999c04a5`; formalize checkpoint `27a4722c`
is published. Inspect and refresh that five-file frontend delta before the
next implementation. Read lean/restart-evidence/20261016-typing-do-pending.md.


Source main is `999c04a5`, merged at `9aaffc95`. The preceding published
checkpoint is `b931bcc6`. PR #60 adds field-specific atoms; PR #61 writes
typing rules through node views; PR #62 rejects negative typing bounds.
Root FINDINGS.md keeps the external Haskell repair registry first and records
`443e3458` there. No local Haskell behavior repair is added by this refresh.

Read lean/notes-frontend-node-view-refresh.md. All 2443 older non-Audit proof
sources and Audit retain their bytes. The pinned full Audit passes 2444 jobs
and 58082 dependency checks. This preserves component proofs; it does not
prove the new node-view, field-pool, typing-validation, or codec adapters.
Current strict Nix build, suites, format, metadata, source audits, and
preservation evidence are in
lean/restart-evidence/20261016-frontend-node-view-refresh/.

The full objective remains correspondence between the specified constrained
languages and generators and the current Haskell library. Exact size classes,
finite execution, counts, ordered ranks and both inverses, probability laws,
and transformation semantics remain separate contracts. No whole-library
theorem is complete. root_exact still assumes a completed strict-read outer
call. Serial graphs do not prove concrete host demand or memo publication.

Next implement the literal first-seeded checked query and Scan. Read
scan-worker-next.md in the preceding conjunction evidence directory; its
next target remains current. Then compose local reduction, required children,
parent construction, and the mutual outer worker. General constrained
termination, unequal-length path classes, and repeated-pass convergence remain
open. Current reducePartially performs one pass. Preserve all frontend,
Sized, generator, probability, host-runtime, and older constructor/equality
obligations, the optimized interned core, and all proofs, counterexamples,
repairs, and drafts. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress; keep the full goal active.

## Current literal conjunction execution and full caller receipts

Source main remains `ccebf0f7`. The preceding published checkpoint is
`ebf92715`. Ten additive modules implement current serial conjunction rows,
worklist, decision, fourth-memo calls, and the full checked caller lift.
Proof commits are `d9e77a20`, `5600e0da`, and `34b6519f`.
No Haskell implementation or test changes occur. Root FINDINGS.md keeps the
external Haskell fix registry first. Record every later repair there with
failure, reproducer, files, commit, checks, and upstream status.

Read lean/notes-current-conjunction-worker.md. The full objective remains
correspondence between the specified constrained languages and generators
and the current Haskell library. Exact size classes, finite execution, counts,
ordered ranks and both inverses, probability laws, and each transformation's
semantics remain separate contracts. No whole-library theorem is complete.

RowsWorker executes operand exposures, row-major projections, equality folds,
canonical child columns, and class requirements. Two bounds control projection
and reads. Contradiction retains equality allocations and skips requirements.
Errors, missing equality fields, pending, unresolved, and exhaustion remain
distinct at their actual returned physical states. Completion derives stable
bounds from finite graphs. Stability proves unconditional success preservation
and whole-state uniqueness. Actual reconstructs successful row graphs without
a physical premise; matching tuples derive arities without a new worker check.
Legitimate initial facts derive finite execution, effects, rows, and probes.

ConjunctionWorker.explore implements the actual dynamic worklist. Only
admission decreases the algorithmic budget. Its definition terminates by
budget and pending length; it adds no recursion fuel. Rows precede insertion,
and generated requirements precede the pending suffix. Failure retains the
physical state and local table/pending context. decision checks open input,
then executes actual exploration, Boolean grow, and answer. call looks up the
fourth memo before the open guard and inserts only completed misses.

Completion derives the same Run/Decision/Call from literal success and stable
bounds from finite graphs. Initial physical Ready and query availability
construct finite calls. Stability preserves exact answers, tables, physical
states, and saved memos under larger lower-stage bounds with budget fixed.
AllocatedConjunctionWorker retains the full checked state, native cells, and
domain cache. Failures retain the initial fourth memo. Warm hits retain the
identical checked state and ignore both bounds.

AllocatedConjunctionWorkerActual.finite constructs stable literal execution
and the full caller Post from initial Context and query residency. Both outer
result families, warm merge table, and input inventory remain. The returned
fourth memo, probe heap, and global receipts remain valid. verified derives
the same endpoint facts for a supplied literal success. True excludes every
accepted finite term. False does not prove nonemptiness; valid open answers
are false. No future body result or final invariant is a public premise.

The row graph completes all operand exposures. Haskell can skip operand reads
when an earlier tuple prefix is empty. These serial graphs do not establish
that demand schedule, host global-table event replay, lazy publication, or
the noConstraint CAF. Global Reads remain logical evidence at the aligned
return. root_exact still assumes a completed source-aligned outer call.

Pinned Lean 4.34.1 passes the complete Audit: 2444 jobs and 58082 theorem
dependency checks. Only the permitted three foundations and old unused-input
warning remain. Raw logs, public probes, integration kernels, independent
reviews, frozen sources, and preservation checks are in
lean/restart-evidence/20261016-current-conjunction-worker/.
All Haskell files remain unchanged. Reuse the strict Nix build, 788 examples
plus golden, 15-file Fourmolu, and four-package Cabal-gild and metadata checks.

Next implement the literal first-seeded checked query and current Scan, then
local reduction, parent construction, and the mutual outer worker. Read
scan-worker-next.md in the evidence directory. General constrained outer
termination, unequal-length path classes, and repeated-pass convergence remain
open. Current reducePartially performs one pass. All frontend and generator
adapters, separate Sized and probability contracts, concrete host execution,
containers, identities, concurrency, machine bounds, solver IO, random draws,
callbacks, codecs, full pipeline composition, and older constructor/equality
work remain active. Preserve the optimized interned core and all local proofs,
counterexamples, repairs, and drafts. No board posts or deployments. Push
verified formalize checkpoints regularly. This checkpoint is progress.

## Current literal checked edits and class passes

Source main remains `ccebf0f7`. The preceding published checkpoint is
`67f2b5d0`. Nine additive modules implement current structural edits and
compiled class passes. Proof commits are `87ad619b`, `2cbebf92`, `2f1af1cf`,
and `ca2fe823`. No Haskell implementation or test changes occur.
Root FINDINGS.md keeps the external Haskell fix registry first. Record each
later repair there with failure, reproducer, files, commit, checks, and
upstream status.

Read lean/notes-current-edit-worker.md for the full objective and proof map.
The goal is correspondence between the specified constrained tree languages
and generators and the current Haskell library. Exact size classes, finite
execution, counts, rank inverses, probability laws, and each transformation's
semantics remain distinct contracts. There is no completed whole-library
correspondence theorem.

SharedEditWorker interprets current EditNode, Children, Rows, and List with
six separate stage bounds. Head exposure retains pending, unresolved, and
exhausted outcomes. A failed prefix retains the complete reached checked
state, local slots, merge memo, and diagnostic. Unselected children retain
their values. Raw same-arity reconstruction retains the original full guard.
It does not allocate a new equality field for the raw edge rebuild.

Completion constructs stable sufficient bounds from finite current graphs.
Target and edit success stability is unconditional. Whole-state uniqueness
aligns any supplied successful return with the graph constructed from initial
selected support. Actual derives the same graph, Reads, physical receipt,
probe heap, and computed inventory. list_language derives narrowing and
preservation of class-satisfying selected terms. Unrelated open siblings
need not satisfy selected path closure.

ClassWorker runs compiled edits with empty class-local slots over the full
supplied checked state and warm merge table. The right fold executes the
tail first; the head captures that tail's actual forest, state, and merge.
Final propagation follows only a completed fold. Failures retain all reached
slots. Class completion derives stable six-stage bounds. Stability proves
unconditional success monotonicity and exact forest/Checked/memo uniqueness.

ClassWorkerActual.caller_finite constructs stable literal pass execution and
the full caller Post at the computed next inventory from legitimate initial
Context, resident values, coherent nontrivial records, selected domains, and
actual-prefix ranges. Both outer result families and the fourth memo remain
valid. Supplied success receives the same endpoint facts. Language narrows;
membership agrees with the input for forests satisfying every class. No
future body law or completed pass is a premise of caller_finite.

The outer root_exact theorem remains conditional on a completed strict-read
recursive call and its legitimate initial facts. Global-query read receipts
remain logical evidence. These workers do not execute concrete host global
tables or prove GHC forcing, lazy publication, or the noConstraint CAF.

Pinned Lean 4.34.1 passes the full Audit: 2434 jobs and 57891 theorem dependency
checks. Only the permitted three foundations and old unused-input warning
remain. Public probes, integration kernels, independent reviews, frozen
sources, and preservation evidence are in
lean/restart-evidence/20261016-current-edit-worker/.
All Haskell package sources remain unchanged. Reuse the strict Nix build,
788 examples plus golden, 15-file Fourmolu, and four-package Cabal-gild and
metadata checks from the preceding source refresh.

Next implement dynamic conjunction rows/worklists, its decision and fourth
memo, Scan, local reduction, parent construction, and the mutual outer worker.
Read conjunction-worker-next.md in the evidence directory. General constrained
outer termination, unequal-length path classes, and repeated-pass convergence
remain open. The public reducePartially performs one pass. Concrete host
runtime, containers, identities, concurrency, machine bounds, solvers,
random draws, callbacks, codecs, frontend and generator adapters, separate
Sized contracts, and older constructor/equality work remain active. Preserve
the optimized interned core and all local proofs, counterexamples, repairs,
and drafts. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress toward the full objective.

## Current literal checked targets and shared leaves

Source main remains `ccebf0f7`. The preceding published checkpoint is
`740c6e5c`. Proof commits are `817e4459`, `0d636786`, and `2a8afe4d`.
Eight additive modules implement current allocated Target,
shared Force, and checked Leaf execution. No Haskell implementation or test
changes occur. Root FINDINGS.md keeps the external Haskell fix registry first.
Record each later repair there with failure, reproducer, files, commit,
validation, and upstream status.

Read lean/notes-current-target-worker.md. TargetWorker retains the complete
NativeDemand.State and allocated merge memo. Projection precedes merge.
The source seed executes at the fold base. Each head precedes the tail;
checked intersection uses that tail's returned state. Five stage bounds
remain separate. Failed prefixes retain their exact observations and full
states and skip continuations. Empty targets return the identical state.

TargetWorkerNative derives physical Step at a supplied native done from
initial Good, idle cells, closed resident operands, and reached word ranges.
It independently constructs the physical trace and aligns the whole return
by success uniqueness. Arbitrary native success does not imply those checks.
TargetWorkerSound derives actual fold prefixes from legitimate initial
Ready/At, available captured values, selected path domains, warm merge laws,
actual-prefix ranges, and initial global validity. No future body law is
a public premise.

TargetWorkerCompletion derives stable sufficient bounds from every finite
current graph. It also proves unconditional successful execution stability
and whole-return uniqueness under different bounds. TargetWorkerActual
derives each supplied success's own checked receipt and probes. Its finite
endpoint constructs stable literal execution from initial selected support.
caller and caller_finite retain both outer result families and the fourth
memo in a full Post at the computed next inventory.

SharedTargetWorker executes literal ready hits, target misses, and checked
leaf requests. A hit ignores every bound and retains the complete state.
A miss stores only a completed target. Failure retains its returned checked
state and merge table without installing a slot. Completion and Actual
derive stable execution, actual graphs and reads, full receipts, probes,
narrowing, and preservation of class-satisfying selected subterms.
Target language is inclusion, not exact equality. Global query receipts
remain logical evidence; these workers do not execute concrete host tables.

Pinned Lean 4.34.1 passes the full Audit: 2425 jobs and 57723 theorem dependency
checks. Only the permitted three foundations and old unused-input warning
remain. Public probes, integration kernels, independent reviews, frozen
sources, and preservation evidence are in
lean/restart-evidence/20261016-current-target-worker/.
All Haskell package sources remain unchanged. Reuse the strict Nix build,
788 examples plus golden, 15-file Fourmolu, and four-package Cabal-gild and
metadata checks from the preceding refresh.

Next implement literal checked EditNode/Children/Rows/List, compiled class
editing, and the class right fold with final empty propagation. Preserve
actual Head exposure, same-arity raw rebuilding, full guards, selected path
positions, and unrelated open siblings. Each class resets only local slots.
Read checked-edits-next.md in the evidence directory. Then implement dynamic
conjunction, Scan, local reduction, parent construction, and the outer worker.

General constrained outer termination, unequal-length path classes, and
repeated-pass convergence remain open. Current reducePartially performs
one pass. Host forcing, publication, noConstraint CAF, containers, identities,
concurrency, machine bounds, solver IO, random draws, callbacks, codecs,
all frontend and generator adapters, separate Sized contracts, and older
constructor/equality work remain active. Preserve the optimized interned
core and every local proof, counterexample, repair, and draft. No board posts
or deployments. Push verified formalize checkpoints regularly. This
checkpoint is progress toward the full-library objective.

## Current source refresh and literal merge execution

Source main is `ccebf0f7`, merged into formalize at `44ba7bf1`. The previous
published checkpoint is `10b58c54`. Proof commits are `03c50a7d`, `cb2f4061`,
and `03b48a40`. This increment adds five Lean modules.
It changes no local Haskell behavior or test. Root FINDINGS.md retains the
external Haskell repair registry first. Record every later repair there with
its failure, reproducer, files, commit, checks, and upstream status.

Read lean/notes-current-merge-worker.md for the current top-level proof map.
The full objective is correspondence between the specified constrained tree
languages and generators and the current Haskell library. Exact size classes,
finite execution, counts, size order, both rank inverses, probability laws,
and each transformation's stated semantics remain distinct contracts.
There is no completed whole-library correspondence theorem.

The existing Sized Exact record proves finite modeled classes, distinct
accepted terms, exact counts, signed errors, both inverses, and ordered
prefixes on validated original row maps under the stated guard contracts.
The completed current outer root_exact theorem proves independent language
equality and the full returned physical/memo invariant. It still requires a
completed strict-read call, legitimate initial Context, allocated empty
inherited readiness, input availability, and reached checks.

SourceCurrentAllocatedMergeWorker now interprets the current allocated Code.
It retains the exact heap, equality operations, and merge memo on success
and failure. Top rows allocate emptyField at the reached state. Work and
selection fuel remain separate. A positive-work ready hit needs no body fuel.
Sound derives the same actual Run or Call. Completion derives stable bounds
from finite graphs and proves both graph equivalences and success stability.

WorkerActual.finite constructs a finite literal merge return from legitimate
warm Context and input availability. It derives stable execution and the full
caller Post at the same output, heap, operations, and memo. Both outer result
families, native tables/domain cache, and fourth memo remain. The language
law is inclusion: merge is an over-approximation. Logical global-query read
receipts are constructed; the worker does not execute concrete host tables.

SourceCurrentCurriedDefaulting models current narrowHeads with ?any priority.
The historical filter agrees only when ?any is absent. The actual two-row
counterexample shows an adapter boundary, not a Haskell bug. The upstream
refresh adds root typing inputs, Binders, type domains, and deriveLTAOn.
Broader row/closure, GHC pruning, LTA contract/codec, and generator rank
adapters remain open. No cfta core or Sized source changes upstream.

The full pinned Audit passes 2417 jobs and 57607 theorem dependency checks.
Only the three permitted foundations and the old unused-input warning remain.
The strict Nix all-component build passes. All six current suites pass:
788 examples plus golden. All 15 changed Haskell files pass Fourmolu; all
four active packages pass Cabal-gild and metadata checks. The first GMP
linker failure is an environment PATH issue, corrected without source edits.
Raw logs, public probes, integration kernels, independent reviews, frozen
sources, and preservation checks are in
lean/restart-evidence/20261016-typing-refresh-merge-worker/.

Next implement literal checked Target and shared Force/Leaf, followed by
edits, Class/Pass, conjunction, Scan, local reduction, parent, and the outer
two-family worker. Read target-current-next.md in the evidence directory.
Their strongest current endpoints remain relations. Retain exact failed
states and strict source reads. Do not supply a future body success oracle.

General constrained outer termination, unequal-length path classes, and
repeated-pass convergence remain open. Current reducePartially is one pass.
Host forcing, lazy publication, noConstraint CAF, concrete containers,
identity lifetime, concurrency, machine bounds, solvers, random draws,
callbacks, codecs, broader frontends, separate Sized contracts, and all older
constructor/equality targets remain active. Preserve the optimized interned
core and all local proofs, counterexamples, repairs, and drafts. Push verified
formalize checkpoints regularly. No board posts or deployments. This is
progress toward the full objective.

## Current mutual recursive reduction correctness

Source main remains `8f85ddb6`. The preceding published checkpoint is
`7fedbcd7`. Proof commits are `3192fe1b` and `3a86f40e`. Six additive modules
prove the full mutual physical and language invariant for completed current
recursive calls. No Haskell implementation or test changes occur. The
external Haskell fix registry remains first in root FINDINGS.md. Record each
later repair there with its failure case, files, commit, checks, and
upstream status.

PartialInvariant.Context retains checked Ready, inventory At, warm caller
Sound, merge Stored and CacheCovers, fourth Correct, actual global Valid,
and explicit ProbeHeap. Input requests retain ready inherited values and
resident inputs. Post describes the same actual returned caller and globals.
Its inventory can change. No warm table is reset.

PartialChecks stores physical graph indices as data. Direct and Reach
follow actual completed constructors. Checks contains only reached live
edge-body Scan word plans. It has no result law, future invariant, child
completion callback, or general completion claim. It covers the permitted
completed graph decompositions, not a chosen host forcing trace.

StepEffects derives the literal inherited prefix, indexed descent, raw
same-arity rebuild, and ordered-identity modifyNode contexts and probes.
ForestLanguage composes ordered row unions and returned-edge descendants.
CallSteps derives first-owner input facts, retains its exact evaluating
cell through the actual body frame, finishes its derived result, and
transports the law by the physical key. Resident Mu reconstruction derives
its literal same-heap cleanup from the explicit probe invariant.

PartialActual follows all eight strict source-read recursors. NodeCall,
NodeBody, EdgeCall, EdgeBody, Rows, Descendants, Children, and Walk derive
their own availability or residency, independent language law, and full
Post at their supplied result, state, and global endpoints. The smaller
actual node induction result supplies each indexed child law. Ordinary
rows use the RETURNED parent edge's child list and full guard. No recursive
body law is a public premise.

root_exact proves exact independent language preservation for a completed
call with an allocated empty inherited payload. It retains the same actual
physical and memo Post. Initial Context, input and inherited readiness,
strict Reads, and reached checks remain explicit. This does not prove the
Haskell noConstraint CAF or universal outer completion.

Pinned Lean 4.34.1 passes the complete Audit: 2412 jobs and 57527 theorem
dependency checks. Only the standard three foundations and the old
unused-input warning remain. Public probes, integration kernels, independent
reviews, source hashes, and raw logs are retained in
lean/restart-evidence/20261016-current-mutual-caller/.
All 4571 starting files remain. All 2405 older non-Audit proof sources retain
their bytes. Twenty-one frozen manifests, stashes, other worktree records,
and the first Haskell registry remain. Earlier unavailable external drafts
are not claimed recovered or reverified. Reuse unchanged-source strict Nix
build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild.

Read lean/notes-current-mutual-caller.md and bounded-current-next.md in the
evidence directory. Next add the literal bounded outer executable worker,
with complete reached states, body-free hits, errors, missing fields,
unexpected Rec, busy or absent cells, and exhausted outer fuel. The local
checked budget is separate from outer recursion fuel. Implement the current lower Scan, class-pass, local, and parent workers
before outer composition; their present endpoints are relations. Connect
success to the strict graph and prove sufficient stable bounds only on a
justified domain. Do not substitute a body completion oracle.

General constrained outer termination, unequal-length path classes, and
repeated-pass convergence remain open. Serial graphs do not prove GHC
forcing, lazy IntMap/list demand, or pending publication. The full-library
goal, all frontend and recursive-generator adapters, separate Sized
contracts, noConstraint CAF, concrete containers, concurrency, identity
lifetime, machine limits, solver IO, random draws, callbacks, codecs, and
older constructor and equality work remain active. Preserve the optimized
interned core. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress.


## Current source-aligned reads and caller prerequisites

Source main remains `8f85ddb6`. The preceding published checkpoint is
`abd6a170`. Proof commits are `6f300927`, `5b391983`, `2e3f0fd4`, and
`4b2995ee`. This checkpoint adds 35 Lean modules. No Haskell implementation
or test file changes. The external Haskell fix registry remains first in
root FINDINGS.md. Record every later repair there with its failure case,
affected files, commit, checks, and upstream status.

The old primary closed-endpoint read relation can query a different node
from its pure trace input. A kernel counterexample starts from actual closed
construction, a resident gate input, and valid three-table memos. The old
receipt queries an uninstalled node with identity 999 and returns invalid
tables. This is a Lean receipt defect, not a demonstrated Haskell defect.
The strict primary relation ties the query to the actual source node.
Completed execution constructs it. Erasure retains the old receipt;
the old relation alone does not supply the refinement.

Required, Projection, Gate, Seeded, Query, Conjunction, and Scan validity
now follow their supplied actual reads and literal returned tables.
Uniqueness is used only at a recorded fixed exposure budget. Equal returned
heaps do not identify different schedules. Strict Scan, local, and parent
schedules are constructed from legitimate initial invariants and reached
range checks. The new actual receipt endpoints describe the supplied result,
state, and globals. Rejected parents need no live child or range premise.

Thirteen Probe modules retain the explicit filtered-probe heap through
current gates, queries, native merges, Scan, required paths, target folds,
structural edits, class passes, local reduction, and parent construction.
The strict supplied-parent endpoint proves probes at that same actual return.
Independent kernels combine its full receipt and literal resident Mu cleanup
on the same heap. Initial ProbeHeap remains explicit; original construction
derives it. Ready, Effects, and Keeps alone do not imply it.

Current caller frames retain both result families' protected evaluating and
returned cells through all eight mutual graphs. Indexed descent derives its
literal payload. Walk and Children language lemmas compose smaller actual
call laws at their exact source offsets. These are induction steps.
Strict outer reads retain the source-aligned parent schedule and erase to
the old graph. Actual reduced-edge calls derive their full receipt, probes,
owner body law, exact finish cell, and candidate law through physical keys.
No future result law or final validity is supplied.

Pinned Lean 4.34.1 passes the complete Audit: 2406 jobs and 57445 theorem
dependency checks. Only the standard three foundations and the existing
unused-input warning remain. Public probes, integration kernels, independent
reviews, source hashes, and raw logs are retained in
lean/restart-evidence/20261016-current-caller-invariants/.
All 4276 starting files remain. All 2370 older non-Audit proof sources retain
their bytes. Twenty frozen manifests, stashes, other worktree records, and
the first Haskell registry remain. Earlier unavailable external drafts are
not claimed recovered or reverified. Reuse unchanged-source strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-caller-invariants.md and mutual-current-next.md in
the evidence directory. Next prove the full mutual physical and language
invariant for current NodeCall, NodeBody, Rows, Descendants, Children, and Walk.
Use the new strict reads, actual smaller calls, protected frames, actual edge
receipts, probes, inherited descent, raw rebuilding, and modifyNode.
Do not supply a callback that assumes the desired recursive body law.

General constrained outer completion, unequal-length path classes, and the
literal bounded executable worker remain open. Serial graphs do not prove
GHC forcing, lazy IntMap/list demand, or pending publication. The full-library
goal, all frontend and recursive-generator adapters, separate Sized contracts,
noConstraint CAF, concrete containers, concurrency, identity lifetime, machine
limits, solver IO, random draws, callbacks, codecs, and older constructor and
equality work remain active. Preserve the optimized interned core.
No board posts or deployments. Push verified formalize checkpoints regularly.
This checkpoint is progress.

## Primary memo read source-record boundary

The historical `EndpointMemoGateTrace.NodeReads.endpoint_closed` receipt
does not tie the queried node's entry and edges to the pure gate input.
It can therefore record a completed query for an unrelated physical record.
`SourceCurrentPrimaryReadsCounterexample` constructs a resident closed root
with an actual recursive child. Its heap is gate-ready and its initial
three-table bundle is valid. The old receipt instead queries a nonresident
node with identity 999. The returned descendant table stores that node.
Its final bundle is invalid. The pinned direct and canonical Lean checks
verify this counterexample. The full Audit includes it: 2406 build jobs
and 57445 theorem dependency checks pass with only standard foundations.

This is a Lean receipt-model defect. It does not establish a Haskell defect.
No Haskell implementation or test change is required by this finding.
Historical constructive gate theorems remain available in their original
scope. Their existential returned bundle does not validate every supplied
receipt accepted by the old read relation.

`SourceCurrentAllocatedPrimaryReads` adds the exact source-node annotation
to the closed endpoint. Its completed gate adapter constructs these stricter
reads from the actual source execution and initial invariants. The direct
gate validity proof follows these supplied strict reads. It has no final
validity premise. Current Scan and parent adapters must carry this source
refinement. The historical outer read graph alone does not supply it.
All older proof sources remain unchanged.

## Current inherited descent and reduced-edge result memos

Source main remains `8f85ddb6`. The preceding published checkpoint is
`a15d6143`. Proof commits are `e5714c8d`, `0af22f98`, `e37b311b`, and
`1226b1f3`. No Haskell implementation or test changes occur. The external
Haskell fix registry remains first in root FINDINGS.md. Record each later
fix there with its failure case, affected files, commit, checks, and
upstream status.

Eight additive modules retain the CURRENT inherited prefix, raw rebuilding,
both caller result families, ordered recursive graph, actual read schedule,
Mu reconstruction, warm result laws, and reduced-edge wrapper. Inherited
combination runs once on the RETURNED edge, inherited FIRST. Contradiction
short circuits before its own accessor. Each child receives its actual
indexed allocated descent. Raw same-arity setChildren and literal modifyNode
retain their distinct source operations. Warm tables are not reset.

Both result families retain their complete first published requests. A
suspended hit starts its stored owner. A completed hit reuses that owner's
proved law through the actual physical key and keeps the whole caller state.
Equal key transport derives inherited satisfaction equivalence; it does not
assume identical metadata or a candidate result law. Actual physical effects
retain all warm cell facts. Empty families derive Sound without answers.

The current reduced-edge wrapper is composed with the actual ParentEdge
finite theorem. It derives the owner body law, retains its exact running
cell, finishes that cell, and derives the candidate's law. Fresh keys construct
their own prefix. Ready hits need no parent range plan. finite_or_busy covers
all valid starts: actual busy observation or an actual completed call and
full physical, language, inventory, merge, fourth, and global receipt.
Validity excludes absence. No busy cell becomes a result. Ranges inspect
only reached evaluated owners and actual field loads; no future successful
body, readiness oracle, or result-language law is an input.

Mu reconstruction uses an explicit filtered-probe heap derived by original
construction. Actual constructor work, optional binders, and checked native
execution retain it. A resident binder then rebuilds to its smart cleanup
with unchanged heap and exact independent meaning. Current Ready does not
imply that probe heap. Its transport through all high-level current graphs
remains open. The raw outer graph and Reads alone prove neither its physical
invariants nor its full recursive language law.

The pinned full Audit passes 2371 jobs and 57099 theorem dependency checks.
Only standard foundations and the old unused-input warning remain. Public
probes, external integration kernels, and independent reviews are retained
in lean/restart-evidence/20261016-current-inherited/. All 4146 starting files
remain. All 2362 older non-Audit proof sources retain their bytes. Nineteen
frozen manifests, stashes, other worktree records, and the first Haskell fix
registry remain. Earlier unavailable external drafts are not claimed recovered
or reverified. Reuse unchanged-source strict Nix all-component build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-inherited-caller.md and outer-current-next.md in the
evidence directory. Next prove protected running-cell frames and the mutual
physical/language invariant for the CURRENT recursive calls, descendants,
ordered rows, and modifyNode. Derive child laws from smaller actual calls.
Do not assume the desired body law through a callback. Preserve the explicit
probe heap through current operations before using the Mu receipt globally.
General constrained outer completion, unequal-length path classes, and the
literal bounded executable worker remain open. Serial graphs do not prove
GHC forcing, lazy IntMap/list demand, or pending publication.

The full-library goal, broader frontend and recursive-generator adapters,
all separate Sized contracts, noConstraint CAF, concrete containers,
concurrency, identity lifetime, machine capacity, solver IO, random draws,
callbacks, codecs, and older constructor and equality work stay active.
Preserve the optimized interned core. No board posts or deployments. Push
verified formalize checkpoints regularly. This checkpoint is progress.

## Current warm local reduction and checked parent construction

Source main remains `8f85ddb6`. The preceding published checkpoint is
`af0b0fa9`. Proof commits are `cb5232fe`, `8f38d731`, `9432d30d`, and
`c2cfe5c8`. No Haskell implementation or test changes occur. The external
Haskell fix registry remains first in root FINDINGS.md. Record each later
fix there with its failure case, affected files, commit, checks, and
upstream status.

Five additive modules compose the CURRENT warm local child reduction and
its checked parent constructor. The actual allocated precheck retains its
literal returned equality operations and complete native state. It derives
all three source branches and the live original records. The unchanged
child branch can still retain accessor allocation; it is not a whole-state
no-op theorem. No initial closed forest or cold cache reset is required.

One actual current Scan selects erasure or the literal required worker and
checked class right fold. Exact selected records, global read receipts,
fourth answers, merge entries, and returned inventories remain connected.
Ranges inspect only reached raw precheck, Scan, required, and class prefixes.
No future completion, readiness, admission oracle, or result-language law
is an input. Initial legitimate warm invariants and actual machine checks
remain explicit.

The complete local receipt narrows the input forest. It gives equal membership
for terms satisfying the original full guard and inherited equalities. The
parent checks raw contradiction BEFORE local child reduction. Rejection needs
no field load, inherited readiness, child availability, or local ranges.
Its sentinel derives Top allocation at the actual current cache. The live
branch calls the actual checked mkEdge at the literal local return. Both
constructor acceptance and rejection have exact independent PCS edge meaning.
The parent language narrows the original raw edge and is equal under inherited
satisfaction. No unconditional output-class-satisfaction law is claimed.

Local child count is preserved. A rejected constructor can instead return
one empty child and Top; final-edge arity is not unconditionally preserved.
The next inherited stage must read THAT returned guard and child list.
Its inherited-FIRST combination differs from the local precheck's own-FIRST
key. Final same-arity setChildren remains a separate raw interning operation.

The pinned full Audit passes 2363 jobs and 56924 theorem dependency checks.
Only standard foundations and the old unused-input warning occur. Public
probes, independent reviews, and a two-edge warm integration pass. The latter
derives source field loads and child availability, then constructs the second
edge at the first edge's actual returned state and all returned memo tables.
Evidence is in lean/restart-evidence/20261016-current-local-reduction/.
All 4060 starting files remain. All 2357 older non-Audit proof sources retain
identical bytes. Eighteen frozen manifests, stashes, other worktree records,
and the first Haskell registry remain. Earlier unavailable external drafts
are not claimed recovered or reverified. Reuse unchanged-source strict Nix
build, 777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-local-reduction.md and inherited-current-next.md in
the evidence directory. Next port the returned-edge inherited prefix, its
indexed descents and CURRENT recursive requests, then ordered rows and the
literal modifyNode reconstruction. Combine the parent payload once. Do not
map an old helper that repeats combination at every child. Keep the source
contradiction short circuit before an otherwise demanded own accessor.
General constrained outer completion and its actual outer/edge result caches
remain open. Completed serial graphs do not establish the literal bounded
worker, GHC forcing, IntMap demand order, or pending cache publication.
The pure selection noConstraint CAF adapter remains explicit.

The full library goal, broader frontend and recursive-generator adapters,
all separate Sized contracts, concrete containers, concurrency, identity
lifetime, machine capacity, solver IO, random draws, callbacks, and codecs
stay active. Preserve the optimized interned core and every older constructor
and equality proof. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress.

## Current checked structural edits and full class pass

Source main remains `8f85ddb6`. The preceding published checkpoint is
`b992e324`. Proof commits are `63310da4`, `251fa392`, `1e54e3cb`,
`9cdb80c5`, and `7f00cf8e`. No Haskell implementation or test changes occur.
The external Haskell fix registry remains first in root FINDINGS.md. Add each
later fix there with its failure case, files, commit, checks, and upstream status.

Nine additive modules connect CURRENT checked leaf narrowing to structural
edits, compiled classes, the complete right fold, and final empty propagation.
Finite endpoints construct actual read annotations from initial invariants
and reached raw-prefix ranges. No future successful edit, readiness, model,
admission oracle, or result-language law is supplied. Each returned inventory,
checked state, and global bundle enters the next selected call. Positional
child edits preserve arity. Raw same-arity setChildren retains the original
complete guard and operation state. Other original siblings can remain open.

Each class captures its actual tail-returned forest. Only its local slots
start empty. Both native tables, domain cache, equality operations, warm merge
entries, and global receipts remain. Full-pass language narrows the input and
has identical membership for terms satisfying all selected classes. Final
literal empty propagation preserves exact forest language and the full state.
No unconditional output-class-satisfaction claim follows.

The current Required receipt derives every selected class domain. Its actual
return feeds the new finite pass. Merge Stored grows from the pre-required
heap. Class satisfaction derives the required paths. Therefore class-satisfying
terms have identical membership before required preparation and after the full
pass. Composed effects retain original values and fourth-memo correctness.
Initial legitimate warm coverage, selected-record coherence, actual-prefix
machine checks, and global validity at the actual required return remain inputs.
The earlier RequiredGlobalMemos endpoint derives that global validity.

The pinned full Audit passes 2358 jobs and 56817 theorem dependency checks.
Only standard foundations and the old unused-input warning occur. Public
probes, integration kernels, and independent reviews pass. Evidence and
frozen sources are in lean/restart-evidence/20261016-checked-edits/.
All 3948 starting files remain. All 2348 older non-Audit proof sources retain
identical bytes. Seventeen frozen manifests, stashes, other worktree records,
and the Haskell registry remain. Earlier unavailable external drafts are not
claimed recovered or reverified. Reuse unchanged-source strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-checked-class-pass.md and checked-outer-entry-next.md
in the evidence directory. Next compose actual allocated precheck and Scan
with Required and this pass. Parent reconstruction uses mkEdge, whose early
contradiction test can skip the child thunk. FieldAvailable alone does not
prove constructor acceptance. Later inherited descent reads the RETURNED edge
and combines inherited constraints first. Final setChildren is a separate raw
same-arity step. General constrained outer completion and its literal worker
transfer remain open. Completed sequential graphs do not establish GHC or
IntMap demand order. Keep the pure selection noConstraint CAF adapter explicit.

The full library goal, broader frontend and recursive-generator adapters,
all separate Sized contracts, concrete containers, publication, concurrency,
identity lifetime, machine capacity, solver IO, random draws, callbacks, and
codecs stay active. Preserve the optimized interned core and every older
constructor and equality proof. No board posts or deployments. Push verified
formalize checkpoints regularly. This checkpoint is progress.

## Current checked target folds, historical slots, and leaf narrowing

Source main remains `8f85ddb6`. The preceding published checkpoint is
`8df6baa2`. Proof commits are `49ae70ae`, `5f547424`, and `94a5c1b1`.
No Haskell implementation or test changes occur. The external Haskell fix
registry remains first in root FINDINGS.md. Add each later fix there with
its failure case, files, commit, checks, and upstream status.

Seven additive modules construct the first-seeded target fold in the CURRENT
checked state. Each actual query computes its next inventory at its literal
entry heap. Projection, allocated merge, recursive tail, and checked native
query retain source order, live equality operations, both native tables,
domain cache, warm merge entries, and global receipts. Only selected path
domains must be closed. Other original siblings can remain open.

Class-specific target inclusion follows from class satisfaction. Shared slots
retain historical target receipts independently of the current inventory.
A hit returns the identical complete state and global bundle without a new
range plan. A miss constructs the target once. The actual leaf then queries
target/input at the force return and retains all slots across the computed
next inventory. Its language narrows the input and preserves the selected
subterm of an original class-satisfying forest. No future successful native
call, final model, admission oracle, or result-language law is supplied.
Initial legitimate warm invariants and reached machine checks remain explicit.

The pinned full Audit passes 2349 jobs and 56708 theorem dependency checks.
Only standard foundations and the old unused-input warning occur. Public
probes, integration kernels, and independent reviews pass. Evidence and
frozen sources are in lean/restart-evidence/20261016-checked-target/.
All 3864 starting files remain. All 2341 older non-Audit proof sources retain
identical bytes. Sixteen frozen manifests, stashes, other worktree records,
and the Haskell registry remain. Earlier unavailable external drafts are not
claimed recovered or reverified. Reuse unchanged-source strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-checked-targets.md and checked-class-edit-next.md in
the evidence directory. Next port structural edits with a returned current
inventory, then the compiled class and right-folded class pass. Same-arity
source setChildren reuses raw internEdge and the original guard. Positional
edits preserve child count. Each class captures the actual preceding tail
and clears only its class-local slots. Final empty propagation, inherited
constraints, and the general constrained outer caller remain open.

The full goal still requires exact generation, count/rank inverses,
probability laws, each optimization's stated semantics, and correspondence
with the current Haskell. Broader frontend and runtime-family adapters and
all separate Sized contracts stay active. The pure selection noConstraint
CAF allocation and GHC forcing adapter remain open. Containers, publication,
concurrency, identity lifetime, machine capacity, solver IO, random draws,
callbacks, and codecs retain explicit boundaries. Preserve the optimized
interned core and every older constructor and equality proof. No board posts
or deployments. Push verified formalize checkpoints regularly. The full goal
remains active; this checkpoint is progress.

## Current checked allocated merge and selected target operands

Source main remains `8f85ddb6`. The preceding published checkpoint is
`b7510ec5`. Proof commits are `784b2168`, `6938c72f`, and
`4d9ea213`. No Haskell implementation or test changes occur.
The external Haskell fix registry remains first in root FINDINGS.md.
Record each later fix there with its failure case, files, commit, checks,
and upstream status.

Five additive modules connect selected target projection and merging to the
CURRENT checked state. Large-row construction demands its canonical empty
equality field at the reached constructor step. Small rows and completed
hits add no such row demand. Dynamic field proofs and constructive lifts
derive physical readiness without an initial Top-available premise.
The same allocated call derives its heap-only graph. Existing finite merge,
language, and global receipt proofs apply to that derived graph.

The full checked wrapper retains both native tables and the domain cache,
allows actual equality-operation growth, and retains concrete Inventory.At.
Initial warm merge Stored and uniform ambient CacheCovers remain explicit.
The literal source subsumption test compares a raw field with Top. It is
different from the broader normalized SourceMemoGate.plain test: an empty
And guard is a checked witness. Independent PCS truth discharges the literal
test's semantic law. This is a proof adapter correction, not a Haskell fix.

Selected support constructs projection followed by the allocated merge.
Other captured siblings can remain open. The result is closed and available.
It retains original values, warm tables, input inventory, loaded fields, and
global receipts. Proper paths give selected-subterm inclusion. Projection
discards ancestor guards and merging can add terms, so no general inverse
language claim is made. An independent kernel composes this operand with
the NEXT generated native query and derives its expanded inventory and
result law from reached ranges.

The pinned full Audit passes 2342 jobs and 56610 theorem dependency checks.
Only standard foundations and the old unused-input warning occur.
Public probes, kernel integrations, and independent reviews pass.
Evidence is in lean/restart-evidence/20261016-checked-merge/.
All 3792 starting files remain. All 2336 older non-Audit proof sources
retain identical bytes.
Earlier frozen proofs, stashes, other worktree records, and the Haskell
registry remain. Earlier unavailable external drafts are not claimed
recovered or reverified. Reuse unchanged-source strict Nix build, 777 examples
plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-checked-merge.md and the checked-target-fold-next.md
evidence note. Next port the first-seeded target fold, class-local target
slots, force and leaf edits, then the class pass, final empty propagation,
and general constrained outer caller. Keep merge and native tables warm.
The pure selection graph still needs its literal noConstraint CAF allocation
and GHC forcing adapter. Final-row allocation alone does not establish that
runtime trace. Containers, publication, concurrency, machine capacity, solver
IO, random draws, codecs, broader full-library targets, and each separate
Sized contract remain active. Preserve the optimized interned core and
every older constructor and equality proof. No board posts or deployments.
Push verified formalize checkpoints regularly. The full goal remains active.

## Current checked Scan global memos and selected required execution

Source main remains `8f85ddb6`. The preceding published checkpoint is
`ca0b8697`. Proof commits are `e715f34c`, `bc99fc26`, `2ce01ce2`, and
`aad5d624`. No Haskell implementation or test changes occur. The external
Haskell fix registry remains first in root FINDINGS.md. Record each later
fix there with its failure case, files, commit, checks, and upstream status.

Ten additive modules connect all three global gate memo tables to CURRENT
checked execution. Actual checked native steps derive constructor event
traces and NoGlobal. Projection and seeded receipts retain exact source
order. CURRENT conjunction exposure, allocated tuples, requirements,
projections, Worklist, Decision, and fourth-memo Call derive their own
physical inputs and returned global tables. No historical Decision/Call
or unchecked whole-engine execution substitutes for these source branches.

The actual current Scan threads those receipts through its reached prefix.
A stop needs no suffix read or range plan. Its semantic endpoint also derives
final Inventory.At and original-class refutation on the SAME Scan. Actual
History, construction, resident load, and live precheck derive cold native
entry and physical facts while retaining the returned equality operations.
Initial legitimate global tables, fourth Correct, source coverage, inherited
stored readiness, and reached ranges remain explicit. No global GHC cache
reset is claimed.

Current selected records retain exact original positions, order, and
multiplicity. Primary certificates replay at the Scan-final heap and derive
finite requireAll execution. Required work retains the SAME equality
operations, both native tables, domain cache, input inventory, and loaded
fields. Its language is exactly the original forest filtered by selected
required paths. It derives every selected path domain without closing
unrelated original siblings. The constructed finite endpoint produces Scan,
then its required worker and global receipts on outcome=none. No completed
Scan, required worker, or future result-law premise is supplied.

The pinned full Audit passes 2337 jobs and 56426 theorem dependency checks.
Only standard foundations and the old unused-input warning occur.
Independent public axiom/signature checks, kernel integrations, and source
reviews pass. Evidence and frozen sources are in
lean/restart-evidence/20261016-current-scan-memos/.
All 3712 starting files remain. All 2326 older non-Audit proof sources
retain identical bytes. Prior frozen proofs, stashes, other worktree records,
and the Haskell registry remain. Earlier unavailable external drafts are
not claimed recovered or reverified. Reuse unchanged-source strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-checked-scan-memos.md and the next-class-edit boundary
note in the evidence directory. Next port actual shared targets and class
edits to the checked state, with Inventory.At and live equality operations.
The older target Fold and leaf use unchecked native Step. Derive Top's
same-cache field only at actual allocating merge branches; do not supply a
universal old-cache Top premise or fabricate allocation on hits/small groups.
Then compose the class pass, empty propagation, and general constrained
outer caller. Keep every other full-library and separate Sized contract
active. Preserve the optimized interned core and all older constructor and
equality proofs. Runtime, containers, allocation, machine, solver, and
callback boundaries remain explicit. No board posts or deployments. Push
verified formalize checkpoints regularly. The full goal remains active.

## Current seeded-query language and sound allocated class scans

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`34066d33`. New proof commits are `20a9336e` and `57ead43f`.
No Haskell implementation or test changes occur. The external Haskell fix
registry stays at the top of FINDINGS.md. Add each later Haskell fix there
with its failure case, affected files, commit, checks, and upstream status.

Seven additive modules carry the actual finite input inventory through the
whole checked seeded fold. Projection retains the same warm native tables.
Each checked native request constructs its next inventory at its actual
entry heap and derives final admission and contextual laws. The induction
retains head projection, tail fold, final native query, and the exact source
rotation `rest ++ [seed]`. Selected path support permits unrelated original
siblings to remain open. Empty input returns literal empty and the unchanged
state. No future model, completed callback, or result-language law is given.

Independent term facts derive a common proper subtree for every satisfied
active original class. The actual checked query retains that subtree.
The CURRENT conjunction memo's true answer therefore refutes the class.
The actual current Scan threads final inventory, physical readiness, loaded
fields, original values, and fourth-memo correctness through its visited
prefix. Every stopped original class has a uniform rejection theorem.
No unvisited suffix is required after a true answer.

The constructed endpoint starts after the actual allocated live precheck.
Original allocation History, source construction, and resident field readback
derive initial Ready, original child Values, active classes, and proper paths.
Literal cold native tables derive initial At without a supplied cache law.
The returned precheck operations remain. Finite Scan, final inventory At,
and stopped-class soundness are conclusions. History, origin coverage,
build, inherited stored readiness, initial fourth-memo Correct, and reached
Ranges remain explicit. Empty fourth tables derive Correct. No global GHC
cache reset or general constrained caller theorem is claimed.

The pinned full Audit passes 2327 jobs and 56369 theorem dependency checks.
Only standard foundations and the old unused-input warning occur.
Public axiom/signature probes, kernel integrations, and independent source
reviews pass. Evidence and frozen sources are in
lean/restart-evidence/20261016-seeded-language/.
All 3638 baseline files remain. All 2319 older non-Audit proof sources retain
identical bytes. Prior frozen proofs, stashes, other worktree records, and
the root Haskell registry remain. Earlier unavailable external drafts are
not claimed recovered or reverified. Reuse unchanged-source strict Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-seeded-language.md. Next compose all three global
gate memo receipts with CURRENT checked Scan, selected required paths and
later edits, then the general constrained outer caller. Keep every other
full-library and separate Sized contract active. Preserve the optimized
interned core and every older constructor and equality proof. Runtime,
container, allocation, machine, solver, and callback boundaries remain
explicit. No board posts or deployments. Push verified formalize checkpoints
regularly. The full goal remains active; this checkpoint is progress.

## Current causal memo admission through exact native queries

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`6ba5d18b`. New proof commits are `f2e119b9`, `4b1d8e25`, and `49184f18`.
Audit and scope note commit is `ff561e50`.
No Haskell implementation or test changes occur. The external Haskell fix
registry remains at the top of FINDINGS.md. Add every later Haskell fix
there with its failure case, affected files, commit, checks, and upstream status.

Nine additive modules derive causal admission for every native memo phase.
Exact source requests derive model membership and captured seen-pair
coverage before lookup publishes them. Demand, finish, and machine effects
retain the same original requests. The invariant transports through actual
input-model growth and derives returned-only Admitted and SeenAdmitted.

Local certificates cover the literal node compiler and actual checked-edge
prefix. Union members, Mu bodies, row pairs, zipped children, and grown-heap
binder reads derive admission from source scope and finite-input closure.
Recursive continuations supply only physical resident-value facts. No child
result law or completed callback supplies membership. The actual trace
simulation derives each reached publication check and every final cell's
coverage. Its static branch families are concretely instantiated.

The exact query endpoint now derives coverage of newly returned internal
requests. The generated-operand endpoint exposes the actual expanded root
inventory and its finiteInput, retains the same warm tables, and returns
that coverage for later model expansion. The preceding one-next-query
coverage gap is closed under the stated initial invariants and word checks.
Initial Good, Contextual, all-cell Covered, Scoped, SemanticReady, Idle,
source growth/history, and reached WordRanges remain explicit for a warm
entry. Empty modeled tables derive initial Covered. No Haskell global reset
or complete generated-history theorem is claimed.

The pinned full Audit passes 2320 jobs and 56321 theorem dependency checks.
Only standard foundations and the old unused-input warning occur.
Independent source reviews found no material defect. Focused checks pass
68 public axiom reports, 78 public signatures, and 46 kernel integrations.
Eight named kernels have additional axiom and signature checks. All use
only the permitted foundations.
A two-generated-query kernel uses the first actual receipt for every second
cache invariant; only its next reached WordRanges is new. Reuse the
unchanged-source strict Nix build, 777 examples plus golden, five-file
Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-native-admission-history.md. Evidence and frozen
sources are in lean/restart-evidence/20261016-admission-history/.
All 3538 baseline files remain. All 2310 older non-Audit proof sources
retain identical bytes. Prior frozen proofs, stashes, other worktree
records, and the root Haskell registry remain. Earlier unavailable external
drafts are not claimed recovered or reverified.

Next carry the concrete expanded inventory and admission through the
complete source seeded fold. Derive common-subtree inclusion, the actual
checked class witness, and current stopped-class rejection soundness.
Compose actual allocated precheck state, all gate memo receipts, selected
required paths, and the general constrained outer caller. Keep every other
full-library and separate Sized contract active. Preserve the optimized
interned core and every older constructor and equality proof. Runtime,
container, allocation, machine, solver, and callback boundaries remain
explicit. No board posts or deployments. Push verified formalize checkpoints
regularly. The full goal remains active; this checkpoint is progress.

## Current semantic input admission and actual allocated Scan entry

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`f37a8fe5`. New proof commits are `953f3b1a`, `61ce6cff`, and `048d9fce`.
Audit and scope note commit is `3b02d00c`.
No Haskell implementation or test changes occur. The external Haskell fix
registry stays at the top of FINDINGS.md. Add every later Haskell fix there
with its failure case, affected files, commit, checks, and upstream status.

Six additive modules derive exact old-domain rank and language agreement
through actual heap growth. An enlarged current inventory admits newly
listed closed resident operands. Cross-view transport retains the same
returned native cells and their contextual laws. It needs explicit old
returned-request admission and coverage of both names in every captured
seen pair. Conditional contextual laws alone do not establish that coverage.

The next-query theorem constructs `oldRoots ++ [left, right]` at the actual
current heap. It derives target Original syntax, input membership, and warm
cache transport, then completes the same checked query with a closed
resident result and exact physical intersection language. No target model,
target contextual law, future return, or desired result law is supplied.
This proves one next query. Causal admission of newly returned internal
cells remains open, so an arbitrary generated-query history and the whole
seeded class fold do not follow yet.

The allocated class-entry adapter uses the precheck's actual returned
operation state. It derives physical Scan.Ready, original proper paths,
actual child availability, ordered original records, and finite current
Scan with fourth memo correctness. No completed historical Scan is a
premise. Original-class rejection soundness remains separate.

The pinned full Audit passes 2311 jobs and 56189 theorem dependency checks.
Focused validation passes 57 public axiom reports, 57 full signatures,
and 34 kernel examples. Only standard foundations and the old unused-input
warning occur. Independent reviews found no material defect. Reuse the
unchanged-source strict Nix build, 777 examples plus golden, five-file
Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-native-semantic-admission.md. Evidence and frozen
sources are in lean/restart-evidence/20261016-semantic-admission/.
All 3463 baseline files remain. All 2304 older non-Audit proof sources
retain identical bytes. Earlier unavailable external drafts are not
claimed recovered or reverified.

Next derive returned-request and seen-pair admission from actual execution,
then iterate the bridge through the seeded fold. Derive common-subtree
inclusion, the checked class witness, and current stopped-class soundness.
Compose actual allocated precheck state, all gate memo receipts, selected
required paths, and the general constrained outer caller. Keep every other
full-library and separate Sized contract active. Retain explicit runtime,
container, allocation, machine-range, solver, and callback boundaries.
Preserve the optimized interned core and every older constructor and equality
proof. No board posts or deployments. Push verified formalize checkpoints
regularly. The full goal remains active; this checkpoint is progress.

## Current finite conjunction class scans and constructed entry

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`2805ce87`. Proof commits are `79a00157`, `14fcff90`, `d03bced1`, and
`e103bb55`. Audit and scope note commit is `b5d30312`. No Haskell
implementation or test changes occur. The Haskell fix handoff at the top
of FINDINGS.md remains current for external agents.

Six additive modules connect the CURRENT conjunction decision and memo to
finite checked class Scan. Actual projections retain the same operation
state. The source first-seeded right fold uses the actual checked native
engine. Closed available operands derive Original syntax at each actual
returned heap. Scope completion and actual physical traces derive final
Good, loaded fields, stored costs, Scoped, Idle, and closed resident queries.
No native memo table is reset between queries.

The whole finite Scan derives its own gates, seeded queries, and current
memo calls. It retains source order, repeated selected occurrences, fourth
memo correctness, and earlier entries. A true answer stops before the suffix.
Reached ranges supply machine checks, not future successful callbacks.
No completed historical Scan, desired result law, or final invariant is a
premise. A covered original field history and actual source build derive
initial Scan.Ready. The cold wrapper also derives empty fourth correctness.
Available forest values, proper paths, coverage, and reached ranges remain
explicit. Only modeled native/domain/operation tables start cold over the
retained equality interner. No Haskell global reset is claimed.

This is finite PHYSICAL completion. Original-class rejection soundness still
needs common-subtree inclusion in the actual seeded query. Closed residency
and Original syntax do not admit a generated operand to a fixed semantic
model or revalidate old warm-cell laws after model expansion.

The pinned full Audit passes 2305 jobs and 56121 theorem dependency checks.
Focused validation passes 29 public axiom reports, 29 signatures, 28 kernel
examples, and one named kernel theorem with its additional axiom report.
Only standard foundations and the old unused-input warning occur.
Independent reviews found no material defect. Reuse unchanged-source strict
Nix build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild.

Read lean/notes-current-conjunction-class-scan.md. Evidence and frozen source
copies are repository-local in lean/restart-evidence/20261016-conjunction-scan/.
All 3401 baseline files remain. All 2298 older non-Audit proof sources and
prior frozen modules retain identical bytes. Earlier unavailable external
drafts are not claimed recovered or reverified.

Next derive semantic input-model admission and warm-cache law transport for
generated operands, then an actual checked class_witness and stopped-class
soundness. Compose actual allocated precheck records/state, the three global
gate memo receipts, selected required paths, and the general constrained
outer caller. Do not infer semantic cache validity from physical scope.
Arbitrary warm operation tables, GHC forcing and publication, allocation
order, concurrency, concrete containers, and machine capacity retain explicit
boundaries. Every other full-library and separate Sized contract remains
active. Preserve the optimized interned core and every older constructor and
equality proof. No board posts or deployments. Push verified formalize
checkpoints regularly. The full goal remains active; this checkpoint is progress.

## Current native entry from original allocation and construction histories

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`8ec2983b`. Proof commits are `07ef6169`, `13950ca4`, and `c585a6d3`.
Audit and scope note commit is `6591e383`. No Haskell implementation or test
changes occur. The Haskell fix handoff at the top of FINDINGS.md remains
current for external agents.

Five additive modules derive initial checked native invariants from one
covered original allocation history and actual source construction.
History events retain normalization checks. Coverage derives normalized
syntax and existing same-cache field loads. Physical Good, SemanticReady,
availability, closedness, and Original syntax are conclusions.

Literal serial field preparation derives its own finite History, atomic
steps, final validity, retained entries, and ordered field readback.
The complete native query history starts at that actual returned interner.
Its entry needs no supplied Good, SemanticReady, Original, model membership,
parent law, future native result, or completed preparation. Normalized
literal fields, initial equality-cache validity, actual source build,
closed available query operands, and reached WordRanges remain explicit.
Final ordered exact languages, closed resident results, and unchanged
cacheable historical repeats follow from the same actual checked walk.

Only the modeled completed operation tables start empty over the retained
interner. No Haskell global reset or GHC eager field-demand order is claimed.
The allocated class-entry adapter also derives exact finite precheck behavior.
Its Scan endpoints retain completed historical Scan as a premise; they do
not transfer the later conjunction decision or prove general termination.

The pinned full Audit passes 2299 jobs and 56075 theorem dependency checks.
Focused validation passes 18 public axiom reports, 18 signatures, 26 kernel
examples, one named kernel theorem, and three executable evaluations.
Only standard foundations and the old unused-input warning occur.
Independent reviews found no material defect. Reuse unchanged-source strict
Nix build, 777 examples plus golden, five-file Fourmolu, and four-package
Cabal-gild.

Read lean/notes-current-native-original-entry.md. Evidence and frozen source
copies are repository-local in lean/restart-evidence/20261016-original-entry/.
All 3347 baseline files remain. All 2293 older non-Audit proof sources and
prior frozen modules retain identical bytes. Earlier unavailable external
draft bytes are not claimed recovered or reverified.

Next connect the CURRENT conjunction decision and its memo/worklist effects
to class Scan. Then compose current checked native callbacks, selected
required paths, and the general constrained outer caller. Do not replace
this obligation with the historical completed Scan premise. Warm operation
tables, new generated operands, cross-model admission, runtime/GHC forcing
and publication, allocation order, concurrency, concrete containers, and
machine capacity retain explicit boundaries. Every other full-library and
separate Sized contract remains active. Preserve the optimized interned
core and every older constructor/equality proof. No board posts or
deployments. Push verified formalize checkpoints regularly.
The full goal remains active; this checkpoint is progress.

## Current exact serial native histories and retained warm answers

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`3e84dab7`. Proof commits are `ef5bbc8e`, `2bdf6641`, and `c8fe3b9f`.
Audit and scope note commit is `133ffb69`. No Haskell implementation or test
changes occur. The Haskell fix handoff at the top of FINDINGS.md remains
current for external agents.

Five additive modules derive one input model for the complete finite list
of closed Original available operands, then complete the literal serial
Code.walk in that same fixed model. Every actual head receipt supplies the
tail's physical, contextual, scope, and semantic invariants. Whole-walk
WordRanges derives each head and tail plan through actual reached traces.
There is no per-query future-success or result-law callback.

The final receipt retains ordered exact intersection languages, closed
resident values, and actual final returned cells for every cacheable query.
Each such historical query repeats in two checked steps with the whole
final checked state unchanged. Requests without a key retain their direct
body path and have no warm-hit claim. Empty and duplicate histories are
covered. The cold endpoint derives initial Contextual, Scoped, Idle, and
all operand model membership from the finite source inventory. Initial
Good, SemanticReady, and actual-prefix WordRanges remain explicit.

The pinned full Audit passes 2294 jobs and 56040 theorem dependency checks.
Focused validation passes 21 public axiom reports, 21 signatures, 37 kernel
examples, and two named kernel theorems. Only standard foundations and the
old unused-input warning occur. Independent reviews found no material
defect. Reuse unchanged-source strict Nix build, 777 examples plus golden,
five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-native-warm-history.md. Evidence and frozen source
copies are repository-local in lean/restart-evidence/20261016-warm-history/.
All 3291 baseline files remain. All 2288 older non-Audit proof sources and
the preceding frozen modules retain identical bytes. Earlier missing
external draft bytes remain unavailable. They are not claimed recovered
or reverified.

Next derive initial Good and SemanticReady from complete original allocation,
normalization, and loaded-field histories at the actual caller boundary.
Compose with the current class Scan and constrained outer caller. The new
history uses a fixed source and listed original operands; new allocations,
generated operands, and cross-model cache admission remain separate.
Runtime/GHC forcing and publication, concurrency, concrete containers, and
machine ranges retain explicit boundaries. Every other full-library and
separate Sized contract remains active. Preserve the optimized interned
core and every older constructor/equality proof. No board posts or
deployments. Push verified formalize checkpoints regularly.
The full goal remains active; this checkpoint is progress.

## Current actual result scope and closed exact cold returns

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`9fab9f35`. No Haskell implementation or test changes in this update. The
Haskell fix handoff near the top of FINDINGS.md remains current.
Proof commits are `6d6f142e`, `bf2669ee`, and `db8f6efa`.

Seven additive modules derive scope through actual checked execution.
Returned node and edge cells retain the scope of their original request.
The paired independent request induction derives each local scope before
its actual protected finish. Static certificates follow all actual source
branches and guarded edge prefixes. They require no input-language model.

The cold scope endpoint derives initial scoped tables and Idle, then proves
result.free = []. ColdClosedExact combines this with the independent language
proof by completed-result uniqueness. Both the literal value and complete
checked state are equal. The same contextual Receipt therefore carries
scoped tables, final Idle, an empty result free list, and exact original
intersection language. No parent law, parent scope, completed child callback,
final invariant, or future physical plan is a public premise.
Initial Good, SemanticReady, and actual-prefix WordRanges remain explicit.

The pinned full Audit passes 2289 jobs and 55998 theorem dependency checks.
Focused validation passes 40 public axiom reports, 40 signatures, 32 kernel
examples, and one named kernel theorem. Only standard foundations and the old
unused-input warning occur. Independent reviews found no material defect.
Reuse unchanged-source strict Nix build, 777 examples plus golden, five-file
Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-native-closed-scope.md. Evidence and frozen source
copies are repository-local. All 3229 baseline files remain. All 2281 older
non-Audit proof sources and the preceding nineteen frozen modules retain
identical bytes. Earlier missing external draft bytes remain unavailable and
are not claimed recovered or reverified.

Next admit warm caches from actual serial histories in one fixed model.
A model for two initial roots need not validate later roots. Source residency
alone is insufficient; derive coverage of the full finite query inventory.
Then compose complete original allocation, normalization, and loaded-field
histories with the current class Scan and constrained outer caller. Keep
runtime/GHC forcing and publication, concurrency, concrete containers, and
machine ranges explicit. Every other full-library and separate Sized target
remains active. Preserve the optimized interned core and every older proof.
No board posts or deployments. Push verified formalize checkpoints regularly.
The full goal remains active; this checkpoint is progress.

## Current actual contextual completion and cold root exactness

Source main remains `8f85ddb6`. The preceding published proof checkpoint is
`4d74d00c`. No Haskell implementation or test changes in this update. The
Haskell fix handoff near the top of FINDINGS.md remains current.
Proof commits are `551371b0`, `809fa691`, and `4b14d7be`.

Nine additive modules prove actual paired contextual completion. The strong
independent request induction discharges both node and edge body obligations.
Local source certificates derive every node branch and actual checked edge
prefix. A miss derives its local language law before its actual finish. A
warm hit recovers the exact requested law from both cache invariants.

cold_complete derives fixed original input models and ranks from closed,
available Original operands. Empty native memo tables derive initial
Contextual and Idle. Initial Good, SemanticReady, and actual-prefix WordRanges
remain explicit. It returns one actual checked Receipt with physical effects,
final Contextual and SemanticReady, result availability, final Idle, and exact
original intersection language for every output environment and term.
No own-root finish law, completed body callback, final validity, or future
physical input plan is a premise. The older FinishThrough endpoints retain
their conditional scope; this cold endpoint independently derives root meaning.

The full pinned Audit passes 2282 jobs and 55887 theorem dependency checks.
Only standard foundations and the old unused-input warning occur. Focused validation passes 66 public axiom reports, 66 signatures, and
43 kernel examples across all nine modules. Each has saved logs.
Reuse the unchanged-source strict Nix build, 777 examples plus golden,
five-file Fourmolu, and four-package Cabal-gild results.

Read lean/notes-current-native-contextual-root.md. New evidence and frozen
source copies are repository-local. All 3147 baseline files remain. All 2272
older non-Audit proof sources and the previous ten frozen modules retain
identical bytes. Earlier missing external draft bytes remain unavailable and
are not claimed recovered or reverified.

Next derive result Scope and cached free-list closedness, admit warm caches
from real histories, and compose complete original allocation and annotation
history with the current class Scan and constrained outer caller. Runtime/GHC
forcing and publication, concurrency, concrete containers, and machine ranges
remain explicit. All other full-library and separate Sized targets remain
active. Keep the optimized interned core and every older constructor/equality
proof. No board posts or deployments. Push verified formalize checkpoints
regularly. The full goal remains active; this checkpoint is progress.

## Current paired physical completion and actual Mu/reference meaning

Source main stays `8f85ddb6`, merged at `7dccd588`. Checkpoint `554a116f`
is published on formalize. Haskell source and tests stay unchanged. The fix
handoff near the top of FINDINGS.md remains current for external work.
Proof commits `bcc1165d` and `60e83ee8` add general checked physical
completion and actual bound-reference/Mu branch composition.

The strong independent request induction now discharges both node and edge
body completion hypotheses internally. Constructed traces derive the reached
physical input plan. Closed Original available roots complete from initial
Good and Idle, returning physical invariants, exact effects, availability,
and final Idle. Actual-prefix WordRanges remains explicit. Good includes
physical cache validity, ready heap, operation validity, and loaded fields.
No own-body completion or future InputsThrough premise remains at this endpoint.
This is checked-model physical completion under those contracts.

Reference resolution derives original bound scope and actual readback. The
selected Mu bodies derive middle SemanticReady from their child trace, then
complete the actual optional binder and derive the parent contextual law.
Only the exact child's local NodeLaw and physical trace/effects remain as
recursive semantic hypotheses. The global contextual semantic/cache induction,
result closedness, and independent root language correctness remain open.
Do not treat the older FinishThrough endpoint as an independent root proof.

The full audit passes 2275 jobs and 55741 theorem dependency checks.
Focused validation passes 104 public axiom reports, 62 signatures, 70 examples,
and one named kernel theorem across this update and the preceding seven modules.
Only standard foundations and the old unused-input warning occur. Independent
reviews found no material defect. Reuse the unchanged-source Nix build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

Read lean/notes-current-native-paired-physical-completion.md, then the two
preceding physical/source notes. All ten frozen module hashes and new evidence
are repository-local. The 3052-file baseline has no missing file; all 2262 older
non-Audit proof sources remain byte-identical. Earlier missing external draft
bytes remain unavailable and are not claimed recovered or reverified.

Next combine actual recursive returns with contextual child laws, preserve
Contextual at each actual finish, derive result scope/closedness and admissible
warm-cache use, and prove root exactness without its own finish-law premise.
Then compose original allocation histories, the current class Scan, and the
constrained outer caller. All other full-library and separate Sized targets
remain active. Runtime capacity, GHC forcing/publication, concurrency, frontend,
and graph/synthesis adapters retain their recorded boundaries. Keep the
optimized interned core and every older constructor/equality proof. No board
posts or deployments. Push verified formalize checkpoints regularly.
The full goal remains active; this checkpoint is progress.

## Current physical checked execution and actual branch meaning

Source main `8f85ddb6` is merged at `7dccd588`. PR #54 retains named child
measure terms over `every`. PR #55 exposes explicit typing automata and the
`Typing` record API. Native intersection, equality, constructors, and Sized
source bodies stay unchanged. The Haskell repair handoff at the top of
FINDINGS.md records files, failures, commits, checks, and upstream status.
The optimized interned core and all older constructor/equality proofs remain.

Proof commits `3ca57b91` and `7d9d433b` add seven new modules. Physical native
cache validity and actual checked execution need no semantic Produced receipt.
Exact current operands, key bounds, running cells, and returned residency
supply physical checks. Operation/field preservation and strict request bounds
now derive actual yielded transitions. Pure body misses complete. The general
recursive completion induction and reached physical plan remain open.

Local node laws cover empty, repeated-reference, self, swap, reset, and unions.
Actual checked edge, selected union, and ordinary-node bodies derive their
parent contextual laws from exactly the reached child laws and effects.
Original input models stay fixed. All exact returned states retain the actual
operation cache and both native tables. Costs are not derived by these branch
laws. Recursive child completion and semantic laws remain induction obligations.
The existing FinishThrough endpoint includes its own root finish law; it is
conditional transfer, not independent root correctness.

The full audit passes 2272 jobs and 55698 dependency checks. Focused probes
pass 81 public axiom checks, 47 signatures, 53 examples, and one named kernel
theorem. Only standard foundations and the old unused-input warning occur.
Strict Nix build, all six suites with 777 examples plus golden, five-file
Fourmolu, and four-package Cabal-gild pass. No local test file changes.

Read lean/notes-current-native-physical-meaning.md and
lean/notes-main-8f85ddb6.md. Evidence is repository-local under
lean/restart-evidence/20261016-physical/ and the recorded new files in
lean/restart-evidence/20261016-recursive/. The 3052-file starting baseline and
new frozen module hashes record preservation. Earlier missing external draft
bytes remain unavailable after the documented temporary-directory reset.
They are not recovered or claimed reverified.

Next construct protected-frame actual traces through bind and finish. Close
the joint node/edge completion and semantic induction from initial invariants.
Then compose original allocation histories, the current class Scan, and the
constrained outer caller. Keep every other full-library target and every
separate Sized contract active. No old eager execution or historical Scan
substitution. No board posts or deployments. Push verified formalize
checkpoints regularly. This checkpoint is progress; the full goal stays active.

## Current contextual Mu components and source main d44b2a0f

Source main `d44b2a0f` is merged at `b09f4ebb`. Upstream adopts the finite
needed-type repair from `ca0e9a65`. Typing.hs now matches main. New synthesis
uses reduction-round order and refold edge mappings. The optimized interned
core and all older proofs remain. The package delta from main contains only
the historical constructor changelog entry and the equality reproducer comment.
The Haskell fix handoff near the top of FINDINGS.md records failure cases,
paths, commits, checks, and upstream status for external work.

Proof commits are `1ce04615`, `dc64812b`, `43b910be`, `22b5e0fc`, and
`06a73330`. Actual maybeMu least language and unfolding now support local
soundness and rank-sum completeness. The induction derives fresh candidate
containment. Literal source bindings, domain entry, pair codecs, and stored
body inputs derive the Mu adapter from a contextual law for the actual child.
Child completion and that child law remain recursive obligations.

Stronger returned-cell NodeLaw/EdgeLaw invariants survive lookup, demand,
physical advance, and actual checked execution when reached finishes supply
their local laws. Closed input models and rank erasure construct exact closed
receipts from actual body traces and physical effects, with no final native
validity premise. Initial Original closed operands derive physical code
certificates, independent request bounds, and actual checked edge prefixes.

The actual query endpoint is conditional readback and cache transfer. For a
started query, FinishThrough includes its own root finish law. The names
query_law_of_finish_laws and query_exact_of_finish_laws make this explicit.
Do not use that plan as an independent derivation of root language correctness.
Prove the actual body law before its finish step. General checked completion,
recursive semantic body induction, reached input/finish plans, and adequate
initial warm contextual-cache admission remain open.

The new birth-order component proves first observed rounds, min transport,
injective key-renaming lookup, fallback bounds, and a supplied-total-step
history bound of thirty-one. It does not prove process-history independence.
Actual traversal/refolding, empty-history rejection, identity/counter bounds,
IntMap, Double, and canonical enumeration order remain source adapters.

The full audit passes 2,265 jobs and 55,567 dependency checks. Ninety-seven
public axiom checks, seventy-two signatures, sixty proof examples, and one
additional named kernel theorem pass. Only standard foundations and the old
unused-input warning occur. Independent reviews found no proof defect and
made the root-finish premise explicit. Strict Nix all-component build, all
six suites with 770 examples plus golden, ten-file Fourmolu, and four-package
Cabal-gild pass. No local test file is changed.

Read lean/notes-current-native-contextual-completion.md and
lean/notes-main-d44b2a0f.md. Fresh evidence is repository-local at
lean/restart-evidence/20261016-recursive/. The execution environment reset
its temporary directory. Before the reset, 2,981 baseline files and nineteen
external drafts were verified. Their temporary snapshots and external bytes
are unavailable afterward. Do not claim those missing bytes were reverified
or recovered. All 2,981 tracked baseline files remain; older non-Audit proof
sources are byte-identical. No missing draft is reconstructed.

Next prove paired actual checked body completion and result semantics from
initial invariants. Preserve running frames, loaded fields, semantic heaps,
and costs at the same returned state. Then compose original whole allocation
history, the new current class Scan, and the actual constrained outer caller.
Keep every other full-library target and each separate Sized contract active.
No old eager execution or historical Scan substitution. No board posts or
deployments. Push verified formalize checkpoints regularly. The full goal
remains active. This turn is progress: source refresh, eight proof modules,
Haskell fix handoff, source validation, and repository-local evidence.

## Current recursive pair contexts and finite typing order

Source main is `885a446e`, merged at `aa981389`. Upstream fixes ordinary
helper declaration order. The preserved Z/A reproduction now agrees with
fromDatatype. Local repair `ca0e9a65` prevents unused type-growing descriptions
from blocking finite typing ranks. It restricts metadata discovery to actual
row constructor types, while retaining complete local declaration indices.
The two-leaf non-regular reproduction now returns exactly Right [One,Two].
Standard Bool remains False before True; its documentation is corrected.
The optimized interned core and all older proofs and repairs remain intact.

Proof commits are `24a5358c` and `a911bd69`. Audit and notes are in `28636822`.
Actual closed original inputs derive independent InputMeaning and RankedInput
without a desired output law. New SoundPairs and rank-bounded CompletePairs
support fresh typed pair overrides and actual repeated-reference laws.
The exact arbitrary-candidate SeenContext extension is formally refuted.
Complete extension has a local candidate-containment obligation. Derive it
inside the full Mu proof by smaller original input ranks; do not export it
as an assumed parent-result law. General Mu semantics and warm open-cache
admissibility remain open. Closed NodeProduced alone does not supply them.

The historical helper-position phase retains exact local indices, source
order, last-label-winner lookup, and zero fallback. The repaired executable
walk derives its complete traversal from a finite needed inventory. Its
measure is unseen needed occurrences followed by pending length. It works
with an infinite-key description function and skips the unused growing chain.
The actual needed row-symbol inventory, sufficient needed-only ancestor
coverage, Generic/label coherence, containers, Int bounds, and full value/rank
correspondence remain adapters. Atomic literal-domain order remains separate.

The full audit passes 2,257 jobs and 55,353 dependency checks. Thirty-two
public axiom probes, twenty-three signatures, and twenty-eight literal kernel
examples pass. Only standard foundations and the old unused-input warning
occur. Independent reviews found no context or relevant-filter defect under
the stated source coherence boundary. Upstream strict all-component build
and 225 generator examples pass. After the local repair, the focused strict
generator build, all 225 generator examples, exact growing/Z-A/Bool probes,
and Fourmolu pass. Other five suites are reused from the unchanged preceding
source: combined 768 examples plus golden. Package files retain Cabal-gild.
No local test file is changed.

Next derive general checked completion and recursive finish receipts through
the actual checked traces. Prove the Mu containment/rank induction and a
stronger warm open-cache or causal-history invariant. Compose original whole
allocation history, the new current class Scan, and the physical outer caller.
Do not substitute the historical Scan or old eager execution. Continue every
other full-library target and every separate Sized contract. Full scope stays
active. Read lean/notes-current-native-pair-contexts.md and
lean/notes-typing-relevant-order.md.

Start: /tmp/mcfta-allocated-query-checkpoint-20261016-0357/ (2,976 files).
Closing: /tmp/mcfta-pair-helper-checkpoint-20261016-0415/.
Script: /tmp/mcfta-preserve-pair-helper-20261016.py. Evidence uses
/tmp/mcfta-pair-helper-*, pair-context validation, helper-order validation,
and the marked Bool/growing source reproductions. All sixteen prior external
drafts stay. Three new marked source drafts bring the total to nineteen.
Stashes and other worktrees stay. No board posts or deployments.
Push verified formalize checkpoints regularly. The last allowance observation
was 81 percent and is stale. Stop owned work at 1 percent or less.
The full-library goal remains active.

## Current checked query composition and completion prerequisites

Source main is `78618ea2`, merged at `45475383`. It adds rooted refinement
conditions, polymorphic literals, and positional node-view name checks.
Native intersection, conjunction emptiness, and Typing source stay unchanged.
Proof commits are `ae797af8`, `2cfa0e21`, `ef14ad04`, and `541ae1cd`.
Audit and scope notes are in `c5440696`. The optimized interned core and
all older constructor/equality proofs remain. Full library scope stays active.

Actual checked finite execution now preserves SemanticReady and stored
CostHeap from current physical inputs. All outcomes retain their actual
states. The combined endpoint derives readiness, fields, native validity,
and both histories at that same returned state. CostHeap is an unfolding
invariant, not a runtime complexity bound.

The completed checked query now enters the new conjunction memo with the
actual constructor heap and equality cache. It derives result availability,
checked provenance, final idle/valid native tables, correct saved entries,
old-entry retention, and conservative answer soundness. Advancing the memo
result retains both full native tables and the domain cache. A true answer
excludes common original terms for closed operands in the exact empty domain.
The actual query completion and reached input plan remain explicit premises.
That plan includes semantic NodeProduced/EdgeProduced checks at finish cells.

New actual checked running proofs restore enclosing active bounds. New child
bounds use only the independent original-input requiredFuel measure. Checked
rejection skips child requests and effects. Actual-prefix Words/WordRanges
preserve exact full states. They do not generate range or completion proofs.
The new derive name phase proves exact positional prefixes, first-error
order, diagnostic text, and earlier shape-error precedence. It does not
supply Generic/schema/codec or rooted measure correspondence laws.

Next derive general checked query completion and its reached input receipts.
The recursive Mu proof needs open-context soundness and rank-bounded
completeness. Exact SeenContext cannot extend to arbitrary binder candidates.
Warm returned cells currently carry only closed/empty-domain language laws;
derive a stronger open-cache invariant or adequate causal-history proof.
Compose initial whole-heap allocation histories, then define the new current
Scan and complete the physical class/outer caller. Do not substitute the
historical intersection Scan or an old eager native execution. Continue all
other full-library and separate Sized targets. Typing helper-order disagreement
remains in main; the fetched fix branch is unmerged.

The full pinned audit passes 2,254 jobs and 55,292 dependency checks.
Forty-eight public axiom probes, thirty-six signatures, and fifty literal
kernel examples pass. Two extra named kernel theorems are counted separately.
Only standard foundations and the old unused-input warning occur. Independent
review found no state-threading or conservative-soundness defect. The refreshed
strict Nix build and all six suites pass: 767 examples plus golden. Fourmolu
checks four changed Haskell files with the new fixities. Cabal-gild checks
four active packages. No new test file is committed.

Read lean/notes-current-allocated-query-memo.md and
lean/notes-main-78618ea2.md. Start preservation is
/tmp/mcfta-allocated-fields-checkpoint-20261016-0331/ (2,967 files).
Closing preservation is /tmp/mcfta-allocated-query-checkpoint-20261016-0357/.
The script is /tmp/mcfta-preserve-allocated-query-20261016.py. Evidence uses
/tmp/mcfta-allocated-query-*, native semantic/cost/running/request validation,
and /tmp/mcfta-derive-78618ea2-*. Sixteen prior external marked drafts,
stashes, and other worktrees remain. No board posts or deployments.
Push verified formalize checkpoints regularly. The last allowance observation
was 81 percent and is stale. Stop owned work at 1 percent or less.
The full-library goal remains active.

## Current loaded-field closure through checked native execution

Source main stays `894a74af`. No Haskell source changes. Proof commits are
`ec36d774`, `1b035257`, `0f6968e2`, and `d77c8389`. Audit and scope note are
in `86171cb4`. The optimized interned core and all older proof definitions
stay. Full library scope remains active.

Actual constructor, conjunction, ready intersection, and sentinel allocation
receipts now derive successful field loads in the exact returned operation
cache. Normalized Top alone has a verified cold-cache miss. No universal
conjoin-cache closure is assumed. Allocation-aware compiled continuations
retain their loads through actual cache growth and raw constructor effects.

The checked body derives its original loads from resident initial Fields.
Ready and sentinel branches derive new annotations from their actual
allocation receipts. Every native step retains loaded fields at its returned
cache. Finite execution derives the reached field checks, full physical and
operation histories, and the actual yielded continuation. Errors and blocked
outcomes keep their real states. Blocked continuations are not certified by
the OutcomeFields predicate. The source guard equality instance stays pinned.

Actual primary/secondary gates, nodeEdges, heads, and supported projections
retain the same loaded fields with unchanged operation state. A false class
trace derives finite projection for a selected proper path at its exact
anchor. Unrelated original siblings can remain open.

The execution plan still includes reached word checks and actual finish-cell
NodeProduced/EdgeProduced receipts. This is field closure, not a general
checked native completion proof. Initial whole-heap allocation history still
needs composition. The older scoped Fold/Seeded has no operation-cache state.
Do not erase its execution differences or reuse the historical Scan body.
Next define the reached allocation-aware query. Derive its completion, input
receipts, independent language, SemanticReady, and CostHeap at the same final
heap. Then enter the new conjunction memo and define the current Scan.
Continue general constrained outer completion and every other full-library
and separate Sized target. Keep older constructor and equality work.

The full audit passes 2,247 jobs and 55,211 dependency checks. Thirty-nine
public axiom probes, twenty-one endpoint signatures, and thirty-one kernel
examples pass. Only the standard foundations and old unused-input warning
occur. Independent review found no cache-indexing or circularity defect.
Haskell is unchanged, so the prior strict Nix build, six suites with 763
examples plus golden, post-repair 224 generator examples, Fourmolu, and
Cabal-gild are reused. Read lean/notes-current-allocated-native-fields.md.

Start: /tmp/mcfta-typing-checkpoint-20261016-0318/ (2,961 files).
Closing: /tmp/mcfta-allocated-fields-checkpoint-20261016-0331/ (2,967 files).
Script: /tmp/mcfta-preserve-allocated-fields-20261016.py. Evidence uses
/tmp/mcfta-allocated-*, /tmp/mcfta-current-allocated-*, and
/tmp/mcfta-conjunction-field-allocation-*. Sixteen external marked drafts,
stashes, and other worktrees are preserved. No board posts or deployments.
Push verified formalize checkpoints regularly. The last allowance observation
was 81 percent and is stale. Stop owned work at 1 percent or less.
The full-library goal stays active.

## Current typed-rule graph exactness and source repair

Source main is `894a74af`. It includes the typing API from `c52d5c3e` and
merges the same recursive-field repair as local `2e25be03`. Merges `727fa870`
and `73475670` retain both histories. All generator files have identical
bytes before and after the second merge. The optimized interned core stays.
Proof commits are `7871a676`, `23fa596d`, and `d1f62e7b`.
Audit and scoped notes are in `0908f20c`. Full library scope stays active.

Independent typing judgments now describe ordinary rules, exact matching
environment positions, binder order, and positive Subterm nesting. The finite
visited-map traversal derives exact final rows and child-key closure. The
computed root graph accepts exactly independent empty-environment derivations
under the stated fixed-field law. No completed graph oracle is supplied.
The unconditional endpoint has permissive fixed-tree semantics. This proves
supplied-rule semantics. Datatype typing and callback index fidelity still
need constructor, schema, and codec laws. Global LawfulFixed is stronger
than reached-only source checks. The direct field predicate does not imply it.

The source repair rejects fixed values in fields of the target datatype.
Both ill-scoped and over-bound recursive fixed-tree reproductions now return
FieldMismatch. The existing field-mismatch example covers both cases.
A separate reproduction still shows helper declaration-order disagreement:
fromDatatype returns Lit Z before Lit A; fromTypingRules reverses them.
This order defect is unresolved. Preserve the shared rank-order target.

The aggregate audit passes 2,242 jobs and 55,122 dependency checks. Forty-five
public axiom probes, nine endpoint signatures, and thirty kernel examples
pass. Only the standard foundations and the existing unused-input warning
occur. Strict Nix build and all six suites pass at the source refresh: 763
examples plus golden. After repair, all 224 generator examples pass again.
Other suites are reused because only Typing changed. Fourmolu checks three
changed Haskell files. Cabal-gild checks four packages. Upstream then merges
byte-identical generator files, so these source checks remain applicable.

Next continue actual native query and checked constraint allocation to derive
equality-cache Fields. Connect the new conjunction memo to a new current Scan.
Do not supply future Fields or reuse the historical Scan as current execution.
General constrained outer completion, lazy demand and publication, machine
identities/capacity, concrete containers, broad API integration, and all separate
Sized contracts remain open where recorded. Preserve older constructor and
equality work. Read lean/notes-typing-rules.md and lean/notes-main-c52d5c3e.md.

Start snapshot: /tmp/mcfta-conjunction-worklist-checkpoint-20261016-0250/
(2,953 files). Closing: /tmp/mcfta-typing-checkpoint-20261016-0318/ (2,961 files).
Script: /tmp/mcfta-preserve-typing-20261016.py. Evidence uses /tmp/mcfta-typing-*.
Sixteen external marked drafts, stashes, and other worktrees are preserved.
No board posts or deployments. Push verified formalize checkpoints regularly.
The last allowance observation was 81 percent and is stale. Stop owned work
at 1 percent or less. The full-library goal remains active.

## Current allocated conjunction worklist and completed memo

Source main remains `a4f38cbb`. The refresh found no new source change.
Proof commits are `692b5efb`, `fc19ceeb`, `8796bf90`, `d4162cc7`,
`71af830d`, `5995899d`, `2829037a`, and `78f0c1c7`.
Full library scope stays active. Earlier sections retain historical scopes.

Actual physical tuples now retain source order and accepted-edge coverage.
The equality fold loads original fields, runs actual allocated accessors,
stops at a contradictory head, and derives canonical combination receipts.
Requirements construct child columns and row-major class projections.
Common-heap coherence derives the identity-map key law.
One row graph threads both returned heaps and derives smaller accepted witnesses.

The dynamic worklist constructs every reached row from initial invariants.
Only admission decreases its budget. Open pending operands can be skipped.
Actual Run derives returned readiness, resident table domains, and local
coverage for each stored entry. Literal Boolean grow completes in at most
budget plus one comparisons. A true verdict excludes every accepted finite term.
No fixed edge/project/row supplier or future invariant is supplied.
The new Decision derives the open shortcut or completed closed worklist.
SourceCurrentConjunctionMemo.finite constructs valid completed hits/misses
using this new Decision. The historical intersection-based Call is not used.

The schedule completes rows before logical insertion. Haskell stores lazy
rows and can demand or skip prefixes differently. This is not a proof of GHC
forcing, equal source heaps/Booleans under reordered reads, pending publication,
or runtime allocation order. Initial Ready includes equality-cache Fields.
Next derive that invariant through actual native query and checked constraint
allocation, then connect the new memo to the current class prefix and new Scan.
Do not substitute a future Fields premise or the historical Scan body.
Continue general constrained completion and every other full-library target,
including all separate Sized contracts and older constructor/equality work.

The pinned full audit passes 2,238 jobs and 54,980 dependency checks.
Seventy-five public axiom probes and 62 kernel examples pass.
Only standard foundations and the preexisting unused-input warning occur.
Thirteen new modules and one note preserve all earlier non-Audit proof files.
Audit gains one import. No Haskell/package source changes. The prior strict
Nix build, six suites with 755 examples plus golden, Fourmolu, and Cabal-gild
checks remain applicable and were not repeated for this proof-only increment.

Read `lean/notes-current-conjunction-worklist.md` for the exact proof boundary.
Start: `/tmp/mcfta-general-scan-checkpoint-20261016-0228/` (2,939 files).
Closing: `/tmp/mcfta-conjunction-worklist-checkpoint-20261016-0250/` (2,953 files).
Script: `/tmp/mcfta-preserve-conjunction-worklist-20261016.py`.
Evidence uses `/tmp/mcfta-conjunction-*` and `/tmp/mcfta-current-conjunction-*`.
Fourteen external marked drafts, stashes, and other worktrees remain.
The last weekly allowance was 81%; it is stale. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints regularly.
The full-library goal stays active. HANDOFF.md records per-command SSH port443.

## Current finite class prefixes and conjunction read completion

Audited source main is `a4f38cbb`, merged at `a140c37b`.
It changes CI scheduling only. Haskell semantics remain at the prior source
checkpoint. Proof commits are `25165c9c`, `a57bc0b7`, `abc52af9`,
`14422982`, and `00c44f26`. Audit and notes are in `0b865a79`.
Full library scope stays active. Earlier sections retain historical scopes.

Both current class gates now derive finite stable traces directly from
initial semantic readiness, costs, and available inputs. The false-secondary
seeded query derives its actual projections, native calls, and returned
physical invariants under reached range checks. The composed per-class
prefix constructs selected, skipped, or queried outcomes from the initial
invariants. It stops before provablyEmpty and assumes no completed gate/query.

The literal conjunction map now has exact overwrite, last-winner, ascending
readback, and faithful-key canonical sequence proofs. Actual finite nodeEdges
and row-major getPath reads derive resident closed outputs and retained
semantic, cost, and annotation heaps. Accepted-edge and selected-subtree
language laws follow from the actual reads.

Source boundary: SourceCurrentEmptinessDecision.closed still embeds the
historical native-intersection TaskTrace body. Its memo Call and Scan consume
that body. Those proofs remain valid for their definitions. They do not
establish the post-4101 conjunction source algorithm's Boolean or heap result.
Conservative soundness alone cannot equate the two bodies. Earlier sections
that use these Decision/Scan names retain this historical body boundary.

Next thread actual reads through literal tuples, equality accessor/combine
allocation, child columns, class projections, identity-map canonicalization,
and the dynamic pending worklist. Then define current Decision, memo Call,
and Scan, and connect the scan to the executable physical class pass.
Preserve reached word checks, native constraint-allocation transfer, pending
publication, GHC demand, machine identity, and concrete container boundaries.
Continue general constrained completion and every other full-library target,
including all separate Sized contracts and older constructor/equality work.

The full pinned audit passes 2,225 jobs and 54,843 dependency checks.
Only permitted foundations and the existing unused-input warning occur.
Forty public axiom probes and 23 kernel examples pass. The prior strict Nix
build, 755 examples plus golden, Fourmolu, and Cabal-gild results remain valid.
Haskell checks were not repeated for this CI-only and proof-only increment.
Five new modules, two notes, and three additive Audit imports preserve every
older non-Audit proof file. Only the upstream CI file changes outside proofs/docs.

Read `lean/notes-current-conjunction-completion.md` and
`lean/notes-main-a4f38cbb.md`. Start snapshot has 2,932 files:
`/tmp/mcfta-memo-target-workers-checkpoint-20261016-0213/`.
Closing: `/tmp/mcfta-general-scan-checkpoint-20261016-0228/` (2,939 files).
Script: `/tmp/mcfta-preserve-general-scan-20261016.py`.
Evidence uses `/tmp/mcfta-general-scan-*`, `/tmp/mcfta-current-class-*`,
`/tmp/mcfta-seeded-query-*`, `/tmp/mcfta-conjunction-map-*`, and
`/tmp/mcfta-conjunction-completion-reads-*`. Fourteen external drafts, stashes,
and other worktrees remain. The last weekly allowance was 81%; it is stale.
Stop owned work at 1% or less. No board posts or deployments. Push verified
formalize checkpoints regularly. The full-library goal stays active.

## Current executable memo-aware class completion

Audited source main is `6baa0e25`, merged at `416f0f39`.
Proof commits are `e6cd7144`, `ed4d2a22`, `939612a9`, `ebc925e8`,
and `91724f7b`. Audit and scope notes are in `6be321b2`.
Full library scope stays active. Earlier sections retain their historical
source definitions and proof boundaries.

Executable memo-aware target, shared leaf, signed edit, row, and class
workers now have successful graph correspondence and stable completion.
Actual finite graphs derive sufficient bounds for the same results and
full returned native, target-slot, and completed merge-table states.
Initial physical invariants and selected domains construct finite targets
and class passes. No future cache validity or recursive completion is supplied.
Unselected original siblings can remain open.

`SourceCurrentMemoPhysicalClassWorker.live_scan_pass` composes live entry,
actual successful Scan, finite required execution, and one executable class
pass under its reached range plan. The same pass supplies six-stage stable
completion, a sufficient common bound, normalized fields, physical readiness,
producer histories, selected domains, fourth-memo correctness, ordered global
receipts, and independent original-forest language bounds. Only its completed
merge table starts empty. The exact caller still checks original constraints.

Successful Scan and actual-prefix native range checks remain premises.
These bounds instrument logical execution. They do not measure runtime work.
The sequential worker order does not prove literal lazy GHC forcing or
cache-allocation order. Pending publication, runtime identities, concurrency,
and concrete host representation remain separate obligations.

Main adds conditional measures and derived-field diagnostics. The new
measure evaluator follows chosen-only Ite and complete Option traversal for
Boolean lists. The folding proof preserves full denotation and existing
lowering interpretations under explicit integer laws. Label maps, substitution,
sort preparation, onlyPoint, derived-type discovery, and diagnostic compilation
remain frontend bridges. Static missing-child scans include both Ite branches.
The derived-field precheck does not guarantee every named measure exists.

The full pinned audit passes 2,220 jobs and 54,792 dependency checks.
Only permitted foundations and the existing unused-input warning occur.
Seventy-four public axiom probes and 43 kernel examples pass.
Strict Nix build and all six suites pass: 755 examples plus golden.
Fourmolu passes eight changed Haskell files. Cabal-gild passes four packages.
Fifteen new modules, two notes, and three additive Audit imports preserve
every earlier non-Audit proof file. Upstream changes eleven existing files.

Read `lean/notes-current-memo-class-workers.md` and
`lean/notes-main-6baa0e25.md`. Next continue general Scan and outer constrained
completion, native allocation and checked semantic transfer, pending lazy
publication and GHC demand, literal HashMap iteration and allocation order,
import trim/DFS/SCC, whole enumeration and waiting counts, templates and typed
refinements, heterogeneous generators, decision-model, curried/GHC, synthesis,
normal forms, and every separate Sized contract. Keep the optimized interned
core and all older constructor and equality work.

Start: `/tmp/mcfta-memo-workers-checkpoint-20261016-0149/` (2,915 files).
Closing: `/tmp/mcfta-memo-target-workers-checkpoint-20261016-0213/` (2,932 files).
Script: `/tmp/mcfta-preserve-memo-target-workers-20261016.py`.
Evidence uses `/tmp/mcfta-memo-target-workers-*` and `/tmp/mcfta-measure-choice-*`.
Fourteen external drafts, stashes, and other worktrees remain. The last weekly
allowance was 81%; it is stale. Stop owned work at 1% or less. No board posts
or deployments. Push verified formalize checkpoints regularly. The full-library
goal stays active. HANDOFF.md records the per-command SSH port 443 fallback.

## Current executable memo merge and physical class entry

Audited source main is `4101746a`, merged at `0fca52f8`.
Proof commits are `d86eb552`, `4854718c`, `b990ff2d`, `2f2575ef`,
and `5cbb09b7`. Audit and notes are in `f1a27d46`.
Full library scope stays active. Earlier sections retain
their historical source definitions and proof boundaries.

The memo-aware merge now has an executable interpreter and both directions
of completed graph correspondence. Actual finite graphs derive sufficient
work and selection bounds. Every larger pair returns the same output,
heap, and completed merge table. A common bound follows from the local
selection receipts. Work fuel bounds interpreter depth, not total work.
The physical finite/cold endpoints derive their own actual call.
The same call supplies language coverage, producers, and global receipts.

Actual merge, target, leaf, edit, row, class, and pass graphs now preserve
normalized physical equality fields. No future field heap or old/new graph
equality is supplied. Unselected siblings can remain open.

`SourceCurrentMemoPhysicalClassPass.live_scan_pass` composes the live
physical entry, actual successful Scan, finite required execution, and one
finite memo-aware class pass under its reached range plan. The same pass
supplies readiness, costs, fields, stored merge records, producer histories,
selected domains, original/result availability, fourth-memo correctness,
ordered global receipts, and independent original-forest language bounds.
Only its completed merge table starts empty. Original constraint checks
remain necessary. Successful Scan and reached ranges remain premises.

The new conjunction emptiness proof derives literal tuple coverage, smaller
requirements, finite exploration, exact source Boolean growth, and fixed-point
soundness. Completed resident exposure, getPath readback, key faithfulness,
and actual IntMap/lazy-runtime correspondence remain adapters.
The new solver command model derives one scope declaration batch per process,
local cleanup, replacement redeclaration, and unchanged logical requests.
External SMT/process/bracket/IO behavior remains explicit.

The fit-ranking component proves preservation with complete score vectors
and no new fits for all vectors. Short vectors lose the unscored pool suffix.
Failure returns partition order. The recorded pool is an intended request,
not an IO receipt. A verified zero-timeout source probe makes no model call.
Score order/stability, Double laws, and server/timeout IO remain open.

The full pinned audit passes 2,206 jobs and 54,469 dependency checks.
Only permitted foundations and the existing unused-input warning occur.
Strict Nix build and all six suites pass: 749 examples plus golden.
Fourmolu passes eight changed Haskell files. Cabal-gild passes four packages.
Eleven new modules, two notes, and five additive Audit imports preserve every
earlier non-Audit proof file. Upstream changes twelve source/package files.

Read `lean/notes-current-memo-workers.md` and `lean/notes-main-4101746a.md`.
Next connect executable target, shared leaf, edit, and class workers to the
new memo-aware graphs. Continue general Scan/outer constrained completion,
whole-pass pending publication and GHC demand, checked allocation/native and
machine bridges, literal HashMap allocation order, import trim/DFS/SCC,
whole enumeration/waiting counts, templates/refinements, heterogeneous
generators, decision-model, curried/GHC, synthesis, normal forms, and all
distinct Sized contracts. Keep the optimized interned core and older proofs.

Start: `/tmp/mcfta-memo-shared-checkpoint-20261016-0128/` (2,901 files).
Closing: `/tmp/mcfta-memo-workers-checkpoint-20261016-0149/` (2,915 files).
Script: `/tmp/mcfta-preserve-memo-workers-20261016.py`.
Evidence and closing preservation use `/tmp/mcfta-memo-workers-*`,
`/tmp/mcfta-conjunction-emptiness-*`, `/tmp/mcfta-declare-once-*`, and
`/tmp/mcfta-ghc-ranking-*`. Fourteen external drafts, stashes, and other
worktrees remain. The last weekly allowance was 81%; it is stale. Stop owned
work at 1% or less. No board posts or deployments. Push verified formalize
checkpoints regularly. The full-library goal stays active.

## Current memo-aware shared class pass

Audited source main is `0696b48d`, merged at `f780009a`.
Proof commits are `24d8eb31`, `aa3e90c0`, `311cb8ac`, `3c1237be`,
`aa4cdd35`, `60ad3b5f`, and `9e59450c`. Full library scope stays active.
Earlier sections retain their historical proof and source scopes.

Shared target slots now retain actual memo-aware construction histories.
A hit reuses its exact stored value and full state. A miss executes the new
Target and stores its returned native state and completed merge table.
Actual leaves, signed edits, rows, and classes thread that same table.
The right fold captures each actual tail forest and table, then starts only
its class-local target slots empty. Unselected siblings can remain open.

`SourceCurrentMemoClassPassComplete.source_cold` composes one finite Pass
with physical readiness, stored costs and merge records, available results,
selected path domains, producer histories, independent language bounds,
and its exact ordered three-global-table receipt. The physical heap and
global tables can be warm. Only the completed merge table starts empty.
Guard laws, original selected domains, and actual-prefix range plans remain
explicit. Output terms belong to the input language. Input terms that
satisfy all retained original classes survive. The exact caller must still
check those original constraints.

Main adds preorder-prefix exclusion in three files. Its new monitor proof
establishes literal word-prefix rejection, strict active depth descent,
and unique ordered child boundaries. Minimal DAG extraction, endsOf/copies/
walk, and the source run-copy bijection remain open. The advertised template
equivalence needs valid partial preorders: the preserved malformed a0,b0
source example retains leaf a through the new route and removes it through
the template route. No source behavior was changed for this domain caveat.

The full pinned Lean build passes 2,195 jobs and 54,154 dependency checks.
Only permitted foundations and the existing unused-input warning occur.
Strict Nix validation passes all six suites: 745 examples plus golden.
Fourmolu passes both changed Haskell files. Cabal-gild passes four packages.
Seventeen new modules, two notes, and two additive Audit imports retain every
earlier non-Audit proof file. This refresh changes only the three upstream files.

Read `lean/notes-current-memo-shared-class-pass.md` and
`lean/notes-main-0696b48d.md`. Next connect executable memo-aware workers,
physical annotation fields, and the current Scan/required entry to this pass.
Continue general constrained completion, allocation/native/machine bridges,
whole-pass lazy publication and GHC demand, source group allocation order,
import trim/DFS/SCC, enumeration and waiting counts, templates/refinements,
heterogeneous generators, decision-model, curried/GHC, synthesis, normal
forms, and every distinct Sized contract. Keep the optimized interned core.

Start: `/tmp/mcfta-published-merge-checkpoint-20261016-0104/` (2,882 files).
Closing: `/tmp/mcfta-memo-shared-checkpoint-20261016-0128/` (2,901 files).
Script: `/tmp/mcfta-preserve-memo-shared-20261016.py`.
Evidence: `/tmp/mcfta-memo-shared-*` and `/tmp/mcfta-prefix-exclusion-*`.
All prior proofs, repros, repairs, 14 external drafts, stashes, and other
worktrees remain. The last weekly allowance was 81%; it is stale. Stop
owned work at 1% or less. No board posts or deployments. Push verified
formalize checkpoints regularly. The full-library goal stays active.

## Current serial publication and memo-aware targets

Source main remains `a4dd678f`, merged at `1a421c7d`. Proof commits are
`5662dbad`, `c6f18d2a`, `8ec392bc`, `f90e201d`, and `e93d0190`.
Full library scope stays active. Earlier sections keep their historical scope.

The new serial graph publishes a captured producer before its body runs.
Completed maps are proof state for thunk evaluation, not another production
cache. Actual request bounds derive strict ordinary-height descent and
exclude running ancestor keys by resident identity. Finite public endpoints
take no ancestor-exclusion, future-validity, or winner-equality premise.
The actual completed body leaves its parent lookup unchanged. An absent
parent stays absent, so an actual miss returns its computed candidate.

Lifting and projection retain the same output, constructor heap, and completed
memo. Warm captured-record, completed-key, and cache-coverage invariants remain
explicit. Empty tables derive them. PublishedComplete.native_cold composes
one finite early-publication history with native state, independent language,
producer history, and its exact three-global-table receipts. Tickets are
abstract labels. Concurrent forcing, runtime identities, actual GHC demand,
and host cache operations remain open.

The new native merge retains native tables and domains. Selected operands
project the captured original forest, then call that merge. They allow open
unrelated siblings. The new first-seeded target fold threads its actual
returned merge table through operands and native intersections. It derives
readiness, costs, physical entries, common selected-subterm coverage, and
ordered receipts for that same trace. Multiple native intersections can
populate native tables. Finite targets still assume actual-prefix word-range
plans. Original constraint checks remain necessary for the exact caller.

The literal singleton-map insertion fold now derives ordered bucket contents.
Unique emitted keys and exact lookup membership derive the canonical-group
permutation. Actual HashMap iteration still needs that finite-map contract.
The recursive body still uses canonical outer groups. No equal-heap or
allocation-order theorem follows from a group permutation.

The full pinned Lean build passes 2,178 jobs and 53,977 dependency checks.
Only permitted foundations and the existing unused-input warning occur.
Eleven new modules and four additive Audit imports retain every earlier
non-Audit proof file. Haskell and CI are unchanged. The source-refresh strict
Nix build, 743 examples plus golden, Fourmolu, and Cabal-gild checks remain
valid. They were not repeated for these proof-only changes.

Read `lean/notes-current-published-merge.md`. Next thread this merge table
through shared target closures, leaves, edits, and the full class pass.
Continue general Scan/outer completion, allocation and checked native transfer,
machine bounds, import trim/DFS/SCC, enumeration and waiting counts, templates,
typed refinements, heterogeneous generators, decision-model, curried/GHC,
state search, normal forms, and all distinct Sized contracts. Keep the
optimized interned core and older constructor and equality work.

Start: `/tmp/mcfta-memo-aware-checkpoint-20261016-0045/` (2,870 files).
Closing: `/tmp/mcfta-published-merge-checkpoint-20261016-0104/` (2,882 files).
Script: `/tmp/mcfta-preserve-published-merge-20261016.py`.
Evidence: `/tmp/mcfta-published-merge-*`, `/tmp/mcfta-memo-merge-*`,
`/tmp/mcfta-memo-target-*`, `/tmp/mcfta-memo-demand-target-*`, and
`/tmp/mcfta-current-merge-grouping-*`. All previous proofs, repros, repairs,
14 external drafts, stashes, and other worktrees remain. The last weekly
allowance was 81%; it is stale. Stop owned work at 1% or less. No board posts
or deployments. Push verified formalize checkpoints. The full goal stays active.

## Current recursive memo-aware merge completion

Source main remains `a4dd678f`, merged at `1a421c7d`. Proof commits are
`72df670f`, `85c424ea`, `dda75cf4`, and `4514b014`. Full library scope stays
active. Earlier sections retain their historical proof and source scopes.

The new mutual instruction and call graphs use literal result-cache requests
for every recursive small child and retained ordinary union. Hits skip the
body. Misses execute the memo-aware body and reread the first stored winner.
Actual induction derives physical effects, available results, conditional
closedness, independent language coverage, and ordered global memo receipts.
Warm result tables require initial stored-record and coverage invariants.
Empty result tables derive both invariants and actual producer histories.

Finite completion uses strict ordinary-height descent of request inputs
before lookup. Cached result height needs no bound. Each actual selection
has its own finite comparison bound. No recursive callback completion law,
future validity, old uncached producer, or whole-forest closedness is supplied.
`SourceCurrentMemoMergeComplete.source_cold` fixes the current plain/Top
guards. One actual finite call supplies the language result, physical state,
stored original producer, and coherent final three-table receipt. The initial
physical heap can be warm. Guard interpretation laws remain explicit.

The body uses canonical source groups. Literal HashMap outer iteration and
allocation order still need an adapter. Completed sequential calls do not
prove lazy thunk publication, pending ancestor forcing, concurrency, or GHC
correspondence. Existing shared targets and class passes still use the older
body boundary. Their receipts must be connected to the new requests.

The full pinned Lean build passes 2,167 jobs and 53,797 dependency checks.
Only the three permitted foundations and the existing unused-input warning
occur. Nine new modules and one additive Audit import preserve all earlier
non-Audit proof files. Haskell and CI are unchanged. The strict Nix build,
six suites with 743 examples plus golden, Fourmolu, and Cabal-gild results
from the source refresh remain valid and were not repeated.

Read `lean/notes-current-memo-aware-merge.md`. Continue publication/forcing
and memo-aware target integration, general Scan/outer completion, allocation
history and checked native transfer, machine bounds, import trim/DFS/SCC,
whole enumeration, waiting counts, templates, typed refinements, heterogeneous
generators, decision-model, curried/GHC adequacy, state search, normal forms,
and all distinct Sized contracts. Keep the optimized interned core and all
older constructor and equality work.

Start: `/tmp/mcfta-class-language-checkpoint-20261016-0019/` (2,860 files).
Closing: `/tmp/mcfta-memo-aware-checkpoint-20261016-0045/` (2,870 files).
Script: `/tmp/mcfta-preserve-memo-aware-20261016.py`.
Evidence: `/tmp/mcfta-memo-aware-*`, `/tmp/mcfta-memo-merge-*`, and
`/tmp/mcfta-current-memo-merge-*`. All earlier proofs, repros, repairs,
13 prior external drafts, stashes, and other worktrees remain. One new marked
optional proof draft is also retained. The last weekly allowance was 81%;
that value is stale. Stop owned work at 1% or less. No board posts or
deployments. Push verified formalize checkpoints. The full goal stays active.

## Current class-pass language, physical heaps, and actual global memos

Source main `a4dd678f` is merged at `1a421c7d`. Proof commits are
`a6137293`, `d5059da3`, `58bdb112`, `785fabb0`, and `4fff37a2`.
Full library scope stays active. Older sections retain their historical
source and proof scopes.

The actual shared class pass now derives independent language bounds with
open unrelated siblings. Output terms belong to the input language.
Accepted terms that satisfy all retained original classes survive.
Nontrivial class satisfaction derives required term path existence.
This is conditional exactness. Narrowing alone need not enforce each class.
Original constraint checks remain part of the exact caller.

Actual shared targets, first forces, stored hits, leaves, edits, right folds,
and final propagation now retain stored costs and physical annotations.
Ordered actual global receipts derive all three final tables' validity,
retain earlier unfolding entries, and preserve the scan-final query tables
through required and class execution. Each head captures the actual tail's
forest and returned memo bundle. No future coherence or whole-forest
closedness is supplied. CostHeap is a stored cost invariant, not wall time.

`SourceCurrentPhysicalClassPassLanguage.live_scan_pass` composes computed
physical entry, actual successful Scan, finite required execution, and a
range-checked finite class Pass. The same returned Pass has literal StableRun,
final IdleReady, CostHeap, FieldHeap, original/result availability, retained
entries, fourth emptiness-memo correctness, all selected path domains,
independent language bounds, and its exact final three-table receipt.
Successful Scan and reached range checks remain premises. General current
Scan and outer constrained caller completion remain open. The existing
scoped native state still needs checked allocation/runtime transfer.

The separate merge-result memo now has completed hit/miss provenance,
resident results, retained entries, global effects, and language coverage.
An independent publication graph follows lookup, first-writer thunk insert,
and winner reread. Publication-to-completion/GHC forcing and recursive
memo-aware merge bodies remain open. Target receipts still use the existing
body graph; a cache hit is not a new body execution.

Upstream adds state-based synthesis, automaton enumeration per size, caller
fit deduplication, explicit outcomes, and shared normal-form work fuel.
New source components prove exact positive size compositions, retained split
size/length/accounting, strict child-size descent, shared quotation budget
accounting and sequencing, beta-loop rejection, and the separate output-size
check. Complete argument partitions, host refinement, cached state builds,
automaton/search, Core/value exposure, and current Walk/Fits runtime remain.
The equality/Sized/import/interned source bodies and local repair are unchanged.

The aggregate audit passes 2,158 jobs and 53,642 dependency checks with
only permitted foundations and no new warning. Eleven new modules and four
additive Audit imports retain every earlier non-Audit proof file. Required
strict Nix build and all six suites pass 743 examples plus the golden check.
Fourmolu passes nine changed Haskell files; Cabal-gild passes four packages.
The source delta is exactly the 13-file upstream merge.

Read `lean/notes-current-class-pass-language.md`,
`lean/notes-current-merge-result-memo.md`, and `lean/notes-main-a4dd678f.md`.

Next derive actual memo-aware recursive merge requests and connect published
thunks to completed producers. Continue general Scan/outer completion,
allocation history and checked native transfer, machine bounds, import
trim/DFS/SCC and language/run bridges, whole enumeration, waiting counts,
template exclusion, typed refinements, heterogeneous generators and
decision-model, curried/GHC adequacy, state search and all distinct Sized
contracts. Keep the optimized interned core and older constructor/equality work.

Start: `/tmp/mcfta-shared-paths-checkpoint-20261015-2354/` (2,843 files).
Closing: `/tmp/mcfta-class-language-checkpoint-20261016-0019/` (2,860 files).
Script: `/tmp/mcfta-preserve-class-language-20261016.py`.
Evidence: `/tmp/mcfta-class-language-*` plus the physical class pass, heap,
class memo, merge-result memo and normal-form budget validation notes.
All previous proofs, repros, repairs, 13 external drafts, stashes and other
worktrees remain. The last observed weekly allowance was 81%; it is not a
fresh reading. Stop owned work at 1% or less. No board posts or deployments.
Push verified formalize checkpoints. The full-library goal remains active.

## Current finite shared class pass and actual merge memo effects

Source main remains `45d6538c`, merged at `0694b6f9`. Proof commits are
`22a33ecf`, `284e05ef`, `8b6f9a22`, `b3498f92`, and `3deb645f`.
This checkpoint changes no Haskell or CI file. Full library scope stays active.
Earlier sections retain their historical source and proof scopes.

Shared targets now complete from selected ForestClosed path domains, while
unrelated captured siblings can remain open. Actual projection derives closed
merge operands. Actual target, fold, stored receipt, first force, and hit reuse
retain the existing source graphs and full native state.

The actual edit compiler derives populated child subtrees. Actual shared
node/child/row edits preserve every arbitrary tracked signed path domain.
Original class domains derive safe recursive-prefix reads and concrete native
leaves. Range plans derive finite class execution and literal-worker StableRun.
The actual right fold derives each head's captured domains from the actual
tail output. Final empty propagation retains all tracked domains.

live_scan_pass composes computed live physical entry, an actual successful
Scan, finite exact requireAll, retained original records, and a finite class
Pass under the existing reached-prefix word-range plan. Final native readiness,
retained entries, available output, fourth emptiness-memo correctness, and
EVERY selected path domain follow. This theorem assumes successful Scan and
word-range checks. It does not prove the whole outer caller or fixpoint.
Its exact language, cost/field facts, and global call receipts stop at required
execution. The source graph still uses the existing scoped native state;
transfer to the newer checked allocation state and GHC demand remains open.

Actual comparison, child selection, and general merging now retain stored
cost and physical annotation invariants on available open or closed inputs.
The separate global memo proofs derive ordered exposure and constructor
receipts through the complete merge body. All three final tables are valid;
old unfolding entries remain and both query tables are unchanged. Literal
constructor Work has a checked silent primitive trace. Native Merge receipts
retain the exact returned state and unchanged native tables/domains.
The separate genericMergeAlternativesCache hit/miss/publication model remains
open. Completed merge-worker execution remains a premise of its effects.

Next prove independent language bounds for the new open-sibling class pass.
Use actual target inclusion and shared leaf semantics. Compose all actual
global memos, cost/field effects and separate merge-result memo through target
forcing, class edits and the full current caller. Continue actual allocation
history and checked native/runtime transfer, machine bounds, general current
Scan/outer completion, import trim/DFS/SCC and language/run bridges, whole
enumeration, waiting counts, full template exclusion, typed refinements,
broader generators and decision-model, curried/GHC adequacy, and all distinct
Sized contracts. Keep the optimized interned core and older constructor work.

The full audit passes 2,147 jobs and 53,338 dependency checks with only the
permitted foundations and no new warning. Ten new modules and two additive
Audit imports preserve every older non-Audit proof file. Current-source strict
Nix build, six suites (736 examples plus golden), Fourmolu and Cabal-gild
results remain valid. They were not repeated for this proof-only increment.

Read `lean/notes-current-shared-paths.md`,
`lean/notes-current-merge-effects.md`, and `lean/notes-current-merge-memos.md`.

Start: `/tmp/mcfta-required-endpoints-checkpoint-20261015-2337/` (2,830 files).
Closing: `/tmp/mcfta-shared-paths-checkpoint-20261015-2354/` (2,843 files).
Script: `/tmp/mcfta-preserve-shared-paths-20261015.py`.
Evidence: `/tmp/mcfta-shared-paths-*` and the target, class-edit, class-fold,
merged-cost and merged-query-memos validation notes in /tmp. All prior proofs,
repros, repairs, 13 external drafts, stashes, and other worktrees remain.
Weekly allowance was 81% at the source refresh. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Current required endpoints, physical effects, and global memo composition

Main `45d6538c` is merged at `0694b6f9`. Proof commits are `168ef9ed`,
`c10e6b1c`, `168802b3`, and `82144334`. Full library scope stays active.
Earlier sections retain their historical source and proof scopes.

Actual requireAll now retains the projection domain of EVERY original
selected path, including shorter nonmaximal paths and terminal suffixes.
The proof uses full original primary certificates and actual demanded child
lookups. It does not infer original whole-Mu closedness from a false gate.
Unselected siblings can remain open. Path safety does not imply existence
of a missing root position; accepted original path witnesses remain separate.

Actual completed required graphs now derive semantic readiness, retained
entries, stored cost and physical annotation invariants, available results,
and ordered global memo receipts. The final three tables are valid. Earlier
scan-final unfolding entries remain. Query tables are unchanged. The fourth
emptiness memo remains correct through constructor retention.
scan_required_ready composes these effects with an actual successful Scan,
finite exact requireAll, every selected endpoint domain, and native IdleReady
using advanceHeap. Native warm tables are retained. General Scan and outer
caller completion are not consequences of a supplied successful trace.

Next carry the required result domains through actual shared targets and
class edits with open unselected siblings. Continue fallback merge/subsumes
reads, separate merge memo and physical effects, full current caller and
constrained completion, actual allocation history and checked native/runtime
transfer, word bounds, whole enumeration, representative waiting counts,
whole template exclusion, typed refinement frontends, broader generators,
decision-model, curried/GHC adequacy, and every distinct Sized contract.
Keep the optimized interned core and all older constructor/equality proofs.
The fromRows trim/DFS/SCC, constructor, imported-language, and runtime bridges
remain open. The new endpoint theorem does not close later edit preservation.

Upstream adds child root-shape pruning to template edge copies and changes
CI scheduling. SourceTemplateShapeSplits proves the exact ordered filtered
split list, accepted-child preservation, and impossible killed-part removal.
The full exclusion pipeline and physical inventory bridge remain open.
Equality, Sized, import, GHC, and curried production bodies are unchanged.

The full audit passes 2,137 jobs and 53,195 dependency checks with only the
permitted foundations and no new warning. Six new modules and two additive
Audit imports preserve every older non-Audit proof file. The strict Nix
build and six suites pass 736 examples plus the golden check. Fourmolu passes
the two changed Haskell files. Cabal-gild passes all four active packages.
The Haskell and CI delta is exactly the upstream merge. The local equality
repair is unchanged.

Read `lean/notes-current-required-endpoints.md`,
`lean/notes-current-required-memos.md`, and `lean/notes-main-45d6538c.md`.

Start: `/tmp/mcfta-required-language-checkpoint-20261015-2322/` (2,821 files).
Closing: `/tmp/mcfta-required-endpoints-checkpoint-20261015-2337/` (2,830 files).
Script: `/tmp/mcfta-preserve-required-endpoints-20261015.py`.
Evidence: `/tmp/mcfta-required-endpoints-*`. All prior proofs, repros,
repairs, 13 marked external drafts, stashes, and other worktrees remain.
Weekly allowance was 81% at the source refresh. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Exact current scan/required composition and reconstructed result domains

Main `9a2f9bea` is merged at `d8beb7f5`. Proofs are `b0725b6f`,
`bfccb6cb`, `5fc66c36`, `3bf2b23c`, and `f5a95755`. Full library scope
stays active. Earlier sections retain historical source and proof scopes.

Actual primary replay now retains every selected original class at the
same actual scan-final heap. The canonical selected path union derives
its original-child required domain. The literal requireAll worker has
finite stable execution and exact independent conditional filter language.
Original accepted forests with the original class paths are retained.
Unselected original siblings can remain open.

All maximal tips, including terminal suffixes, retain original endpoint
certificates. Actual required-node, child, and row graphs derive structural
output domains. New open ordinary records need no residency in the earlier
gate heap. Every proper maximal output tip has the existing closed-path
projection domain. scan_required_complete composes all these results from
an actual successful current Scan. Scan memo, cost, and field invariants
still end at its scan heap. The later required/fallback effects remain open.

Next retain original selected paths that stop being maximal when another
path extends them. The structural tip domain alone does not imply their
shorter endpoint closedness. Use actual original endpoint certificates and
conditional closed-node preservation. Then carry these domains through
shared targets and class edits. Continue the full current caller, required/
fallback merge and subsumes memos, costs/fields, actual allocation history,
checked native/runtime transfer, word bounds, general constrained completion,
whole enumeration, representative waiting counts, templates, typed refinement
frontends, heterogeneous generators, decision-model, and every distinct
Sized contract. Keep the optimized interned core and all older proofs.

Upstream adds curried synthesis, type-variable domains/defaulting, a run-edge
narrowing hook, and typed-run counters. New source models prove physical
marker filtering after weighted lookup, exact optional program occurrences,
first-occurrence deduplication, Walk marker packing and next-program tails.
Complete curried typing, GHC erasure/instance/domain/defaulting adequacy,
whole Walk/enumerator scheduling, demand, and machine counters remain open.
The current fromRows schedule proof retains its separate trim/DFS/SCC,
constructor, language/run, physical sharing, capacity, and runtime boundaries.

The aggregate audit passes 2,131 jobs and 53,126 dependency checks with only
the permitted Lean foundations and no new warning. Eleven new modules and
three additive Audit imports preserve every older non-Audit proof file.
Required strict Nix build and all six suites pass 735 examples plus the
golden check. Fourmolu passes all 13 changed Haskell files. Cabal-gild passes
all four active packages. Haskell changes are exactly the upstream merge;
the previous equality repair remains intact.

Read `lean/notes-current-required-language.md`,
`lean/notes-current-required-results.md`, and `lean/notes-main-9a2f9bea.md`.
The prior Sized, allocation-history, and ordered-import notes remain relevant.

Start: `/tmp/mcfta-required-support-checkpoint-20261015-2257/` (2,807 files).
Closing: `/tmp/mcfta-required-language-checkpoint-20261015-2322/` (2,821 files).
Script: `/tmp/mcfta-preserve-required-language-20261015.py`.
Evidence: `/tmp/mcfta-required-language-*`. All prior proofs, repros,
repairs, 13 marked external drafts, stashes, and other worktrees remain.
Weekly allowance is 81%. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Open required-path completion and ordered source import

Main `5c53de80` is merged at `ea7d8b05`. Proofs are `676fd247`,
`68eebcb8`, `fff6ef45`, `63598858`, and `e89aa110`. Full library scope
stays active. Earlier sections retain historical source and proof scopes.

One causal constructor/interleave history now derives original field
origins, final interner validity, and valid cold operation tables. Actual
GHC history, initial validity, and literal coverage remain explicit.

Maximal tips of the actual Needed trie derive path-local required domains.
Actual false primary ClassTrace derives that domain and finite StableRun
of the existing requireAll worker. Unselected original siblings can remain
open. No completed callback, whole-forest closedness, result Support, or
future validity is supplied. Head language is exact. Whole-worker filter
language, common scan-final support for all selected classes, rebuilt/output
support, later class edits, global memo effects, costs, and fields remain.

Source fromRows now uses ordered binder contexts and one post-body memo.
New proofs cover exact dispatch, ordered rows/children, old-entry retention,
a finite key inventory, and a real same-component rank. A combined component/
context rank derives finite Build/root schedules from finite positional
child closure and strict cross-component height descent. Actual trim/DFS/SCC
readback and height derivation, constructor semantics, complete imported
language/runs, physical sharing/counts, capacity, and GHC demand remain.
Old induced-cycle BinderSchedule/BinderCycles correspondence is historical.

Next prove the new required-worker language and combine selected primary
receipts at the actual scan-final anchor. Then retain path-local support
through shared targets and edits. Continue actual allocation provenance,
full caller branches, fallback merge/subsumes memos, checked native/runtime
transfer, word bounds, general completion, whole enumeration, waiting counts,
templates, typed refinements, broader APIs, and every distinct Sized contract.
Keep the optimized interned core and every older constructor/equality proof.

The aggregate audit passes 2,120 jobs and 52,960 dependency checks with only
the permitted Lean foundations and no new warning. Six new modules and
three additive Audit imports preserve every older non-Audit proof file.
Required strict Nix build and six suites pass 724 examples plus golden
checks. Fourmolu passes all four changed Haskell files; all Cabal-gild checks
pass. GHC production normal-key filtering and Sized bodies are unchanged.

Read `lean/notes-original-allocation-history.md`,
`lean/notes-current-required-support.md`, and `lean/notes-main-5c53de80.md`.

Start: `/tmp/mcfta-normal-form-checkpoint-20261015-2242/` (2,798 files).
Closing: `/tmp/mcfta-required-support-checkpoint-20261015-2257/` (2,807 files).
Script: `/tmp/mcfta-preserve-required-support-20261015.py`.
Evidence: `/tmp/mcfta-required-support-*`. All prior proofs, repros,
repairs, 13 marked external drafts, stashes, and other worktrees remain.
Weekly allowance is 82%. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Original allocation origins, primary support, and GHC fit filtering

Source main `e16f3b50` is merged at `50f21a5f`. Proof commits are
`2aab2f05`, `8ba5ad13`, and `e3be9dd6`. Full library scope stays active.
Earlier sections retain historical source and proof scopes.

Earlier literal equality constructors and retained canonical table entries
now derive read-only field lookup for EVERY resident original edge after
actual graph construction. Current cold entry derives ready loaded fields
and exact original readback. The scan soundness interface first supplies
that loaded value; it no longer assumes successful lookup. Actual GHC
construction must still supply the earlier allocation inventory. Valid
operation tables, ready inherited storage, actual live prefix, and completed
Scan remain explicit. No field is allocated at the request site.

Actual false primary node/path/class traces now derive projection support
at their exact returned heaps. This conversion adds no source gate or memo
call. Unrelated original siblings can remain open. Support through requireAll,
rebuilt class forests, shared targets, and edits remains open.

The GHC source adds normal-key fit filtering. Its new completed-fit model
checks seen insertion BEFORE part checks/callbacks, duplicate skip, unknown
keys, callback stop/suffix, merge accounting, quota, and stable output order.
It does not prove Core normalization, whole Walk/GHC execution, or Haskell
contextual equality. Pair eta has a documented partial-value exception;
sizeAtMost 20000 is no reduction-fuel or termination bound.

Next derive synchronized physical original-allocation history and compose
the full current caller. Retain scan-final original children/selected records
and path-local open-sibling fallback support. Merge/subsumes global reads,
separate merge memo, costs/fields, checked native/word/runtime transfer,
general completion, whole enumeration, waiting counts, templates, typed
refinements, broader APIs, and all distinct Sized contracts remain open.

The aggregate audit passes 2,114 jobs and 52,819 dependency checks with only
the permitted Lean foundations and no new warning. Four new modules and
three additive Audit imports preserve every older non-Audit proof file.
Required strict Nix build and all six suites pass 723 examples plus golden
checks. Changed-file Fourmolu and all four active Cabal-gild checks pass.

Read `lean/notes-original-field-origins.md`,
`lean/notes-current-primary-support.md`, and `lean/notes-main-e16f3b50.md`.

Start: `/tmp/mcfta-physical-entry-checkpoint-20261015-2225/` (2,790 files).
Closing: `/tmp/mcfta-normal-form-checkpoint-20261015-2242/` (2,798 files).
Script: `/tmp/mcfta-preserve-normal-form-20261015.py`.
Evidence: `/tmp/mcfta-normal-form-*`. All prior proofs, repros, repairs,
13 marked external drafts, stashes, and other worktrees remain.
Weekly allowance is 82%. Stop owned work at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Physical accessor and original cold scan entry

Source main remains `2ca1644c`. Proofs `dae67292`, `a5b760f1`, and `abe70af7`
derive computed physical accessor records, actual allocated precheck entry,
and original construction invariants. A public accepted original edge
cannot reach rejection through the actual completed cold Scan. Input
language translation and original class satisfaction are derived. Exact
selected-position receipts retain original Record fields for fallback.
Read `lean/notes-current-physical-entry.md`.

Normalized original fields do not establish equality-interner coverage.
Successful read-only lookup, operation validity, ready inherited storage,
the live precheck, and completed Scan remain explicit. The operation-state
result ends at the prefix. Earlier contradiction and later fallback are
outside the cold scan theorem. Do not allocate missing fields at lookup.

Next derive synchronized original equality-field allocation coverage and
compose the complete caller. The current fallback permits unrelated open
siblings, while existing required/edit/Pass proofs require closed forests.
Derive path-local support through rebuilt forests. Merge/subsumes row reads
also need actual unfolding/global memo receipts. Keep all broader runtime,
completion, enumeration, template, typed refinement, and distinct Sized
obligations. Full library scope stays active.

The full audit passes 2,110 jobs and 52,720 dependency checks, permitted
axioms only, no new warning. Five new modules and two additive Audit imports
preserve older definitions. Haskell package trees are unchanged; preceding
required Nix/format checks passed 720 examples plus golden and are not
repeated. The closing snapshot has 2,790 files at
`/tmp/mcfta-physical-entry-checkpoint-20261015-2225/`. All prior proofs,
repros, repairs, drafts, stashes, and worktrees remain. Earlier sections
retain historical source and proof scopes.

## Global memo composition at normalized current entry

Main `2ca1644c` is merged at `a7134ecb`. Proofs `36545747`, `143985fb`,
`0845cfa6`, and `37efaa55` compose the SAME three global gate tables through
actual folds, delayed tasks, current Decision, fourth-memo calls, and the
reached current Scan. Initial invariants derive ordered call receipts and
final memo/heap coherence. No accepted term or future-state invariant is
supplied. Cached equality readback and the actual live precheck derive the
proper-path domain. Physical accessor extraction and caller initialization
remain explicit. Read `lean/notes-query-global-memos.md`.

Current enumeration storage/order adapters derive allocated-prefix map/list
correspondence and root-map/fallback closure laws. Out-of-range map insertion
does not equal an old out-of-range list update. Actual canonicalClasses,
sortOn/Double ordering, physical containers, capacity, whole scheduling, and
representative waiting counts remain separate bridges. Grouped edgeCopies
exclusion and typed derived refinements remain uncovered. The source removes
deriveNode TODO prose; it adds no implementation. Read
`lean/notes-main-2ca1644c.md`.

Next connect physical equality records and initial caller construction, then
the selected required-path/class-reduction/empty-propagation fallback.
General recursive completion, GHC demand/publication, checked native state,
word bounds, whole enumeration, broader APIs, and all distinct exact Sized
contracts remain. Full library scope stays active.

The full audit passes 2,105 jobs and 52,700 dependency checks with permitted
axioms only and no new warning. Required Nix checks pass all six suites,
720 examples plus golden. Formatting passes. Eight new modules and four
additive Audit imports preserve all older proof definitions. The closing
2,784-file snapshot is `/tmp/mcfta-query-global-checkpoint-20261015-2208/`.
All prior proofs, counterexamples, repairs, drafts, stashes, and worktrees
remain. Earlier sections retain their historical source and proof scopes.

Updated: **2026-10-15 21:48 CEST (Europe/Stockholm)**.

## Current secondary, fourth-memo scan, and main 7fdebd07

Main `7fdebd07` is merged at `a3e68610`. Proofs are `0992b336`,
`3e797a74`, and `3be3967c`. Read `lean/notes-current-secondary.md` and
`lean/notes-main-7fdebd07.md` first. Full scope stays active. Earlier
sections retain historical source and proof scopes.

Complete current secondary graphs now have exact finite execution,
returned-heap replay, ranked stable completion, effects, and actual gate
memo receipts. Selected projection derives finite closed output without
closing unrelated original siblings. Actual Fold/Seeded queries, current
Decision, and fourth-memo hits/misses derive query invariants and original
class refutation. The current reached Scan retains that memo. Independent
accepted candidates satisfying all original active classes cannot reach
rejection. Live precheck derives ordered activity and accessor refutation.
Physical record extraction and initial caller construction remain explicit.

Next compose the SAME three global gate tables through actual Fold/Seeded,
delayed Force/Expose/Run/Decision, the fourth memo, and current Scan. Use
existing actual projection/native receipts and anchored support. Derive
coherence at each call. Do not assume future validity or memo-call silence.
Then connect physical caller entry and selected requireAll/class reduction/
empty propagation. Keep general completion, GHC demand/publication, checked
state, word bounds, whole enumeration, shared reaches-helper effects,
waiting counts, template exclusion, broader APIs, and all Sized boundaries.

The source adds typed NodeView/MeasureRecord refinement names and two
exposed Internal backends. Its typed public translation remains uncovered.
Constructor count/order and field kinds are checked; names are not compared.
Generic and custom instance laws, Expr/Integer agreement, errors, and exact
resulting languages/ranks need source bridges. Core gate/Sized bodies stay.

Full audit passes 2,097 jobs and 52,633 dependency checks with permitted
axioms only and no new warning. Nineteen new modules, two additive Audit
imports; older proof files remain. Required strict Nix build and all six
suites pass 714 examples plus golden. Changed-file Fourmolu and active
Cabal-gild pass. Start: `/tmp/mcfta-main-889-checkpoint-20261015-2122/`
(2,751 files). Closing: `/tmp/mcfta-current-secondary-checkpoint-20261015-2148/` (2,774 files).
Script: `/tmp/mcfta-preserve-current-secondary-20261015.py`.
All prior artifacts remain. Weekly allowance is 83%. Stop at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Current main 88998669 and retargeted source rules

Main `88998669` is merged at `6d1462c7`. Proofs are `a9eea20e`,
`86f70026`, and `60c96c89`. Read `lean/notes-main-88998669.md`.
Full scope stays active. Older source descriptions below are historical.

The current primary gate retains the exact old outcome and heap. The
secondary gate now admits a closed constrained Mu at the exact endpoint.
Its actual predicate-only receipt is proved. Selected closed one-index
endpoints derive projection support and actual true-query refutation,
without closing unrelated siblings. The old disabled/free-worker equation
does not hold at this endpoint. General current secondary trace transfer
and current Scan composition remain open.

Current emptiness follows the initial free guard and open-requirement rule.
Actual completed rows derive fixed-point compatibility. True body results
derive closedness and exclusion. A distinct fourth completed memo retains
conservative answers. Actual ordered pruning preserves language, with exact
source errors and suspended constraints. The reaches guard is still pure
in that graph; shared helper memo effects and whole enumerator wiring remain.

matchesNowhere has exact independent subterm-path semantics. Full exclusion
construction, unambiguity, finite obligations, fromRows/SCC, and preorderPrefix
remain open. The older native event proofs and unchanged source components
remain available. All broader runtime/completion/caller/Sized obligations stay.

Full audit: 2,078 jobs, 52,456 dependencies, permitted axioms only, no new
warning. Eight new modules and three additive Audit imports. Older Lean
definitions remain unchanged. Required strict Nix build and six suites pass
713 examples plus golden. Changed-file Fourmolu and active Cabal-gild pass.
Start: `/tmp/mcfta-native-events-checkpoint-20261015-2105/` (2,742 files).
Closing: `/tmp/mcfta-main-889-checkpoint-20261015-2122/` (2,751 files).
Script: `/tmp/mcfta-preserve-main-889-20261015.py`.
All prior artifacts remain. Weekly allowance is 84%. Stop at 1% or less.
No board posts or deployments. Push verified formalize checkpoints.

## Native instruction unfolding-event transfer

Proof checkpoint `97c525f4`, source main `525d722e`. Read
`lean/notes-source-native-events.md`. Full scope stays active.
Earlier sections retain historical checkpoint scope.

Actual typed primitives include a real unfolding-memo operation. A memo hit
still emits a global event. Actual Runs and absence of such events derive
table retention. Expanded Work, fresh constructor requests, and fixed native
callbacks derive these facts without opaque old-outcome adapters.
Native step/execute retain original fuel, continuations, heaps, memo cells,
and every bounded outcome. The event transfer has no availability, future
validity, or successful-completion premise. Scoped native requests derive
actual silent receipts and same-table coherence for all three gate tables.

This establishes the missing resident-instruction event transfer. It does
not establish GHC delayed producer forcing, row-spine sharing, original
child demand, global publication, or predicate/descendant helper-call
silence. Substitution-plan/per-binder caches remain distinct. Next compose
actual receipts through Fold/Seeded, delayed exploration/Decision, and Scan,
using anchored support without whole-original-forest closedness. Concrete
entry, selected fallback, checked state, machine bounds, general completion,
waiting counts, template exclusion, broader APIs/runtime, and distinct Sized
contracts remain open.

Full audit: 2,070 jobs, 52,331 dependency checks, permitted axioms only,
no new warning. Five new modules and one additive Audit import. Older
proof definitions and all four Haskell package trees match `1a8d5db0`.
Unchanged Haskell checks were not repeated.
Start: `/tmp/mcfta-query-memo-checkpoint-20261015-2043/` (2,736 files).
Closing: `/tmp/mcfta-native-events-checkpoint-20261015-2105/` (2,742 files).
Script: `/tmp/mcfta-preserve-native-events-20261015.py`.
All prior artifacts remain. Weekly allowance is 85%. Stop owned work at
1% or less. No board posts or deployments. Push verified formalize checkpoints.

## Actual projection memo receipts and ordered entry

Proof checkpoint `60a8d3eb`, source main `525d722e`. Read
`lean/notes-source-query-memos.md`. Full scope stays active.
Earlier sections retain historical checkpoint scope.

Actual exposure and completed projection graphs now derive ordered global
unfolding receipts, final memo coherence, and old-entry retention. Both query
tables stay unchanged, with coherence derived through actual heap histories.
The exact first Mu call and original-root fallback remain. All three tables
now pass through plain scoped Operand. No final validity is assumed.
These conditional projection effects do not cover every deferred open union.

The exact successful Precheck result derives ordered Active classes and
accessor satisfaction from coherent original records and cached equality
readback. Scan refutation now discharges activity and refutes that accessor.
Native record/trie extraction remains explicit.

Source review confirms that stored-body intersection and fixed callbacks
make no direct global unfoldOuterRec call on completed resident operands.
No existing Code-to-global-event transfer proves native silence. Delayed
Haskell operand/child producers can run those calls when forced by native
keys or constructors. Instrument the actual instructions before composing
native/query/Scan memo receipts. Keep this demand boundary and the distinct
substitution-plan/per-binder memos. Concrete entry, selected fallback,
checked state, machine bounds, general completion, waiting counts, template
exclusion, broader APIs/runtime, and separate Sized contracts remain open.

Full audit: 2,065 jobs, 52,088 dependency checks, permitted axioms only,
no new warning. Five new modules and two additive Audit imports. Older proof
definitions and all four Haskell package trees match `11fb07a1` unchanged.
Start: `/tmp/mcfta-lazy-prefix-checkpoint-20261015-2030/` (2,730 files).
Closing: `/tmp/mcfta-query-memo-checkpoint-20261015-2043/` (2,736 files).
Script: `/tmp/mcfta-preserve-query-memo-20261015.py`.
All prior artifacts remain. Weekly allowance is 85%. No unchanged Haskell
checks were repeated.

## Sound early rejection through reached original classes

Proof checkpoint `3ca8c0c4`, source main `525d722e`. Read
`lean/notes-source-lazy-class-prefix.md`. Full scope stays active.
Earlier sections retain historical checkpoint scope.

The current-policy reached-prefix graph and early-rejection theorem are
proved. Selected records retain original order and multiplicity. A stopped
class is an original member. A true query stops without later primary
receipts. Both meets/classMeets mode equations preserve actual full outcomes.

Current primary gates retain semantic readiness, costs, physical fields,
and histories. The exact secondary anchor derives queried effects from
ClassSat. verified derives all intermediate scan invariants under independent
acceptance and satisfaction of all active original classes. stopped_refutes
excludes such a candidate when the actual scan stops. No reached-ready,
whole-original-forest closedness, semantic answer oracle, or completed
fallback premise is supplied. Actual WordRanges and exploration remain.

Global unfolding/predicate/descendant memo composition and actual query
unfolding receipts remain. Native node/edge tables are separate. Original
ordered Active class extraction, initial caller invariants, selected fallback,
GHC demand/sharing, checked state, machine bounds, general completion,
waiting counts, template exclusion, broader APIs/runtime, and all separate
Sized contracts remain open.

Full audit: 2,060 jobs, 52,058 dependency checks, permitted axioms only,
no new warning. Five new modules and two additive Audit imports. Older proof
definitions and all four Haskell package trees match `a421f9cd` unchanged.
Start: `/tmp/mcfta-native-cost-checkpoint-20261015-2020/` (2,724 files).
Closing: `/tmp/mcfta-lazy-prefix-checkpoint-20261015-2030/` (2,730 files).
Script: `/tmp/mcfta-preserve-lazy-prefix-20261015.py`.
All prior artifacts remain. Weekly allowance is 85%. No unchanged Haskell
checks were repeated.

## Actual query cost retention and current primary class receipts

Proof checkpoint `09cfb640`, source main `525d722e`. Read
`lean/notes-source-native-costs.md`. Full scope stays active.
Earlier sections retain historical checkpoint scope.

The cost gap in the supported-query interface is closed. Actual optional
binders, native evaluation, scoped requests, exposure, projection, task
folds, delayed exploration, and every Decision branch retain CostHeap.
Exposure and projection effects permit open inputs. Anchored seeded queries
retain the existing closed-result proofs without closing unrelated children.
seeded_decision_ready derives final IdleReady, costs, old gate Ready, Keeps,
and normalized fields after either answer. No final invariant is supplied.

Anchored support and initial costs/fields remain explicit. ClassSat still
derives proper paths for the refutation proof. A false forest gate alone
does not exclude root []. Native WordRanges and completed exploration remain
actual receipt premises. This is not unconditional whole-caller readiness.

Enabled primary Path/Class graphs, exact worker correspondence, finite
certified class execution, and three-family memo receipts are now proved.
The current lazy original-class prefix and early stop remain the next target.
Global unfolding receipts through query work and saved-entry coherence still
need composition. Native node/edge memos are separate. Fallback, completion,
checked state, machine bounds, lazy/runtime transfer, waiting counts,
template exclusion, broader APIs, and all separate Sized contracts remain.

Full audit: 2,055 jobs, 52,039 dependency checks, permitted axioms only,
no new warning. Nine new modules and two additive Audit imports. Older proof
definitions and all four Haskell package trees match `a8bbe9b5` unchanged.
Start: `/tmp/mcfta-gate-class-query-checkpoint-20261015-2002/` (2,714 files).
Closing: `/tmp/mcfta-native-cost-checkpoint-20261015-2020/` (2,724 files).
Script: `/tmp/mcfta-preserve-native-cost-20261015.py`.
All prior artifacts and the new marked task-cost draft remain. Weekly
allowance is 86%. No unchanged Haskell checks were repeated.

## Actual scoped class queries from secondary gates

Proof checkpoint `602b20a7`, source main `525d722e`. Read
`lean/notes-source-gate-class-query.md`.

Actual Operand/Fold/Seeded traces now derive retained native states, closed
resident results, accepted common subtrees, and normalized physical fields
from anchored projection support. A false actual secondary class gate and
true actual seeded-query Decision refute the original active class. The
proof derives proper paths under ClassSat before effects and fields. No
static whole-forest domain or semantic emptiness oracle is supplied.

The current caller needs a reached lazy-prefix model. A true query can stop
before later primary classifications. Old full SourceMemoClassSelection uses
the free-only policy and does not certify the enabled primary partition.
Current primary Path/Class wrappers, all three gate memo families, actual
global unfolding calls through projection/native work, and fallback remain.

A fresh secondary gate after earlier queried-false work has a separate
cost-readiness gap. Existing IdleReady/fields/Keeps/growth do not derive
old Ready CostHeap. Prove actual preservation or a sufficient invariant
for original inputs. Do not infer the heap from growth or hide it in a
reached-call assumption. General completion, native word ranges, newer
checked state, lazy/runtime transfer, recent features, broader APIs, and
all separate Sized obligations remain open.

Proposed cost route: actual optionalBinder via maybeMu_eq/build_costs, then
the NativeBudgetHeap.Bounds induction and Step.cost_heap. SemanticReady
already supplies the other gate Ready fields. Actual Fold/Seeded/Decision
cost retention remains unproved. Original-record facts alone do not cover
all reconstructed requests and cache hits in existing cost APIs.

Full audit: 2,046 jobs, 51,989 dependency checks, permitted axioms only,
no new warning. Prior definitions remain byte-identical except one Audit
import. All four Haskell package trees match `702443fe`; checks were not
repeated. Start: `/tmp/mcfta-gate-projection-checkpoint-20261015-1953/`
(2,709 files). Closing: `/tmp/mcfta-gate-class-query-checkpoint-20261015-2002/`
(2,714 files). Script: `/tmp/mcfta-preserve-gate-class-query-20261015.py`.
All prior artifacts remain. Weekly allowance is 86%. Full scope stays active.
Earlier sections retain historical checkpoint scope.

## Actual selected projection from secondary gate traces

Proof `ea919bfa` is pushed. Source main remains `525d722e`. Read
`lean/notes-source-gate-projection.md`.

The gate-to-projection bridge now derives actual finite natural-path
projection, closed resident output, retained accepted subtrees, and physical
annotations. Support is closedness or an exact false node certificate at
one fixed final gate heap. Actual epsilon origins and complete canonical
row readback transfer it to selected children. Repeated open Mu heads use
actual head completion and exact language. No whole-original-value or
whole-head closedness premise is restored.

Initial and anchor gate Ready retain CostHeap for endpoint closedness.
Later callers need SemanticReady, current original availability, and growth
from the completed gate heap. Actual effects retain histories. False proper
forest gates derive all projection premises; [] remains excluded.

Next adapt actual Operand.force and IdleReady.advance, then Fold/Seeded
with one anchor and retained original Values. Preserve the seeded rotation.
For refutes_decision, assume ClassSat first and derive proper paths before
effects/fields. Nontrivial and false secondary gates alone do not exclude
[]. Actual native word ranges, checked-state transfer, lazy demand, general
completion, full caller, recent features, broader APIs/runtime, and Sized
remain open.

Full audit: 2,042 jobs, 51,971 dependency checks, permitted axioms only,
no new warning. Prior definitions remain byte-identical except two Audit
imports. All four Haskell package trees match `5234cbab`; checks were not
repeated. Start: `/tmp/mcfta-secondary-gate-checkpoint-20261015-1936/`
(2,703 files). Closing: `/tmp/mcfta-gate-projection-checkpoint-20261015-1953/`
(2,709 files). Script: `/tmp/mcfta-preserve-gate-projection-20261015.py`.
All prior artifacts remain. Weekly allowance is 86%. Full scope stays active.
Earlier sections retain their historical checkpoint scope.

## Secondary gate replay and exact recursive head exposure

Proof `e7c08d35` is pushed. Source main remains `525d722e`. Read
`lean/notes-source-secondary-gate.md`.

Actual secondary traces preserve semantic heaps, constructor histories, and
physical annotations. Exact effect-free replay above the completed final
gate heap no longer requires CostHeap. Every original false row/path keeps
its certificate. False node endpoints derive original closedness through
actual free-name retention, with the endpoint cost invariant explicit.

Actual repeated-Mu head reads now complete after a false gate in a retained
later cache. The proof follows the source collect restart, visited skips,
and canonicalization. Every completed actual head has exactly the original
independent language and retains physical annotations. These results need
no whole-input closedness, CostHeap, preparation, acyclicity, or final answer
oracle. They do not assert that all exposed children are closed.

The next gap is support of selected children in actual exposed rows. Anchor
each reusable false certificate at the final gate heap. Recover row origins
and selected child positions, then induct over epsilon reachability and
path length. CostHeap is needed only at the anchor's selected endpoint.
The proposed support invariant is not yet a theorem. General projection,
seeded caller composition, native/lazy/runtime transfer, recent features,
general completion, and separate Sized obligations remain open.

Full audit: 2,037 jobs and 51,930 dependency checks, permitted axioms only,
no new warning. Prior definitions remain byte-identical except four Audit
imports. All four Haskell package trees match `516615d0`; checks were not
repeated. Start: `/tmp/mcfta-open-head-checkpoint-20261015-1910/`
(2,696 files). Closing: `/tmp/mcfta-secondary-gate-checkpoint-20261015-1936/`
(2,703 files). Script: `/tmp/mcfta-preserve-secondary-gate-20261015.py`.
All prior artifacts and the new marked draft remain. Weekly allowance is
86%. Full scope remains active. Earlier entries are historical.

## Open ordinary Mu projection and selected-path completion

Proof `00b4806e` is pushed. Source main remains `525d722e`. Read
`lean/notes-source-open-ordinary-head.md`.

The original closed-head premise is unnecessary for a single ordinary Mu
exposure. Actual stored unfolding completes for available open records in a
semantic-ready cache. Ordinary reconstruction retains exact independent
language, all semantic heaps, availability, histories, and annotations.
Finite selected-path completion then gives finite open Mu projection from
the domain of its actual rebuilt head. No final projection-language premise
or completed-projection premise is needed at this endpoint.

The retained warm gate fixture checks the exact operations. Reconstruction
returns the same unfolded ordinary value and heap. Its free list still
contains reference 999, while its selected child path is closed. The domain
comparison replaces one forest value only for the proof. The caller is
unchanged. No whole-source ready cache or completed caller is asserted.

The remaining bridge is from false gate traces to later projection support
in the grown caller heap. Existing final-heap replay is derived, but its
Ready has an extra cost heap. Repeated Mu/nodeEdges cases and current memo
composition remain open. Forest root [] is not certified by a false gate.
All broader native, lazy-demand, completion, recent-feature, API/runtime,
and separate Sized obligations remain.

Full audit: 2,031 jobs, 51,878 dependency checks, permitted axioms only, no
new warning. Prior definitions remain byte-identical except two Audit imports.
All four Haskell package trees match `fd279a46`; checks were not repeated.
Start: `/tmp/mcfta-refused-query-checkpoint-20261015-1853/` (2,691 files).
Closing: `/tmp/mcfta-open-head-checkpoint-20261015-1910/` (2,696 files).
Script: `/tmp/mcfta-preserve-open-head-20261015.py`. All prior artifacts remain.
Weekly allowance is 87%. Full scope remains active. Earlier entries are historical.

## Scoped refused-class queries and the open Mu boundary

Proofs `e36ecf90` and `38569b85` are pushed. Source main remains `525d722e`.
Read `lean/notes-source-refused-class-query.md`.

Completed scoped decisions now refute the caller's actual seeded query.
They retain the immediate empty-query branch and the absent-key branch.
An ordinary projection needs closed selected leaves, not closed unvisited
siblings. The proof derives its query fields and native state from the
actual fold. It supplies no final semantic-answer oracle.

The remaining domain implication is false. An actual open Mu construction
has an active class, true primary gate, and false secondary gate. The
sequential secondary call starts from the primary-returned heap and leaves
that exact heap unchanged. The original Mu is open, so the current path
domain fails. This is a counterexample to a proof premise. It is not a
counterexample to emptiness soundness or a whole-source ready caller.

Next prove open ordinary-head reconstruction from actual unfolding and
ordinary allocation. Preserve language, resident values, semantic heaps,
histories, and normalized fields. Do not assume recursive-input closedness.
Then compose the current gate/query/fallback caller. Lazy demand, checked
native transfer, machine ranges, general completion, waiting counts,
template exclusion, broader APIs, and separate Sized contracts remain open.

The full pinned audit passes 2,027 jobs and 51,762 dependency checks, with
permitted axioms only and no new warning. Prior definitions remain unchanged
except two additive Audit imports. All four Haskell package trees match
`2652fc98`; unchanged checks were not repeated. Start snapshot:
`/tmp/mcfta-seeded-query-start-20261015-1837/` (2,684 files). Closing snapshot:
`/tmp/mcfta-refused-query-checkpoint-20261015-1853/` (2,691 files).
Script: `/tmp/mcfta-preserve-refused-query-20261015.py`.
All earlier artifacts remain. Weekly allowance is 87%. Full scope remains.
Earlier sections retain their historical checkpoint scope.

## Completed scoped task-table soundness

Proof checkpoint: `3c2346e8`, pushed to origin/formalize. Source main remains
`525d722e`. Read `lean/notes-source-emptiness-task-soundness.md`.

Physical task readiness alone does not imply saved-result language. The new
proof derives a separate saved common-subtree invariant from actual folds.
Immutable body receipts survive completed cells. Actual accepted source rows
and final reads then derive strictly smaller accepted requirements. Their
literal classification supplies Decomposes for the existing finite kernel.
No final-row, inventory, semantic-output, or global native-operation oracle
is needed. This avoids the invalid assumption that a fixed resident heap
supports arbitrary future allocating projection and intersection calls.

The completed scoped table and equality-stop loop are sound at the original
closed query's independent guarded language. Original normalized construction
also gives exclusion at the declared syntax language. The source corollary
still assumes a completed scoped exploration trace. It does not prove actual
lazy Haskell demand, checked-native transfer, word ranges, or completion.
Current per-call emptiness and whole equality-caller correspondence remain
open, as do the waiting-count, template exclusion, and broader library gaps.

Caller review preserves two further boundaries. Its intersection uses the
seeded fold rather than the row analysis foldr1. A false secondary gate
certifies visited endpoints, not closedness of every original child. The
existing seeded lemmas require that stronger whole-forest premise. Derive
path-local premises for the general caller. Exact demand transfer must also
preserve empty-query and absent-key shortcuts before the fixed-point loop.

The pinned audit passes 2,021 jobs and 51,551 dependency checks with permitted
axioms only and no new warning. All prior definitions and artifacts remain.
Audit gains one import. All four Haskell package trees match `811910a2`, so
their unchanged checks were not repeated. Starting preservation snapshot:
`/tmp/mcfta-task-language-start-20261015-1816/` (2,676 files).
Closing snapshot: `/tmp/mcfta-task-soundness-checkpoint-20261015-1832/`
(2,684 files). All older external drafts remain in its preservation manifest.
Full scope and the separate exact Sized contracts remain open.

## Main 525d722e: representative waiting counts

Current source main is `525d722eefb722be27def2d965b75f56c7a08bdf`.
Preserving merge: `c12a0420`. Prior checkpoint: `eb3f6d07`.
Backup: `backup/formalize-before-main-525d722e-20261015-1809`.
Read `lean/notes-main-525d722e.md`, then the captured-task and template notes.
Continue on formalize and push verified checkpoints. Full scope remains open.

The source keeps waiting counts by current union-find representative. It uses
pure root reads, gained/lost slot deltas, and post-union count relocation.
The paired assimilation writes retain counts. Correctness must hold at the
compound-operation endpoints; intermediate states can have stale counts.
The scheduler now reads waiting-map keys without path-compression effects.
Existing raw-key index proofs remain valid for their prior models. Current
source needs aggregate-count, differential-write, rekey, pure-root, scheduler,
and machine class-total bridges. Do not assert identical final UF storage.

provablyEmpty's declaration and body are unchanged. The immediate task target
remains immutable captured-body receipts and saved common-subtree semantics,
then accepted-row requirements. Progressive lazy demand, checked native state,
word bounds, general completion, and the current whole caller remain open.
Template exclusion and all other full-library gaps remain separate targets.

The repository-required strict Nix build and all six suites pass 704
examples plus golden checks. Fourmolu passes both changed Haskell files.

All Lean definitions remain unchanged; the prior 2,014-job / 51,484-dependency
audit was not repeated. Separate Sized and Cabal metadata checks were not
repeated because their files are unchanged. Production definitions match main.
Only the retained constructor changelog entry and caller-repro comment differ
in package trees. All prior proofs, repros, marked drafts, external drafts,
stashes, and other worktrees remain. Pre-merge snapshot:
`/tmp/mcfta-main-54f4c272-checkpoint-20261015-1806/` (2,675 files).
Closing snapshot: `/tmp/mcfta-main-525d722e-checkpoint-20261015-1813` (2,676 files).
Weekly allowance is 88%. Stop owned work at 1% or less. No board posts or
deployments. Keep the optimized core and older constructor/equality work.
Keep exact Sized node-count classes, finite execution, canonical sequence,
distinct size order, and both signed inverses as separate contracts.
Earlier entries below retain historical source and proof scopes.

## Main 54f4c272: template exclusion

Current source main is `54f4c272e72c0ab4c9457d56c66653459f5c6f31`.
Preserving merge: `29c6cfc7`. Prior checked proof checkpoint: `7489c506`.
Backup: `backup/formalize-before-main-54f4c272-20261015-1802`.
Read `lean/notes-main-54f4c272.md`, then the captured-task note. Continue on
formalize and push verified checkpoints. Full library scope remains open.

Upstream adds matchesNone, exclude, excludeFTA, and Obligation. The required
language is the original language filtered by templates that match at the
root. Existing matching/restriction proofs survive unchanged. New exclusion
has no Lean coverage yet. Its central obligation is a complete disjoint
edge-copy partition, followed by canonical obligations, cyclic explicit FTA
correctness, interned source correspondence, and recursive completion.
Unambiguity needs a separate proof; ambiguous run counts can change.

Equality, emptiness, Sized, native, and generator source are unchanged. The
immediate proof target remains immutable class-body receipts and the saved
common-subtree invariant, followed by actual accepted-row requirements.
Progressive lazy row demand, original child forcing, checked native transfer,
word ranges, general completion, and the current whole caller remain open.
Keep all broader API/runtime gaps and separate Sized contracts in scope.

The strict Nix build and all six suites pass 704 examples plus golden checks.
Changed-file Fourmolu and all four active-package cabal-gild checks pass.
Repository instructions require the Nix validation. Lean files are unchanged;
the prior full audit of 2,014 jobs and 51,484 dependency checks was not repeated.
Separate Sized probes were not repeated because their source is unchanged.
All earlier proofs, repros, marked drafts, external drafts, stashes, and other
worktrees remain. Production definitions match main. Only the retained
constructor changelog entry and caller-repro comment differ in package trees.

Pre-merge snapshot: `/tmp/mcfta-source-emptiness-thunks-checkpoint-20261015-1759/`
(2,674 files). Closing snapshot: `/tmp/mcfta-main-54f4c272-checkpoint-20261015-1806`
(2,675 files). Weekly allowance is 88%. Stop owned work at 1% or less.
No board posts or deployments. Earlier source heads, observations, counts,
and targets below retain their historical checkpoint scope.

## Captured class tasks and final physical readback

Source main remains `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `7b956d72`. Proofs: `ec3ebf72`, `305da606`,
`c2321463`, and `66b9c097`. Read `lean/notes-source-emptiness-tasks.md`
first. Continue on formalize and push verified checkpoints. Full scope remains.

The task graph captures original forests and ordered class paths without
native work. Actual first forces store native fold results. Hits reuse those
complete values. Source row capture keeps the original child prefix and class
order. Local force/exposure effects now derive final record validity,
complete reads for every stored row task, literal table keys, and physical
readback without supplied final inventory, coverage, or coherence. Native
folds and row reads preserve normalized physical fields. Original normalized
closed construction derives the initial task domain. After row completion,
the admission budget plus one bounds equality-stop fixed-point checks.

Review found two explicit source limits. Exposure completes nodeEdges reads
and captures all rows before child work. Haskell reveals rows progressively.
Exact lazy row demand, original child-thunk forcing, and full cache-effect
order remain open. Task readiness proves availability and closure, not saved
result language. No emptiness oracle or whole-caller soundness is claimed.

Next derive immutable class-body receipts through capture, finish, and traces.
Derive a saved-result common-subtree invariant using each actual Fold.included
and class_witness. Combine accepted source rows, normalized classes, and final
reads to derive smaller requirements for the literal table. Do not assume
that a fixed final resident heap is closed under arbitrary native operations.
Model progressive row demand and original child forcing. Transfer old scoped
leaves to checked constraint allocation; derive word ranges and completion.
Carry both gate modes and all three memo families through the current lazy
class scan, selected fallback, and caller. General native/whole-caller
completion remains unproved. Preserve the full intended library semantics.

The pinned audit passes 2,014 jobs and 51,484 dependency checks with only
permitted axioms. No new warning occurs. All earlier Lean definitions except
one additive Audit import and all four package trees are unchanged. Prior
Nix tests, metadata, formatting, and Sized probes were not repeated. All
proofs, repros, marked drafts, external drafts, stashes, and other worktrees
remain. Start: `/tmp/mcfta-source-emptiness-thunks-start-20261015-1743/`
(2,667 files). Closing snapshot: `/tmp/mcfta-source-emptiness-thunks-checkpoint-20261015-1759`
(2,674 files). Weekly allowance is 89%. Stop owned work at 1% or less.
No board posts or deployments. Earlier targets and counts are historical.

Keep runtime/source correspondence, InputsThrough, semantic finish receipts,
sidecar coverage, candidate-parametric Mu contexts, derived refinements, named
measures, getAllAtPath, decision-model, parser/decoder bridges, recursive
generators, and extraction as separate targets. Keep the optimized interned
core and older constructor/equality work. Sized exact node-count classes,
finite execution, canonical sequence, distinct size order, and both signed
inverse directions remain separate contracts.

## Delayed worklist traces and actual entry inventories

Source main remains `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `c0ae83a2`. New proofs: `2a1e918e`.
Read `lean/notes-delayed-emptiness.md` first. Continue on formalize and push
verified checkpoints. Full library scope remains open.

Reached stateful traces retain each force before the source tests and each
admitted value with its exact delayed rows. They derive old-entry retention,
unique keys, admission bounds, and actual force/exposure receipts. Every task
in a newly stored row is forced before a completed trace returns, including
queued tasks reached after budget exhaustion. Zero budget retains the table;
it does not exclude native effects or prove completion.

Actual entry records now generate their own certified inventory. Closed
availability and exact keys in one heap derive coverage from literal table-key
equality. Coherence derives physical readback. An arbitrary inventory or
separate coverage premise is no longer required. Actual native exploration
must still derive those entry records in one common final heap.

Next instantiate source Task/Force/Expose with captured class thunks and
retained force results. Preserve original child traversal before delayed class
folds. Derive normalized field preservation, final entry validity, and completed
row readout. Connect source folds and exposure to the certified table supply
and primitive laws, then instantiate each oracle call. Transfer native leaves
to checked constraint allocation. Carry both gate modes and all three memo
families through the lazy refused-class scan, selected fallback, and caller.
General native completion, internal ranges, and whole current reduction remain
open. The reached trace is not a whole-source termination theorem.

The pinned Lean audit passes 2,008 jobs and 51,372 dependency checks with only
permitted axioms. No new warning occurs. All earlier Lean definitions except
two additive Audit imports, all package trees, repros, marked drafts, external
drafts, stashes, and other worktrees remain. Haskell checks were not repeated
because all four package trees match c0ae83a2.
Start: `/tmp/mcfta-delayed-emptiness-start-20261015-1730/` (2,664 files).
Closing snapshot: `/tmp/mcfta-delayed-emptiness-checkpoint-20261015-1737/` (2,667 files).

Keep native InputsThrough, semantic finish receipts, sidecar coverage,
candidate-parametric Mu/repeated-pair contexts, full runtime correspondence,
derived refinements, named measures, getAllAtPath, decision-model, parser/decoder
bridges, recursive generator composition, and extraction as separate targets.
Keep the optimized interned core and older constructor/equality work. Sized
exact node-count classes, finite execution, canonical sequence, distinct size
order, and both signed inverses remain separate contracts. Weekly allowance
was 89% on this checkpoint. Stop work and owned workers at 1% or less. No board
posts or deployments. Earlier next targets and counts below are historical.

## Explored emptiness tables and source row readback

Current source main remains `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Starting checkpoint: `7b270679`. New proofs: `76afeec1`, `e736beeb`, and
`71b7fd08`. Read `lean/notes-emptiness-table-source.md` first. Continue on
formalize and push verified checkpoints. Full library scope remains open.

The actual completed table now derives the finite key carrier, exact raw
rounds, least fixed point, and equality-stop completion. Empty-start exploration
derives exact stored-supply receipts. Certified source values derive complete
untagged identity readback under common-heap coherence and inventory coverage.
The physical table endpoint excludes original guarded terms without a supplied
Readback oracle. Actual nodeEdges reads derive accepted retained rows, active
classes, and satisfaction of the full equality accessor, including residual
guards. Original normalized closed construction derives those reads. Plain
getPath operands and both distinct native fold schedules retain their actual
scoped caches and smaller accepted-subterm witnesses. The seeded helper also
retains its empty-list fallback.

Next model the stateful worklist of delayed requirements. Original children
precede captured class-intersection thunks. Force each queued item before the
budget check; do not force all class intersections before child traversal.
Derive inventory coverage and closed resident requirements in one final heap.
Connect actual row and fold receipts to the certified table supply and primitive
laws, then instantiate each oracle call. Transfer scoped fold leaves to the
newer checked constraint-operation state. Word-range checks and general native
completion remain open. Carry both gate modes and three memo families through
the lazy refused-class scan, selected fallback, and recursive caller.

The pinned Lean audit passes 2,006 jobs and 51,337 dependency checks with only
permitted axioms. No new warning occurs. All Haskell package trees are unchanged;
prior Nix build/tests/formatting/metadata and separate Sized probes were not
repeated. All earlier proof definitions except additive Audit imports, repros,
marked drafts, external drafts, stashes, and other worktrees remain.
Start: `/tmp/mcfta-emptiness-table-start-20261015-1707/` (2,656 files).
Closing snapshot: `/tmp/mcfta-emptiness-table-checkpoint-20261015-1726/` (2,664 files).

Keep native InputsThrough, semantic finish receipts, internal ranges, sidecar
coverage, and candidate-parametric Mu/repeated-pair contexts as separate targets.
Keep the optimized interned core and older constructor/equality work. Full
source/runtime correspondence, derived-refinement APIs, named measures,
getAllAtPath, decision-model, parser/decoder bridges, and extraction remain open.
Sized exact node-count classes, finite execution, canonical sequence, distinct
size order, and both signed inverse implications remain separate contracts.
Weekly allowance was 89% at 2026-10-15 17:23 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments. Earlier
source heads, counts, runtime observations, and next targets are historical.

## Main a22b2ad4: conservative emptiness

Current source main: `a22b2ad46ffcad57a77b64447c18da7b0850f52f`.
Preserving merge: `e612302b`. Pre-merge checkpoint: `aaeeac64`.
Proofs: `598ad8dc`, `59b2fbf4`, `0414c98b`, and `dab4eade`.
Read `lean/notes-main-a22b2ad4.md`, then the stateful memo note. Continue on
formalize and push verified checkpoints. Full library scope remains open.

The source adds provablyEmpty and an early-empty branch for refused equality
classes. The primary gate retains the 24a policy. The secondary gate uses the
older endpoint rule. Five additive modules prove exact mode agreement, finite
Boolean stabilization and leastness, smaller accepted witnesses for actual
source-shaped requirement lists, completed-value worklist termination and
admission bounds, and conditional constrained-term preservation by the new
pass. The row theorem derives Decomposes from three primitive laws, physical
readback, and one-level accepted row exposure. The pass theorem requires a
sound per-call oracle; its actual source graph bridge remains open.

Next connect actual exploration to the finite table. Retain native exposure,
projection, and both distinct intersection-fold schedules. Derive normalized
active classes, closed resident requirements, and untagged machine identity
readback. Then instantiate oracle soundness and carry both gate modes plus
all three memo families through the actual lazy refused-class scan. Reconnect
the selected-class fallback and recursive caller. General native and outer
caller completion remain unproved. The 1000-key budget bounds admissions,
not native calls, thunk demands, work, or allocation.

The fixture now reduces to EmptyNode. A fresh-process temporary observer
prints Just True for that comparison. The preserved old identity observer
cannot observe EmptyNode; its error is not a reduction cycle. Raw malformed
singleton/empty classes demonstrate why normalized Constraint invariants are
necessary. They are not counterexamples for valid normalized inputs.

The strict Nix build and all six suites pass: 697 examples plus golden checks.
Changed-file Fourmolu passes. Metadata and Sized are unchanged; prior metadata
and separate 205-rank checks were not repeated. The pinned Lean audit passes
1,999 jobs and 51,206 dependency checks with permitted axioms only. No new
warning occurs. Logs use `/tmp/mcfta-main-a22b2ad4-*-20261015.log`.
Repository instructions require the Nix validation.

All production definitions match this main. Only the retained constructor
changelog entry and caller-repro comment differ in package trees. The reviewed
upstream delta changes four files. Other optimized interned operations,
normalization, Sized, and generator source remain unchanged. Prior proofs
except additive Audit imports, repros, marked drafts, external drafts, stashes,
and other worktrees remain. Pre-merge snapshot:
`/tmp/mcfta-endpoint-memo-checkpoint-20261015-1646/` (2,650 files).
Closing snapshot: `/tmp/mcfta-main-a22b2ad4-checkpoint-20261015-1704/` (2,656 files).

Keep unchanged native InputsThrough, semantic finish receipts, internal ranges,
sidecar coverage, and candidate-parametric Mu/repeated-pair contexts as separate
targets. New derived-refinement APIs, named measures, full causal/pending
correspondence, containers/word adequacy, lifetime capacity, getAllAtPath,
decision-model, parser/decoder bridges, and extraction remain open. Keep the
optimized interned core and older constructor/equality work. Sized exact
node-count classes, finite execution, canonical sequence, distinct size order,
and both signed inverse implications remain separate contracts.
Weekly allowance was 90% at 2026-10-15 16:55 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments.
The sections below retain historical source heads, observations, and targets.

## Stateful endpoint checks and three memo families

Proof source main: `24a710a39e5adcc94c4d986f0bda81a8483bdba8`.
Current preserving merge: `6a02619c`. Starting checkpoint: `84735645`.
Stateful execution: `c403f378`. Descendant memo: `491b05b2`.
Active-call proof: `18134c83`. Three-memo source receipts: `9f6d66a6`.
Pull returned Already up to date. The closing remote check then found main
at a22b2ad4, now fetched. Preserve this proof checkpoint before reviewing and
merging its emptiness check. The proofs in this section use 24a710a3. Continue
on formalize and push verified checkpoints. Read `lean/notes-endpoint-memo-stateful.md`,
then `lean/notes-main-24a710a3.md`. The prior next-stateful-node target is done.
The actual current class-selection pipeline and full library scope remain open.

EndpointStatefulGate and its Trace/Graph/Completion modules implement the
current endpoint rule with actual returned constructor caches. Completed
logical graphs and finite execution agree in both directions. Boolean and
full final-cache results are unique. The proved actual unfolding rank derives
finite node/path/class checks and original cold-construction receipts.
The two node reads are pure parameters at this layer.

SourceEndpointMemo follows each memoized recursive helper call in original
row/member/child order. It carries its own completed table and the existing
constraint-predicate table. Hits bypass all body work. False calls pass both
returned tables onward; true calls stop the scan. Correctness derives the
concrete helper answer, current validity of both returned tables, and retention
of every old completed entry. Constructor growth preserves the invariant.
Original construction supplies inputs. Exact stored input/answer readback and
an effect-free second identical query follow from resident key injectivity.

SourceEndpointMemoAncestry proves strict possible-child descent, availability,
and ancestor-key separation. Its size lemmas accept caller SizeOf instances;
a concrete FullSyntax probe verifies that specialization. The active-call
machine records a miss before its body. Under derived strict active ancestry,
no recursive call demands an active ancestor key. The machine returns exactly
the completed model's answer and both memo maps. Cold resident inputs and
original construction derive completion without an assumed finishing trace.
This is a sequential active-call result, not native first-installed ownership.
Pre-existing suspended/active cells, winner readback, concurrency, typed family
selection, Eq/Hashable, native maps, unsafe IO, and GHC remain source limits.
The predicate-memo operation is still a completed operation in this machine.

EndpointMemoGateTrace/Lift derive actual completed calls of all three tables:
unfolding, constraint predicates, and descendant queries. An open endpoint
skips the descendant helper. A closed endpoint retains its actual paired result.
Mu calls update the predicate table and then use the actual unfolding memo
when needed. False siblings retain all returned tables. Initial Ready,
available inputs, and coherent initial memos derive returned Ready, coherent
memos, constructor growth, and issued-ID history. No future memo validity is
supplied. EndpointMemoGateSource derives stable finite current-policy node
checks and these three-table receipts from original construction and empty
memos. It does not rewrite or prove the older class-selection worker.

Next derive current path/class receipt graphs and the complete ordered
physical class filter with all three tables. Connect that filter to the
existing proved physical sort and prechecks. Then retarget guarded class folds,
requireAll/path edits, native intersection prefixes, and recursive reduction.
Preserve earlier policy definitions and historical cycle witnesses. The
specific closed source cycle is fixed upstream; general caller/fixpoint
termination remains unproved. Continue the unchanged native intersection
obligations: InputsThrough, semantic finish receipts, internal word bounds,
sidecar coverage, and candidate-parametric Mu/repeated-pair contexts. New
derived-refinement APIs, named measures, full causal/pending correspondence,
container/word adequacy, lifetime capacity, getAllAtPath, decision-model,
parser/decoder bridges, and extraction remain open. Keep the optimized interned
core and older constructor/equality work. Sized exact classes, finite execution,
canonical sequence, distinct size order, and both signed inverses stay separate.

The pinned Lean audit passes 1,994 jobs and 51,072 dependency checks with only
propext, Classical.choice, and Quot.sound. Focused endpoints pass 612 jobs.
No new warning occurs; the old unused-input warning remains. Logs:
`/tmp/mcfta-endpoint-memo-audit-20261015.log` and
`/tmp/mcfta-endpoint-memo-focused-20261015.log`. No Haskell file changed.
The previous strict Nix build, 697 examples plus golden suite, formatting,
metadata, and separate 205-rank checks were not repeated.

Start: `/tmp/mcfta-endpoint-memo-start-20261015-1628/` (2,636 files).
Closing snapshot: `/tmp/mcfta-endpoint-memo-checkpoint-20261015-1646/` (2,650 files).
Every earlier proof definition except additive Audit imports, repro, marked
draft, external draft/limit file, stash, and other worktree is preserved.
All four Haskell package trees are byte-identical to the starting checkpoint.
Weekly allowance was 90% at 2026-10-15 16:43 CEST. Refresh before work; stop
work and owned workers at 1% or less. No board posts or deployments. Older
source heads, counts, and next targets below retain their historical context.

## Main 24a710a3: endpoint recursion guard

Current source main: `24a710a39e5adcc94c4d986f0bda81a8483bdba8`.
Preserving merge: `6a02619c`. Proof checkpoint: `3eed507c`.
Pre-merge checkpoint: `f976cb6a`. Backup:
`backup/formalize-before-main-24a710a3-20261015-1612`.
Continue on `formalize` and push verified checkpoints. Read
`lean/notes-main-24a710a3.md`, then `lean/notes-native-field-running-invariants.md`.
After a pull, check fetched main ancestry before proof edits. Keep all earlier
proofs, repros, repairs, drafts, stashes, and worktrees. Full scope remains open.

This main update changes the existing equality gate. An ordinary path endpoint
now blocks a class if it reaches a constrained Mu. The helper checks cached
zero depth first, traverses ordinary children and stored union members, and
stops at every Mu. The path gate still blocks references and unions before
its own finite shortcut. The helper has a new global unary memo. The comment
conflict retained the upstream explanation and the standalone repro pointer.
All production definitions now match main. Only that pointer and the earlier
constructor-probe changelog entry differ in the four package trees. Interned
construction, intersection, equality normalization, and Sized are unchanged.

Six additive Lean modules model the stronger policy. SourceEndpointReachability
has a structurally total stored-record traversal and an exact witness theorem.
EndpointRecursionGate preserves dispatch order, completed-result stability,
selected-class subset of the previous policy at the same fuel, and the bounded
constrained-pass law under existing primitive graph laws. EndpointGateCompletion
proves ranked total decisions, finite completion, and agreement for nodes,
paths, and classes. SourceEndpointGate and SourceEndpointGateCompletion use
actual certified source records and the proved unfolding rank. Original source
construction derives finite current-policy checks for every finite path.
SourceEndpointCallerRegression evaluates the preserved original constructor
input and proves that its first endpoint is closed and has the new witness.
Every certified readback changes from the old clear answer to the new barrier.

The old ConstrainedRecursionGate, stateful/memo gate families, selection pipeline,
and caller-cycle proofs remain byte-identical. Their endpoint policy is now
historical. Their theorems remain valid for their definitions. They do not
prove exact current-source selection or cache effects. The new results do not
retarget those workers or model the new global memo. The generic pass law is
conditional on primitive operations; it is not a proof of the native caller.

The preserved Haskell caller repro with --cold now completes with Just 17.
Its unchanged default certificate prints Just False and raises its deliberate
certificate error: the repaired gate no longer produces the old narrowed-child
cycle. This is an expected historical-certificate mismatch. The upstream test
passes for reducePartially, termsMatching, and the README fixpoint composition.
The specific source cycle is fixed. General one-pass and repeated-pass
termination remain open. Unequal path lengths can still move constraints
below an unconstrained recursive unfolding. Do not infer a new cycle without
an actual current-policy witness.

Next carry the current policy through actual stateful selection and both older
gate memo families. Model the new descendant memo and its ordered recursive
calls. Boolean agreement alone does not imply equal caches. Then reconnect
class folds, guarded native prefixes, and the recursive caller. The existing
native intersection bodies are unchanged: continue deriving InputsThrough,
semantic finish receipts, internal ranges, sidecar allocation coverage, and
the candidate-parametric Mu/repeated-pair context law. New derived-refinement
frontends, named measures, global causal prehistory, pending equality thunks,
container/hash/word adequacy, lifetime capacity, unsafe IO, GHC, general
completion, repeated fixed points, getAllAtPath, decision-model, parser/decoder
bridges, and extraction remain open. Keep older constructor/equality work.
Sized exact classes, finite execution, canonical sequence, distinct size order,
and both signed inverse implications remain separate contracts.

The strict Nix build passes all libraries, executables, tests, and benchmarks.
All six suites pass: 697 examples plus the golden suite. Fourmolu passes both
changed Haskell files. Cabal metadata and Sized are unchanged; their previous
checks and separate 205-rank probe were not repeated. The Lean audit passes
1,981 jobs and 50,858 dependency checks with only permitted axioms. No new
warning occurs; the old unused-input warning remains. Validation logs use
`/tmp/mcfta-main-24a710a3-{tests,build-format,lean-audit}-20261015.log`.
The caller observations have separate caller-cold and caller-old-certificate
logs with the same prefix. Component checks do not establish full scope.

The previous snapshot `/tmp/mcfta-main-6fe34ab8-checkpoint-20261015-1605/`
retains all 2,629 file hashes and its clean f976cb6a checkpoint. The new snapshot
is `/tmp/mcfta-main-24a710a3-checkpoint-20261015-1625/` (2,636 files).
All prior Lean definitions except additive Audit imports, old repros, marked
drafts, stashes, other worktrees, and external draft/limit files remain.
Only Equality/Operations changes among the previously preserved optimized
interned/equality/Sized source files, by the reviewed upstream guard and a
comment pointer. Weekly allowance was 91% at 2026-10-15 16:23 CEST. Refresh
before work; stop work and owned workers at 1% or less. No board posts or
deployments. Older source heads, counts, and next targets below are historical.

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

## Actual cache capacity, complete Sized queries, and physical prechecks

The latest proof checkpoint is `d094c368`, after `8dab9b3c` and `a9cae6f5`.
The source base remains `origin/microcfta` at `7bfb69d1` (PR #129).
The fresh pull found no change. Read `lean/notes-native-capacity-sized.md`.
This section supersedes the earlier word-bound and compiler next targets.

`SourceRecursiveIntersectionNativeCapacity` derives tagged node, shifted
domain, and raw edge key safety from the actual three source counters.
`Capacity bits machine` uses native width `bits + 2`. The node counter is
less than `2 ^ bits`, the raw domain counter is less than `2 ^ (bits + 1)`,
and the edge counter is at most `2 ^ (bits + 2)`. Domain zero and the actual
raw identity plus one shift are both included.
`CacheRanges` bounds only caches at actual yielded prefixes of one call.
It assumes no completion, sufficient fuel, or request provenance.

`NativePrefixSplit` retains exact inner/outer traces and shared caches.
`NativeCapacityWords.prefix_words` derives request safety by strong induction
on actual prefix length. Completed inner bodies derive their own checked
correspondence before memo completion. `wordRanges` therefore derives the
whole request-word contract from actual cache capacity and initial source
safety and validity. No prefix-provenance premise is supplied.
`NativeCallback.complete_capacity` derives complete finite callbacks.
`NativeKeyCapacity` transfers these checks through actual child, edge, and
all-row scans. It retains exact short-circuit order and actual next caches.

`NativeCompiler.CapacityRanges` requires capacity only at actual reached
callbacks after the real prechecks. `complete_capacity` proves finite actual
compiler execution and literal reference results, including errors.
`SourceFreshOrdinaryCapacityNativeSized.complete` starts from actual closed
construction and normalized original annotations. It derives all cold table,
root, normalization, and ready-cache facts. Successful outputs have complete
optimized/reference query-record equality, one finite stable minimum prepass,
finite exact distinct node-count classes, counts, decoder order, identical
reference classes, distinct size-major prefixes, rank coverage, and both
global term inverses. Bounded and position/replay laws retain the same run.
No word-safety, final metadata, scan equality, product law, or native completion
is supplied. Concrete reached cache capacity remains an explicit resource
boundary. Arbitrary natural caches cannot fit a fixed native word width.

`SourceFreshOrdinaryNativeEntryPrecheck` proves literal EmptyNode/freeVars
precedence before traversal. Open references take the open-root error.
`closed_empty_exact` proves that the cold adapter's `reference.isNone` flag
matches the constructor check on closed roots. `reference_boundary` proves
why that domain is required: open references also encode as none, but the
actual source rejects them as open. No closed theorem is refuted. No Haskell
runtime defect is claimed. EmptyNode returns an empty source map directly;
the singleton empty-state cold table remains an auxiliary certificate.

Next connect the physical prechecks to a staged public execution relation.
Empty and open roots must return without cold rows or native callbacks.
Only nonempty closed roots may enter the derived cold/native compiler.
Use a common query API or exact source error so finite-key carriers stay
inside the row phase. Derive decisions from the actual physical value.
Do not supply arbitrary freeVariables or equate every reference-none value
with EmptyNode. A general Ready cache with the constraint invariant can cover
open inputs; actual closed construction derives those premises for its root.
Keep normalized original annotations explicit. Public raw equality patterns
do not normalize arbitrary values. Concrete containers, lazy scheduling,
external solver correctness, and verified Haskell extraction retain their
stated boundaries. Preserve the optimized interned core and older targets.

The current audit passes 1,542 jobs and 44,313 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-capacity-entry-precheck-20261014-audit.log`.
No new warning remains. The old unused `inputs` warning remains.
No production Haskell code changed. The same base passed 645 source examples,
five updated probes, and formatter checks. These were not repeated.
Current snapshot: `/tmp/mcfta-capacity-native-sized-checkpoint-20261014-2243/`.
It saves all 1,919 Lean-tree files. None of the 1,908 prior files is missing.
All prior proof modules except audit imports retain their exact bytes.
Fixtures and marked drafts retain their bytes. Preserve all backups, stashes,
worktrees, counterexamples, and repairs. No background proof worker is active.
All work remains local. Check allowance and stop all work at 1% or less.

## Complete warm callbacks and actual ordered ambiguity scans

The latest proof checkpoint is `53ba5057`, after `5de26f4b` and `3dd34cb7`.
The current source base remains `origin/microcfta` at `7bfb69d1` (PR #129).
The fresh pull found no upstream change. This section supersedes earlier
warm-completion and ordered-scan next-target statements.

`SourceRecursiveIntersectionNative.Idle` excludes evaluating node and edge
memo cells. It permits suspended and returned cells. Initial tables are idle.
Actual completed body code and constructor/domain cache growth retain Idle.
`warm_node_terminal` derives a finite observation from the actual input view
and Idle. `warm_node_complete` excludes pending construction with complete
semantic heaps. It derives successful stable native execution, exact checked
correspondence, coverage, and Idle in the returned warm state. Empty initial
memo tables and supplied native completion are no longer required.
Checked per-request `WordRanges` remain explicit.

`SourceFreshOrdinaryNativeCallback.Execution` follows actual callback control.
Its empty-exposure branch returns false immediately and retains the exposure
cache. It does not execute row collection or minimum lookup. Its nonempty
branch records finite native, exposure, collection, and minimum execution.
`complete` derives a complete callback with exact common-term Boolean,
actual machine growth, and all seven next-call invariants in `Ready`.
`Execution.unique` proves identical Boolean and cache at every successful
choice of bounds. `Execution.correct` covers every actual completed callback.
The earlier unconditional cold-table wrappers remain auxiliary finite
readback certificates. They do not define the callback's early-return control.
The early-return repair changes only the formal execution relation.
The live Haskell already has this branch. No runtime bug was found here.

`SourceFreshOrdinaryNativeKeyCallback.complete_keys` derives closed original
physical operands and their exact languages from actual finite input-table
metadata. Later ready caches retain those same operands. Every checked key
pair has finite actual callback execution, the literal finite reference
product Boolean, and its exact subsequent cache. No native completion,
product-language equation, or exact product-row adapter is supplied.

`SourceShortCircuitScan` models actual left-to-right all/any scans.
`SourceFreshOrdinaryNativeKeyScan.children_complete` and `children_correct`
connect the actual zipped child scan to the reference child-overlap Boolean.
`EdgeExecution` rejects different symbols or arities before callbacks.
`edgePairs` retains the ordered source tails comprehension. `edgeQueries`
retains finite map-key order and every row's edge-pair order.
`scan_complete` derives finite actual all-row execution. `scan_correct`
proves the literal reference ambiguity Boolean for every completed run.
Actual caches pass from each executed callback to the next.

The nested `Ranges` predicate checks only reached queries and suffixes after
continuing actual executions. A decisive result does not demand later checks
or calls. It does not assume callback completion or a product-language law.
Do not replace this contract with word bounds on arbitrary future heaps.
Input child-key closure and normalized source constraints retain their stated
boundaries. Whole Haskell extraction and concrete lazy scheduling remain open.

Next connect the actual scan to literal compiler results. Preserve empty,
open, constrained, ambiguous, and canonical branches in source order. Derive
the cyclic input record from actual finite raw rows and root membership.
Use the real constraint precheck to identify guarded rows with structural
rows before applying the new scan equality. Derive the compiler output and
reuse the existing exact class, order, finite execution, and both inverse laws.
Do not leave a whole scan equality, product equation, exact-row adapter, or
native completion as a supplied premise at the actual source entry.
Read `lean/notes-native-full-scan.md`. Do not repeat completed warm success,
callback determinism, or the full ordered scan.

The current audit passes 1,520 jobs and 44,155 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-native-early-scan-20261014-audit.log`.
The old unused `inputs` warning remains. No new warning was introduced.
The unchanged source base already passed 289 core, 209 generator, and 147
refinement examples, all five updated probes, and both formatter checks.
Those Haskell checks were not repeated for these Lean-only changes.
No production Haskell code changed. No proof worker is active.
Current snapshot: `/tmp/mcfta-native-full-scan-checkpoint-20261014-2148/`.
It saves all 1,894 Lean-tree files. No prior file is missing.
All 1,886 previous files remain. Only audit imports, ledgers, README, and two
component notes changed among them. Older proofs, all three fixtures, and
all three marked drafts retain their exact bytes.
Keep every fixture, marked draft, backup, stash, and other worktree.
All work remains local. Check allowance before work and stop at 1%.

## Package rename and current source boundary

The current upstream base is `origin/microcfta` at `7bfb69d1` (PR #129).
The packages are `cfta`, `cfta-generator`, and `cfta-ghc`.
Their directories and Cabal targets use those names. `Data.CFTA.*` modules
retain their names. The workspace path, Git branch, and Lean namespace
`MicroCFTA` retain their names. The Lake package is now `cfta`.

The preceding PR #120 refresh at `71a15220` added the GHC package and expanded
synthesis. These applications still have no complete formal source model.
This scope does not include their benchmarks or workload specifications.

The preserving rebase replayed 555 commits. Its result is `ede5f85a`.
Backup `backup/formalization-before-package-rename-20261014-2112` retains
`2e165b8e`. One changelog conflict retained both the upstream rename note
and the four-line constructor repair note. Immediately after the rebase,
all 1,880 saved Lean-tree files matched byte for byte. No file was missing.
Evidence: `/tmp/mcfta-rename-refresh-20261014-2111/`.
The two stashes, other worktrees, three untracked fixtures, and marked drafts
remain. The active Haskell package trees differ from upstream only in that
retained changelog note.

PR #129 also changes the reserved solver prefix from `__microcfta_` to
`__cfta_`. The source definitions, injectivity and freshness proofs, and
executable counterexamples now use the current prefix. This includes value,
bound, actual, contract, and integer names. The injective external encoding,
ambient freshness repair, and collision counterexamples remain.
Current source links and Cabal commands use the renamed directories and
packages. Historical commit hashes, snapshots, and log transcripts remain.
A path in an older source note now identifies the relocated file.

The latest saved proof checkpoint is `ede5f85a`, after `70289150` and
`dab197d2`. `done_node_table_exact` covers arbitrary completed native calls,
including warm memo states. It derives finite stable tables and exact
independent language. `SourceFreshOrdinaryColdProductivity.prechecked_table`
follows actual root exposure before row extraction. It proves that the
source precheck and minimum lookup detect exactly the finite structural
language. Neither theorem assumes an exact product-row adapter.

The pre-rename audit passed 1,509 jobs and 44,088 theorem dependency checks.
Its log is `/tmp/mcfta-warm-precheck-20261014-audit.log`.
The renamed audit passed 1,509 jobs and 44,088 theorem dependency checks.
Only the three standard foundations remain. The old unused `inputs` warning
remains. The Nix suites passed: 289 core, 209 generator, and 147 refinement
examples. All five updated native probes passed. Fourmolu and cabal-gild
checks passed. The logs are `renamed-audit.log`, `renamed-source-tests.log`,
and `renamed-repros.log` in the evidence directory.
The next composition joins the derived native product language to this
actual prechecked callback, then derives source-key languages and the full
ordered ambiguity scan. Whole Haskell extraction remains outside the proof.

## Current result

The main Sized contract is proved in the source models: exact distinct
accepted terms at each node-count size, finite class evaluation, size-major
enumeration, and both rank/unrank inverse laws. The reference, solver-decided,
and optimized paths have the same required sequence. The latest proofs use
the actual original-state finite map, not an assumption that the state type
itself is finite. **Whole Haskell implementation verification remains open.**

`SourceSizedFiniteKeys*` derives root/child membership from FTA validation,
finite key restriction, exact raw rows, dense canonical order, actual trim
keys, and complete functional and relational bounded-fold readback.
`SourceSizedFiniteKeysDispatch.nativeSized_eq` proves exact raw-map dispatcher
agreement, including errors and all four query functions. The raw synchronous
product minimum calculation and its finite convergence are derived.

`TablePositionCountBound.positions_congr` now proves that bottom-up ranking
reads counts only through the input term's node count. This includes earlier
transition offsets. `TablePositionFiniteEvaluation.finite_rank` constructs
finite count and child-state tables with the exact original rank or failure.
`SourceSizedFiniteKeysRankEvaluation.native_rank_laws` connects that finite
computation to the actual optimized public query and both signed inverse laws.
The state type can be infinite. Concrete Haskell lazy scheduling remains open.

`SourceSizedFiniteKeysNativeLiquid.encoded_correct` proves independent
mixed-sort ambient logical acceptance, original canonical order, complete
bounded prefixes, distinctness, and both signed inverses for the actual raw
fold. `encoded_finite` derives finite outcomes from finite external attempts.
Unknown and unchanged exceptions remain separate. Replies need not be stable.
External Sat/Unsat correctness and completion remain explicit contracts.
See [finite map Sized](lean/notes-sized-finite-keys.md).

## Exact Mu-unfolding budgets

`e8f06e62` defines complete stored meaning at each unfolding bound. A raw Mu
consumes one step. Coherent free-name support and ordinary constructor
normalization are proved. Actual cleanup retains acceptance without requiring
more budget. Actual root-self filtering preserves the budgeted least language.

`19467e4a` proves exact actual finite input derivations at each identical
bound for closed available Original records under every ambient environment.
Erasing the bound recovers independent stored meaning. This budget is
separate from public distinct-term rank.

`9288ec6d` proves exact raw budgets of actual arbitrary nested stored
compilation and simultaneous-substitution plans. Every accepted Mu term has
its exact compiled outer-unfolding plan at a strictly smaller bound.
This result is before execution. Both lexical binder flags consume one raw
step, so the interpretation does not assert exact smart runtime costs.
`50d79bef` proves the actual exact binder finish choice. `35e07971` defines
smart budgets with the existing depth shapes and proves complete semantic
support. `a76a22f1` derives full actual source execution, raw-Mu and empty-local
ordinary-probe readback, and both heap invariants. Actual stored substitution
and unfolding have exact smart-plan meanings. Read
[smart budget execution](lean/notes-smart-budget-execution.md).
`a7b5d94e` proves raw-to-smart plan inclusion for actual captured records.
The existing root/deep shapes supply literal-root lower bounds and deep-change
separation. `InternedGuardedBudgetStoredRefinement.unfold_strict` derives a
strictly smaller budget for every actual returned Mu unfolding.

`9ca74b4d` carries the budget heap through cold/shared execution. Completed
read certificates derive available closed values at every final epsilon path.
The ordered measure `(term size, unfolding budget, stored value size)` proves
finite graph completeness. `trace_table_exact` gives exact independent root
meaning; `trace_table_input_exact` gives the actual initial tagged input
language. `SourceFreshOrdinaryColdSized.source_sized` supplies general closed
construction with exact distinct node-count classes, finite class execution,
size order, and both inverse laws, without preparation or a supplied trace.

`081ce3d1` retains the budget heap through complete native evaluation.
`cold_node_table_exact` and `constructed_node_table_exact` give exact independent
returned-value table language under the existing checked native scope.
The full native two-input language law is now proved for closed original inputs.
The complete native callback/scan compiler composition remains open.
Read `lean/notes-cold-budget-completeness.md` for the completed table boundary.

`2e6fb87a`, `6afdfe00`, and `dac5f26b` now derive literal normalized
ordinary product-row membership and empty-child rejection from actual native
execution. Exact pointwise replay retains guards, child order, domains, and
later cache growth. The law holds at all larger bounds and later valid caches.
Closed native self-intersection also returns the identical record and unchanged
physical/domain machine.

A live ranked witness refutes the proposed general functional Mu row adapter.
For `L = mu x. a | f(a | f(x | a))` and `R = a | f(L | a)`, an actual product
row's child differs from the separate closed intersection of its source children.
`R` occurs in the original graph of `L`. An enclosing `g(L) | g(R)` node gives
two overlapping alternatives. Both smart and raw Mu reproduce the mismatch.
Unary terms through depth 24 still equal the common input acceptance. Those
finite checks do not prove complete language correctness or expose a semantic
runtime defect.

`f04b8261` proves exact graph languages from local related physical rows.
It permits multiple representatives, complete guards, ordered children, and
explicit false-guard or empty-child deletion. Diagonal reuse has exact product
language even for ambiguous source rows. Existing functional rows are a
proved special case. `4d80735a` derives local related rows from actual checked
native ordinary calls at every larger bound and later valid cache.

`ddef16e6` connects related product rows and related roots to the actual
minimum callback, complete ambiguity scan, and literal reference compiler
result. Finite classes, exact distinct guarded node counts, decoder order,
and both rank inverses follow. Physical relation closure and completed row
extraction remain explicit premises.

`NativeProductRowCycleReadout` now proves full unbounded language equality
for the observed finite Mu transcript, distinct literal rows, and a formal
obstruction to the functional adapter with the observed parent/child results.
The live dump and focused comparison validate the exact finite transcript.
They do not verify Haskell extraction. The earlier depth-24 checks remain
finite validation; the stopped generated Lean probes supply no measurement.

The preceding exact relation is a sufficient interface. The later union/self
witness below refutes its general physical derivation. Preserve all three
untracked fixtures. Use separate directional relations for the general
target. Do not assume product language or derive either refuted general
exact-row adapter. Preserve all older theorems for their stated scopes.
Read `lean/notes-directional-union-rows.md`. All workers are terminal.
The later semantic schedule proof now derives full native two-input language
for closed original inputs. It does not require the refuted exact-row interface.

`9b6d9014` now derives actual union and Mu branch witnesses. Union retains
ordered physical child results and exact normalized independent language.
Mu retains the exact extended-domain key, original operand identities,
actual body result, and optional-binder completion in later caches. Its
independent least language and full unfolding equation are proved. These
laws can also be stated through actual successful child-call relations.

`513d2824` derives allocation-free source branch replay from actual checked
native completion at all larger bounds and later caches. Both union operand
orientations and all three Mu branches have their actual child witnesses and
independent language laws. Incoming semantic and independent-language probe
heaps suffice for native Mu; actual evaluation derives their preservation.
No kernel-execution or two-input product-language premise is supplied.

`2083dadf` now proves complete repaired epsilon-origin equations and actual
union constructor origin preservation. Checked native union row extraction
retains exact final-cache member calls, complete guards, and physical child
order in both operand orientations. Incoming semantic/coverage facts and
actual closed row extraction supply the final valid caller machine.

`5a8034f8` establishes a stronger adapter boundary. For `X = {a,b}`,
`Y = {b,c}`, `A = f(X) | f(Y)`, and `U = A | mu x. h(x)`, actual `intersect U A`
returns the identical original `A`. The live raw product cross row needs a
child with exact language `{b}`. Neither returned child has that language.
`UnionDiagonalRowBoundary.no_related_readback` proves that even a
nonfunctional exact `RelatedRows.Readback` cannot describe this root.
The explicit graph has a full correct root-language theorem. The source is
ambiguous; no complete short-circuit scan trace or runtime defect is claimed.
This does not refute a contract restricted to unambiguous graphs.

Separate directional row simulations handle the witness structurally.
`DirectionalRows` proves finite-term inclusion and exact language from both
directions, with full guard implications and ordered children. Exact related
rows remain a proved special case. `DirectionalProduct` derives right
projection and reverse diagonal copies from literal row inclusion.
`UnionDiagonalRowCoverage` proves the complete witness language from these
local simulations. `1f2aa0c6` connects the directional interface to the actual
minimum callback, complete ambiguity scan, compiler equality, finite guarded
classes, and both rank inverse laws. Both physical simulations and completed
extraction remain explicit premises.

`3d9fd615` proves the complete bounded kernel and native product language.
`execute_schedule_replay` uses actual completed calls in one final cache.
Induction derives every recursive correspondence. The semantic bound is
twice the kernel bound. `execute_schedule` recovers the original input view
through actual cache growth. `execute_product` identifies the result with
the finite exact reference schedule. `native_product` derives exact common
finite-term language from actual checked native completion and initial
semantic heaps. No kernel run, recursive correspondence, row relation, or
whole product-language premise is supplied at the native entry.

`0f32ad39` supplies finite actual native product cold tables and stable bounds.
The constructed-source entry derives all heap invariants. Its Sized theorem
proves distinct terms at every node-count size, finite class evaluation,
size-major distinct prefixes, complete rank coverage, and both inverse laws
for the actual product table. Its minimum theorem proves finite convergence,
the exact least common structural size, and the raw-table productivity
Boolean. Guard conjunction, closed original available inputs, domain-cache
validity, and checked `WordRanges` retain their stated scope.

Next compose the complete native overlap callback and finite ambiguity scan
with the derived language and minimum equations. Retain finite extraction
after arbitrary completed warm native calls. The product theorem already
covers those calls; the existential cold-table wrapper currently starts
from `initial` memo state. Connect the actual `nodeEdges` precheck to the
minimum lookup. A positive minimum gives an accepted term and therefore
requires an exposed root edge. An absent minimum gives false for either
precheck result. A literal root-row equality is not required for this logic.

Derive each source-key operand language from actual input cold traces and
resident original closed values. Then prove actual callback equality,
preserve the real constraint precheck and ordered scan, and reuse existing
compiler and Sized sequence theorems. Do not derive either refuted general
exact row adapter or assume the whole product language. Read
`lean/notes-native-product-language.md` before the next proof.
The primary finite-map reference, solver-decided, and optimized Sized proofs
remain. The optimized interned core is unchanged. Whole Haskell source
extraction and runtime representation boundaries remain unverified.

The aggregate audit passes **1,507 jobs and 44,085 theorem dependency checks**,
with only `propext`, `Classical.choice`, and `Quot.sound`. Log:
`/tmp/mcfta-native-product-20261014-audit.log`.
Snapshot: `/tmp/mcfta-native-product-checkpoint-20261014-2056/`.
All 1,878 Lean-tree files are saved. All 1,865 previous files remain.
Only audit imports, two coverage ledgers, and three preceding component
notes changed among those previous files. All earlier proofs and drafts retain
their bytes. The twelve new proof modules and their component note are saved.
No production Haskell code changed. No worker remains active.

## Independent guarded meaning and actual stored compiler

The earlier local preservation snapshot is
`/tmp/mcfta-guarded-native-soundness-checkpoint-20261014-1642/`.
It contains all **1,777 Lean-tree files**, root restart documents, the fixture,
and focused/aggregate logs. All 1,771 files from the previous snapshot remain.
Only audit imports, two coverage ledgers, and three component notes
changed among those older files. All earlier proof bytes and marked drafts
are unchanged. No Haskell source changed in this proof checkpoint.

`b3008aba` adds `InternedGuardedLanguage` and `InternedGuardedSyntax`.
Actual stored bodies and full lexical source syntax have independent positive
least-language interpretations. Probe metadata and the cold reader do not
define these meanings. The interpretations retain full guards and child order.
`meaning_free` proves support from actual coherent cached free names.
Closed captures are independent of ambient reference languages.

`InternedGuardedConstructors` proves actual node/union normalization,
unused/bare-self cleanup, and both raw/smart finish laws for this meaning.
`InternedGuardedSelfFilter` proves actual callback root filtering through its
real union reconstruction. It retains closed candidates and least languages.
`InternedGuardedStoredPlan.encode_language` proves the exact nested compiler
law with coherent slot lookup and nearest local shadowing.
`execute_plan_language` and `unfold_plan_language` derive simultaneous
substitution and outer-Mu plan semantics without an assumed execution law.

`4457307a` proves semantic support for the existing root-profile and free-name
analyses over complete lexical syntax. Pure root profiles bound accepted
languages. Empty-child filtering removes no accepted term. Only surviving
symbolic captures can affect a body language. The ordinary chooser is fresh
for those captures; it need not be fresh for every supplied unused input.
The next reserved interned identity is also fresh for surviving captures.

`e46d3f9e` proves `InternedGuardedExecution.build_language` and `closed_heap`.
The joint source induction derives the semantic probe heap and exact returned
language through both probes, fresh completion, cleanup, and canonical hits.
Every stored Mu has the least language of its exact ordinary probe under
binding of `.uninterned (ordinaryLevel depth)`. A hit uses its complete stored
payload and requested probes. It does not use a discarded candidate body.
Pending outcomes retain the same heap invariant. No execution contract is
assumed. `closed_language` gives the independent language of a completed
closed source expression under arbitrary guards and ambient languages.

`InternedGuardedStoredExecution.execute_checked` composes actual execution
with the exact stored compiler. It proves capture-free simultaneous
substitution language and semantic heap preservation. `unfold_checked`
proves that actual outer-Mu unfolding preserves independent language for
arbitrary available records. No preparation or literal reconstruction
identity premise is used.

`e1baab1e` proves the new independent probe heap through actual bounded
cold worklists and public `nodeEdges` reads. `Trace.guarded_heap` retains it
through every shared row read. `constructed_cold_finite_guarded` derives the
initial invariant from completed closed source construction and retains both
the open-depth and independent-language heaps in the finite final table.
This proves heap propagation. Full independent graph/table language transport
remains open. The later native checkpoint below proves native heap propagation.

`650c3f05` proves independent-language soundness of actual growing-cache
cold worklists and public reads. Each returned guarded edge is included in
one original root language. `SourceFreshOrdinaryColdGuardedSoundness` lifts
this law by finite-term induction to replayed rows, the final repaired graph,
and the actual ascending table. The visited check is sound for this direction.
These are inclusion theorems, not completeness or full language equality.

`b7201597` proves the independent least-language law for actual optional
intersection binders at their repeated-pair reference. The unused branch has
the same least language. `Bounds.guarded_heaps` follows actual native work,
checked memo hits, nested source bodies, completion frames, and continuations.
`NativeColdGuarded.cold_node_table_sound` and `constructed_node_table_sound`
derive finite stable native cold tables with the independent semantic heap.
Their accepted terms belong to the independent language of the returned
physical value. Checked WordRanges, closed Original inputs, and complete
initial caches retain their stated scope. This does not yet identify the
returned value language with the intersection of the two input languages.

`0258ae86` proves `SourceRecursiveIntersectionGuardedInput.original_meaning`.
Original payloads have equal guarded stored and copied lexical meanings.
`input_exact` identifies closed available original records with their exact
finite tagged input derivations. This derives the connection to the existing
input specification. No copy-language contract is supplied.

Next prove completeness of the actual final repaired graph and cold table
for independent meaning. Then derive physical `ProductReadback.members`,
`.rejected`, and `product_exact`. The exact final-cache graph/table law is
already proved, but execution correspondence alone does not supply this
transport. Keep cache growth, availability, and leastness explicit.
Read `lean/notes-independent-guarded-language.md` for the exact next target,
the proved probe invariant, and all remaining scope distinctions.

## Native heap propagation and exact final-cache guarded language

`9a0df4cb` proves `SourceRecursiveIntersectionOpenDepthEffects` and
`SourceRecursiveIntersectionOrdinaryWork`. Actual optional binders retain
the body/probe heap through their exact repaired compilation. All ordinary
compiler jobs add no Mu. `Bounds.open_depth_heaps` follows actual nested
native evaluation, checked memo lookups, source bodies, completion frames,
and continuations. It retains both semantic and body/probe heaps.
`NativeColdTable.cold_node_table` and `constructed_node_table` derive a finite
repaired cold table after successful first native execution. Complete caches,
closed Original inputs, and checked WordRanges retain their stated scope.
No preparation, output trace, or finite future cache is supplied.

`e70160d6` adds `MergedFreshOrdinaryGraph`. Its Mu epsilon step uses the actual
repaired stored executor. `MergedFreshOrdinaryExposureCertificate` derives a
finite complete constructor certificate for allocation-free completed reads.
`ExposureOrigins` proves that every returned edge has a repaired epsilon
origin in each later cache. `ExposureCoverage` proves the reverse inclusion.
`ExposureLanguage.actual_exact` retains complete guards and ordered children.
`SourceFreshOrdinaryColdTableLanguage.trace_table_language_final` identifies
the complete finite table with this repaired graph in its actual final cache.
`cold_table_language` supplies the finite trace and stable bounds.
The native cold-table theorems also return this exact guarded-language law.

The final-cache qualification is essential. These theorems do not equate
the final repaired graph with an initial graph that discards allocated caches,
or with independent intended Mu semantics. The later `b3008aba` compiler checkpoint defines independent meaning and
proves exact stored-plan semantics. Actual source construction and canonical
hit language preservation remain open. Follow `substitutionPlan`; literal identity reconstruction
for arbitrary raw binders is refuted. Then derive physical
`ProductReadback.members` and `.rejected` and apply `product_exact`.
The earlier prepared graph uses the old executor; its preparation premise
remains valid in its stated fragment.

Current audit: 1,417 jobs and 43,451 theorem dependency checks. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-guarded-input-native-soundness-20261014-audit.log`.

## Finite general final tables

`3dc8f856` adds `SourceFreshOrdinaryColdTable`. Every first-written row is
retained. `Trace.closed` declares every nonempty child in the final map.
`Trace.replayed` gives an available closed root and an identical allocation-
free final-cache read for every stored row. `keys_exact` uses the actual final
issued counter and proves a finite distinct exact map domain. `keys_ascending`
proves the native ascending identity order. `cold_table` combines these facts
with the actual finite trace, stable outer/read bounds, semantic heaps,
coverage, the body/probe heap, growth/history, and resident closed edges.
No preparation, fixed future cache, or supplied trace is assumed.

The aggregate audit passes 1,417 jobs and 43,451 theorem dependency checks.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Log:
`/tmp/mcfta-guarded-input-native-soundness-20261014-audit.log`.
This earlier result proves finite table structure and exact row readback.
The later native and repaired-language checkpoints below also prove native
heap propagation and final-cache guarded row language. Initial-source
language transport and physical product language remain open. The earlier prepared graph uses the old stored
executor. Do not remove its preparation premise from termination alone.

The latest restart snapshot is
`/tmp/mcfta-independent-guarded-checkpoint-20261014-1549/`.
It contains 1,761 Lean-tree files, root restart documents, the retained fixture,
and the new audits. Its manifest compares all 1,754 previous checkpoint files.
No file is missing. Only audit imports, coverage ledgers, and three component notes changed
among those files. All other
proofs and all marked drafts remain byte-identical.

## General finite shared traversal

`68e790f0` adds `InternedFreshMuUnfoldBudget`. Counts use actual unfinished
canonical Mu records by body degree. Completed unfoldings are settled, and
actual allocation-free replay preserves settled calls after cache growth.
`unfold_progress` gives strict finite-vector decrease or exact cache equality.
`MergedFreshOrdinaryColdBudget` retains that result, the body/probe heap,
and the maximum degree through every completed actual closed read.

`SourceFreshOrdinaryColdSharedTermination.complete` follows the actual shared
worklist. A changing cache reduces the unfinished-degree vector. An unchanged
cache lets the new row consume an unvisited issued identity. Empty and known
values reduce pending length. `cold_finite` derives an actual finite trace
and uniform stable outer/read bounds. `constructed_cold_finite` derives all
heap premises from actual repaired empty-cache source construction.
No preparation, `NoNewMu`, finite future inventory, or supplied trace is
assumed. The later `3dc8f856` checkpoint derives exact finite map readback.
The later checkpoints prove native body/probe heap propagation and exact
final-cache guarded row language. Initial-source language transport and
physical product language remain separate obligations.

## Finite general repaired cold reads

`6132e4f2` proves a dynamic budget over actual canonical Mu identities.
`InternedMuDepthInventory` handles duplicate issued reservations and growing
inventories. `MergedFreshOrdinaryColdTermination.collect_complete` proves
finite actual closed worklist execution in complete semantic caches with the
body/probe heap. New Mu and open probe allocations are permitted at lower
degrees. No preparation, fixed future cache, trace, or progress contract is
supplied. `read_closed` proves public completion with exact edges and cache,
semantic/coverage and body/probe heap preservation, resident closed edges,
and stability at all larger bounds. `constructed_read_closed` derives all
cache premises from actual repaired empty-cache source construction.

Audit: 1,417 jobs and 43,451 theorem dependency checks. Log:
`/tmp/mcfta-guarded-input-native-soundness-20261014-audit.log`.
General shared traversal is proved below the current source heap boundary by
`68e790f0`. Its unfinished-unfolding budget uses actual allocation-free replay. Native propagation of the body/probe heap is now proved by `9a0df4cb`.
Initial-source language transport and physical product language remain open. See
`lean/notes-stored-plan-binder-depth.md`.

## Repairs and retained counterexamples

- **`73223201`: quantified SMT name capture.** Liquid Fixpoint mapped raw
  names `1` and `fix$1` to the same symbol. A false quantified entailment
  returned Yes. The adapter now uses one injective safe encoding for all
  declarations, variables, function heads, binders, and the default value name.
  The codec, serializer control, complete quantified meaning, preflight, and
  public liquid composition are proved. Native and Lean counterexamples
  remain. See [solver names](lean/notes-solver-name-encoding.md).
- **`a8b32869`: weighted-search midpoint overflow.** The former Int index sum
  can wrap even when both indices fit. The repair uses
  `low + (high - low) quot 2`. The repaired full search requires only a
  representable array length. The historical 64-bit example is an arithmetic
  boundary, not a feasible allocated-array failure. See
  [weighted selection](lean/notes-quickcheck-frequency.md).
- **`17b21453`: cyclic custom-key order qualification.** Equal complete sort
  keys retain source row order. Noninjective custom symbol keys can exchange
  ranks when interning order changes. Counts and both inverses still hold.
  Source comments and Lean/native evidence now state the exact limit.
- Earlier source repairs and counterexamples remain, including direct-row
  Sized dispatch, implicit ambient fresh-name capture, recursive child unions,
  fresh ordinary probes, and the disproved saturated-merge shortcut.

## Other completed source bridges

`SourceInternedRows*` proves finite shared row traversal, ordered constraints
and child readback, guarded language, validation, and issued-cache exposure.
Dense numbering and finite-key minimum sizes are derived. Cyclic query and
sampler records have exact counts, decoder positions, reciprocal masses,
normalization, support, PMFs, and sampled rank replay. No arbitrary sampler
normalization premise remains. Distinct terms, accepting runs, generator
members, and aggregated PMF keys remain separate concepts.

`SourceInternedIntersectionDispatch*` proves ordinary native empty/self/order
control, actual constructor effects, finite completion, and completed memo
results with concrete execution provenance. `SourcePhysicalSharedRows*`
connects actual cache readback and traversal to the minimum callback. The
finite plain callback detects exactly the original operands' shared terms
without a product-row or global child-meet premise.

`SourcePhysicalRecursiveRows*` proves actual repaired unfolding, precise cache
effects, stable replay, and shared rows for `mu x. (base | step x)`. It derives
that fragment's independent language of finite Chain terms from an available coherent
stored knot. `SourcePhysicalRecursiveConstruction` now supplies that knot from actual repaired
empty-cache construction for arbitrary base and step symbols. It derives exact
records, counters, coherent availability, constructor replay, unfolding, and shared
rows. `SourcePhysicalRecursiveSized.source_sized` connects those source-derived
rows to one distinct term at every positive size, finite class evaluation, distinct
size-major prefixes, and both inverse laws.

`InternedFreshOrdinaryFirstOrder*` now derives repaired first-run completion
and the prepared heap for one binder with arbitrary finite binder-free trees
and unions. `SourceFirstOrderExposure.source_read` derives finite actual cold
row exposure with exact cache effects and original guarded language.
`MergedPreparedReaderEffects` proves that all later reads in a warmed cache
retain that exact cache. `SourcePreparedSharedRows*` derives finite shared
traversal and exact guarded language through ordinary, Mu, and union identities.
`SourceFirstOrderSharedRows.source_sized` connects actual construction and
explicit warmup to exact distinct node-count classes, finite evaluation,
size-order prefixes, bounded coverage, and both inverses. Warmup is a proof
construction. Equality between warmup and native cold allocation orders remains
open, as do nested binder construction and native cyclic product rows.
See [first-order shared rows](lean/notes-first-order-shared-rows.md) and
[physical intersection](lean/notes-physical-intersection-rows.md).

`SourceColdSharedRows*` now derives the actual stateful cold output table and
its exact original guarded language. `SourceColdUnfoldBudget` tracks unfinished
Mu unfoldings in the finite initial record inventory. A read either reduces
that budget or retains the identical cache. Unvisited identities and pending
work supply the other two termination measures. `cold_finite` derives a finite
actual trace and stable executable bounds for every closed available root in
a prepared cache. No warmup, fixed input heap, or supplied trace is assumed.

`SourceFirstOrderColdSized` derives the prepared cache from actual repaired
first-order empty-cache construction. Its cold table has exact distinct
node-count classes, finite evaluation, size-order prefixes, bounded coverage,
and both inverse laws. `Trace.native_correct` connects the actual returned
rows to the canonical public reference API and both signed inverse laws.
`Trace.liquid_correct` connects encoded solver-decided folds to original
physical ambient logical meaning, finite classes, canonical order, bounded
coverage, and both signed inverses. Finite external attempts give finite
outcomes, including Unknown and failures. Validation and external solver
contracts remain explicit.

General open nested binder construction, native cyclic intersection product
rows, general pending thunk completion, and concrete runtime correspondence remain open.
See [cold shared rows](lean/notes-cold-shared-rows.md).

`42ce3d8a` completes the cached-depth/deep heap induction for arbitrary nested
source syntax with literal lexical inputs. `InternedFreshOrdinarySourceDepth`
derives exact returned emptiness, cached Mu depth, deep names, and the decoded
heap through every outcome. Closed execution derives that heap even when
pending. Completed callbacks with the same literal captures have identical
cached depth for any supplied names. No recursive depth/deep premise is supplied.

`d0083f37` proves actual repaired ordinary-level agreement when projected
literal capture lists agree. `ordinaryNames` keeps each ordinary reference
level and maps all other kinds to Depth. `callback_level` derives both cached
depth and free-name-bound equality.

`d2ebaddf` retains exact captured suffixes along the actual earlier route and
proves projected agreement from outer crossings to inner crossings. The
ordinary choices agree. This contradicts the pending encounter's required
live ordinary mismatch. `ClosedCompletion.closed_complete` proves that every
source expression built from empty captures and caches returns a complete
value and its exact final cache. No supplied termination or preparation
premise is used. `f095aa16` extends this to literal captures in any complete
cache with a full source context and decoded depth heap.

The later arbitrary-record and native-success checkpoints below extend these
results to mixed captures and derive successful native first execution under
explicit checked words. Output preparation and physical product rows remain
open. See [successful native execution](lean/notes-native-successful.md).

`EqualityNestedUnaryAncestorRoot*` composes actual projections, target merges,
both ancestor edits, and the root identity stop. The fixed unary/two-atom,
one-class fragment terminates within `4 * (left + right) + 2` passes and
retains exact output/cache for additional fuel. All marked drafts retain their
bytes. See [the equality root proof](lean/notes-equality-nested-unary-root.md).

Earlier bounded import, liquid denotation, finite reconstruction, observation
groups, weights, sampling, PMFs, CPS enumeration, union-find, and memo-domain
proofs remain. The detailed notes and API coverage ledger record their scope.

## Recursive intersection control

`SourceRecursiveIntersection*` now derives physical guard precedence,
complete tagged operand order, sorted actual cutoff identities, canonical
domain overwrite, and exact original Mu record lookup. The actual Mu
binding list derives canonical domain-cache allocation and complete
physical bindings. `decision_encoded` and `physical_step` connect the
complete selector to the existing semantic executor. Physical-to-view
closedness equations remain explicit. See
[recursive control](lean/notes-recursive-intersection-control.md).

`InternedFreshOrdinaryPlanEquivalence` and
`InternedStoredSubstitutionRebind` derive full nested stored-plan rebinding
with identical outcomes and caches. `SourceRecursiveIntersectionMaybeMu`
now derives the actual substitution callback and repaired constructor
equation, source facts, physical histories, and replay. Prepared callbacks
and probes complete at arbitrary current caches. `pending_exact` identifies
the exact installed post-probe key with an absent payload. Complete cache
coverage gives successful prepared first-run execution. The later arbitrary-record
completion theorem removes that preparation condition in complete semantic
caches. Result preparation, product language, and product-row readback remain open. See
[optional binder effects](lean/notes-recursive-intersection-maybe-mu.md).

## Stateful recursive caller

`SourceRecursiveIntersectionKernel*` now composes all physical branches,
canonical domain effects, original Mu lookup, ordered union/child/row
calls, guarded edge construction, and actual optional-binder effects.
`execute_checked` derives complete cache facts, both histories, and
available successful results. `execute_stable` retains every non-exhausted
outcome and its exact returned caches at all larger bounds. Actual ordered
traces derive literal symbols, conjoined guards, actual child values, and
canonical surviving parent rows. The bounded recursive kernel remains
uncached. Completed native node/edge effects and successful stable first-run
bounds under checked words are derived below. Physical product-row
correspondence and product language remain open. See
[recursive caller](lean/notes-recursive-intersection-kernel.md).

## Completed replay and memo provenance

`SourceRecursiveIntersectionReplay*` derives complete guarded kernel
replay after constructor/domain growth. The value is identical and both
later caches remain unchanged. Every larger bound gives that same result.
`SourceRecursiveIntersectionMemo` uses actual checked flat triples, shifted
domain identities, nonnegative first-key bounds, and ordered tagged
operands. Equal checked keys identify the same complete physical request.
A swap of unequal operands has a distinct key. Actual completed execution
constructs memo provenance. Initialization, growth, first-writer insertion,
and memo hits derive current availability and finite stable kernel replay.
`SourceRecursiveIntersectionEdgeMemo` now gives the same concrete provenance,
current residency, and stable replay for ordered raw row keys.

`FlatMemoThunk` and `SourceRecursiveIntersectionThunks*` now derive typed
pending publication, exact captured request identity, recursive pending
observations, demand, completion, and retention through source growth in
separate node and edge families. Completed native lookup and demand agree
with concrete stable guarded kernel replay without effects. Unresolved source
placeholders bypass memoization. Actual kernel execution completes the original
running cell at its exact returned source machine. These completion bodies
still use uncached recursion. See
[recursive memo](lean/notes-recursive-intersection-memo.md) and
[native memo thunks](lean/notes-recursive-intersection-thunks.md).

`SourceRecursiveIntersectionCode` and `SourceRecursiveIntersectionCompile`
now compile every source branch to explicit effects and recursive requests.
`compileNode_exact` and `compileEdge_exact` derive exact guarded kernel
agreement for arbitrary recursive node callbacks, including cache effects
and failures. `SourceRecursiveIntersectionNative*` now threads both memo
families through recursive body execution. Misses publish before bodies run;
busy hits retain their code and caches. Request steps, continuation composition,
finite traces, and physical-effect retention are checked. Pending construction
retains its actual installed key, new heap, and original continuation. Whole
guarded kernel correspondence and memo provenance at completion frames are
now derived below. Sufficient first-run bounds and product language remain open. See
[native recursive execution](lean/notes-recursive-intersection-native.md).

## Actual native completion and frame ownership

`SourceRecursiveIntersectionNativeTraceSplit` derives exact body and
continuation segments from actual traces. `completed_iff_evaluation` proves
that actual finite completed native runs and finite nested evaluation trees
agree in both directions, including all returned caches. No kernel execution,
purity, language, or completion-provenance premise is supplied.

Every compiled source body excludes explicit native completion instructions.
`SourceRecursiveIntersectionNativeRunning.done_retains` proves that actual
completed source bodies preserve structural memo `Shape` and all enclosing
running requests. The original node or edge cell remains running until its
original frame stores the actual returned value. This establishes structural
frame ownership. That structural theorem alone does not prove semantic
provenance or a sufficient first-run bound for every input.
See [native completion](lean/notes-recursive-intersection-completion.md).

## Completed native semantic correspondence

Physical continuation safety is now derived for every compiled source branch.
`SourceRecursiveIntersectionNativeCorrectness.Bounds.correct` derives final
strong source/memo validity, exact physical/domain growth, returned record
properties, and stable guarded kernel meaning from actual native evaluations.
The explicit word-bound certificate adds only checked ranges at memoized
requests. New `Produced` facts come from actual compiled body execution and
its original completion frame. No kernel execution, purity, or completion
provenance is supplied at new finishes.

The public native node and edge theorems start from actual bounded native
completion. They derive the same value and exact physical/domain caches as
the guarded kernel, current availability/residency, strong memo invariants,
and concrete provenance. `cold_node_correct` starts with empty memo tables
and an actual valid physical input cache. Actual completion and checked word
bounds remain premises. Available open results can be recursion placeholders.
General first-run termination, new-body preparation, and product-row language
remain open. Physical input-view equations are now derived below. See
[native correctness](lean/notes-recursive-intersection-native-correctness.md).

The original physical input view now derives exact tagged payload readback,
cached free-name equations, original-input closedness, and physical branch
agreement with the semantic schedule. Original syntax has an explicit
complete-reference premise. General source construction has not yet been
proved to supply it for every result. Copied syntax has exact free-name
membership, and closed inputs have closed copies. Independent copied-language
equivalence is now proved in both directions below.

Actual payload sizes derive strict body/row/member ranks and local schedule
decreases. A finite tagged carrier comes from the actual issued counter.
Closed-root reference traversal retains original available records and stays
inside that carrier. It also stays at the root rank or below it. Both roots
therefore give a finite pair carrier. No completed intersection trace is
supplied. The carrier does not declare incompatible tags valid at one
identity. These proofs do not yet derive a sufficient first-run native bound.
See [physical input view](lean/notes-recursive-intersection-input-view.md).

Canonical representative readback and both independent copied-language
directions now derive the entire `FiniteInput` interface. Completeness uses
finite derivation-rank induction at least binders. No copy-language contract
is supplied. The semantic schedule has one sufficient finite bound and an
exact product language for actual closed original physical inputs.
`source_schedule_total` states this product using the actual original copied
least-language meanings. Original complete-reference syntax and availability
remain explicit input premises. Actual source-cache growth retains all old
input-view fields on that valid domain.

These results do not yet give sufficient native memo-driver bounds or exact
physical returned product rows. New binder construction and preparation
remain separate obligations. See
[exact original inputs](lean/notes-recursive-intersection-input-exact.md).

Least successful semantic fuel now gives a request-specific progress measure.
Every immediate branch and ordered edge child strictly decreases it.
Actual canonical domain allocation retains the same exact execution and
least bound as semantic overwrite lists. Initial certificates come from
actual closed original physical inputs. No child execution is supplied.

Actual completed native source bodies now leave no new running cells.
Their original completion frames restore the caller's running cells.
`ActiveAbove` has initialization, publication, physical-effect, start, and
completion-frame lemmas. Published handles cannot be absent. Busy is excluded
under checked keys, strong source validity, active bounds, and the request's
strict decrease. The all-branch compiler invariant and finite native driver
induction are now proved below. See
[request progress](lean/notes-recursive-intersection-request-progress.md).

`compileNode_below` and `compileEdge_below` derive strict request limits and
original scope through every branch and actual continuation. Successful
semantic branch actions exclude unsupported control, incompatible payloads,
and unbound references. Original binder readback excludes missing payloads.
`WordRanges` checks machine-word bounds on actual finite yielded prefixes.
It assumes no completed native run or sufficient fuel.

`code_terminal` closes smaller-body observations by strong bound induction
and structural code induction. It preserves strong source/memo validity after
returns and restores caller bounds through original finish frames.
`cold_node_terminal` starts from actual closed original available roots and
empty memo tables. Under checked words, it derives a finite return or exact
pending constructor. No source failure, absent handle, busy cell, or yielded
outcome satisfies `ReturnsOrPending`. Pending retains its key, code, and state.
No native completion, callback execution, or new provenance is supplied.
`done_correct_of_ranges` derives guarded kernel correspondence for a return.

This is not yet successful completion. Exclude pending constructors at the
actual reached bodies and caches. Existing completion requires payload
coverage and `PreparedWithoutMu`. Closedness alone does not establish this
condition for open nested binders. General output preparation and physical
product-row correspondence remain open. See
[finite native observations](lean/notes-recursive-intersection-native-finite.md).

Payload coverage now holds on completed repaired builds with arbitrary nested
syntax and on completed actual optional binders. Actual native yielded prefixes
retain their incoming coverage. A bounded constructor block derives its exact
optional-binder source site and pre-call heap. Earlier actual completed source
construction in empty caches supplies complete coverage there. Arbitrary
supplied heaps still require incoming coverage.

A complete-cache optional binder cannot report an incomplete final hit after
both probes return. Its pending result must occur in the Depth callback,
ordinary callback, or fresh body callback after a genuine miss.
`InternedFreshOrdinaryEncounter` derives the full repaired nested encounter.
`InternedFreshOrdinaryOldCall.encounter_old` recovers the earlier ancestor
reservation and both exact original available probe records. The current
callback captures the newly reserved reference. Both old probe boundary lists
exclude it. The ordinary callback uses `ordinaryLevel depth`.
`SourceRecursiveIntersectionMaybeMu.pending_encounter` connects the actual
source call to this witness without an assumed callback execution or probe
relation. Signature checks confirm the repaired executor.

`InternedFreshOrdinaryActiveOrigins`, `ActiveEncounter`, and `ActiveSite`
now retain the exact actual descendant path for arbitrary captured values.
Canonical readback derives both original probe records. Their free-name
observations imply equal capture memberships and exclude the ancestor's fresh
name from live captures. `SourceRecursiveIntersectionMaybeMu.active_pending_site`
derives the full witness from actual execution under complete coverage, body
availability, and an incoming repaired semantic context. General native prefix
preservation of that semantic context remains open.

`SourceRecursiveIntersectionOpenBodyBoundary` refutes preparation preservation
at all reached native bodies. Two actual repaired closed original inputs built
from empty caches reach an unprepared optional-binder body after 22 steps.
The initial heap has complete coverage and the full repaired semantic context.
Bounded native execution nevertheless returns. This is a counterexample to a
proof invariant, not an implementation defect. The finite Boolean preparation
test is proved equivalent to `PreparedWithoutMu`. All concrete observations
use kernel reduction.

`InternedFreshOrdinaryActiveReplay.Origin.completed_representative` now
derives an earlier completed source route inside the actual raw Depth build.
It retains ordinary choices and uses Depth for fresh choices. Arbitrary
original captured values remain unchanged. Each crossing retains its actual
source body and repaired ordinary level. `InternedFreshOrdinaryEarlierPair.Site.earlier_pair`
derives both earlier probes and a completed request whose payload survives
to the ancestor cut. Its pair differs from the later original ancestor pair.
No earlier completed callback or route witness is supplied.

`InternedFreshOrdinaryLiveInputReplay.build_same` now proves exact completed
record comparison for arbitrary fixed captured values and varying references.
The symbolic profiles derive actual child liveness. Equal surviving varying
inputs suffice in an actual coherent common cache. Discarded computations can
have different cache effects. `LiveInputReadiness.not_pending_after_probes`
derives the later completed request from an earlier completed binder and the
later actual probes. Full semantic contexts and source cache growth remain
explicit. No later binder completion is supplied.

`InternedFreshOrdinaryJointMismatch.Site.mismatch` derives a changed live
ordinary crossing on the same actual earlier route. Fresh interned changes
contradict the original Depth probe's issued-name bound. The ordinary witness
retains both earlier probes, their different pair, a completed request, and its
payload before the ancestor reservation. The current level is free in the old
ancestor Depth probe, is strictly below its selected `ordinaryLevel`, and comes
from an actual earlier captured value. `active_pending_mismatch` connects this
result to the actual optional-binder call without supplied mismatch witnesses.

`InternedFreshOrdinaryRootEncounter.complete_mismatch` now derives the original
source path and live mismatch at the same exact active origin. `ProducedAt`
retains an actual earlier producer, completed Depth callback, selected ordinary
level, full source context, chronological growth, and descendant path to the
active binder. The captured prefix is strictly shorter. Its exact suffix
relation follows from the path. Closed pending execution in empty caches
derives these producers for every ordinary capture in the ancestor Depth probe.

The actual optional-binder bridge now derives the original lexical root and
an initial-body free-name or shorter-producer alternative. An ordinary name in
the actual stored leaves is free in the original body. `pending_mismatch_producers`
excludes that alternative under explicit absence of ordinary free names in the
body. This condition is not yet derived at every native site. The incoming full
semantic context also remains explicit.

`0f665004` strengthens the rooted induction with `StoppedReached` and
`StoppedRooted`. Every enclosing callback retains the same exact pending key
and final cache. `complete_stopped_mismatch` preserves the selected origin.
`PendingProducedAt` derives the shorter producer's actual pending ordinary
callback and whole binder outcome from its completed Depth probe. It retains
the exact captured suffix, strict length bound, original context, and cache
history. The actual optional-binder bridge keeps the same initial-body
alternative and explicit absence condition. All previous history results remain.

The producer-descent alternative still has no second observation of that same
shorter producer body. The strict prefix bound alone gives no contradictory
recursive descent. Closed/literal source pending exclusion is now proved by
actual paired-route level agreement instead. The remaining native extension
has arbitrary fixed captured records and requires actual context and decoded-
heap preservation.
`InternedFreshOrdinaryProducerPathBoundary` verifies that the repaired executor
can retain a live nested capture while the enclosing producer returns empty.
Result liveness does not follow from a descendant path. Both actual pending-site
probes and chronological source equations must remain in the next proof.
Normalized output absence does not establish
independence of the original memo key. Prove a broader open
nested constructor invariant instead of universal preparation preservation. See
[constructor coverage](lean/notes-recursive-intersection-constructor-coverage.md).

## Arbitrary-record constructor completion

`InternedRecordDepthShape` derives exact decoded inputs from coherent available
records. Root alternatives and deep names remain separate, including mixed
unions. `InternedRecordDepthExecution` proves the full source induction with
arbitrary captures. Each returned record has the predicted emptiness, cached
depth, and deep-name membership. Every outcome retains the decoded depth heap.
The literal-source driver is now a specialization.

`InternedRecordDepthLevels` derives actual ordinary-level equality from equal
projected record shapes. `InternedRecordDepthRoutes` follows both scoped routes.
Their selected ordinary levels agree, which contradicts the pending encounter.
`InternedRecordDepthCompletion.source_complete` derives successful actual
source execution for arbitrary syntax and captured records from a complete
coherent decoded semantic cache. No prepared-body or supplied termination
premise is used.

`SourceRecursiveIntersectionMaybeMuCompletion.complete_decoded` applies this
result to actual stored-body substitution and arbitrary available leaves. It
returns successful optional-binder execution and the exact context, decoded
heap, complete coverage, available result, growth, and issued history. Proof
checkpoints: `92746870`, `e543e630`, `cdcbb881`, and `e4a011e8`. The native caller
still needs semantic-context/depth-heap preservation at its reached source
sites before constructor pending can be excluded. See
[record completion](lean/notes-record-depth-completion.md).

## Successful native first-run execution

`ec611802` proves the actual emitted operations and all compiled source
branches preserve semantic heap conditions. `Bounds.semantic_heap` follows
completed nested native evaluation, checked memo keys, and original frames.
`f7b842e4` splits an actual unfinished appended run into a blocked body or an
actual completed body followed by a blocked continuation. Strong induction
on the finite native bound excludes pending constructors. Each reached
optional binder has its derived available body and complete semantic heaps.
The proof does not assume successful native execution or a no-pending callback.

`NativeSuccessful.cold_node_complete` combines this with the existing finite
terminal theorem. Closed Original available inputs now derive successful
finite native execution in complete semantic caches under explicit
`WordRanges`. The result retains exact caches, strong memo provenance,
guarded kernel meaning, semantic heaps, complete coverage, and identical
value/cache at every larger bound. `constructed_node_complete` derives the
semantic and coverage premises from actual repaired closed source construction.
Output preparation, a finite final cold table, physical product-language
correspondence, and concrete runtime/word-range justification remain open.
See [successful native execution](lean/notes-native-successful.md).

## Actual stored support and general single unfolding

`018f1712` derives exact used lexical positions for actual returned free names.
Stored-plan support connects those slots to original free names outside every
local binder. Actual `MaybeMu.free_support` retains only original body free
names and removes the selected intersection name. Normalization can remove
additional names.

`2ac3ca41` proves that every captured leaf is closed or a reference. Actual
repaired substitution can return a free name only from the replacement of an
original free reference. Arbitrary stored substitution and single Mu unfolding
now complete without preparation in complete semantic caches. They retain
exact cache effects, semantic contexts/depth heaps, complete coverage,
availability, and histories. A closed available record has a closed unfolding.
Native output closedness is now proved below. Repeated repaired cold-reader
termination, final cold tables, and physical product rows remain open. See
[stored support and unfolding](lean/notes-stored-free-unfold.md).

## Native result scope and general repaired cold reads

`59d637f2` proves recursive result free-name scope from actual source
execution. Returned names belong to incoming seen pairs. Mu calls extend
that domain, and actual optional binders remove their pair. Exact guarded
kernel meaning transfers the result to native execution. Empty-domain
native returns are closed. `d935fe35` derives original payload syntax from
closed coherent availability, without an output-syntax premise.

`d87a4324` proves bounded repaired cold-reader effects without preparation
or `NoNewMu`. Every outcome retains complete semantic heaps, coverage,
growth, and issued history. Done results contain resident edges with closed
children. Pending constructors and unresolved references are excluded.
`cold_node_read_effects` supplies these premises from actual successful native
first execution. Exhaustion remains possible. General repeated traversal,
finite final cold tables, and physical product language remain open. See
[native output and cold effects](lean/notes-native-output-cold-effects.md).

## General cold replay and rejected termination measures

`6e9804df` proves general repaired stored/unfolding replay, bounded reader
validity and growth, exact ordered-row replay after final-cache growth, and
larger-bound stability. `nodeEdges_replay_stable` combines both forms of
stability. These results require actual completed reads and only initial
cache validity. No preparation, closed-input, or semantic-heap premise is
needed for replay. No successful bound is supplied for unfinished reads.

`0534aad8` retains an actual source-built closed example:
`mu x. mu y. f(x,y)`. One repaired unfolding creates a previously absent Mu
and increases cached depth from 2 to 3. The node counter grows from 13 to 17.
The actual cold reader still finishes. `not_noNewMu` and `depth_increases`
exclude the initial Mu inventory and descending cached depth as general
termination measures. Kernel evaluation proves the Lean observations.
The live Haskell Nix reproduction confirms the depth increase, closedness,
different result identity, and successful one-edge read. Log:
`/tmp/mcfta-cold-measure-native-20261014.log`. See
[native output and cold effects](lean/notes-native-output-cold-effects.md).

## Direct repaired shared traversal and first-order Sized

`c410bc0a` adds `SourceFreshOrdinaryColdSharedRows`. The shared worklist
calls the repaired reader directly. `Trace.finite` and `collect_trace`
connect exact finite relational and executable runs. `of_prepared` and
`Trace.to_prepared` transfer earlier prepared traces in both directions,
with identical tables and caches. `Trace.correct` retains complete semantic
heaps, coverage, row provenance, growth/history, and closed children for
arbitrary finite repaired traces. It requires no preparation or `NoNewMu`.
`cold_finite` derives finite prepared repaired traversal without a trace.

`SourceFirstOrderFreshColdSized.source_sized` composes actual repaired
empty-cache first-order construction and the new repaired shared worklist.
It derives exact finite node-count classes, distinct size order, complete
bounded prefixes, and both inverse laws. No warmup or trace is supplied.
The same prepared trace bridge retains existing native and solver-decided
table compositions. General nested finite trace existence remains open.
See [repaired cold shared rows](lean/notes-fresh-cold-shared-rows.md).

## Raw-binder identity substitution boundary

`75c50b4d` retains `InternedStoredRawIdentityBoundary`. Actual closed source
construction builds an outer binder whose open stored body contains an
unused raw inner Mu. Replacing the outer name with itself changes physical
identity and cached depth from 1 to 0. Free-name lists remain equal.
Kernel evaluation proves the exact observation. Live Haskell also reports
`(False,1,0)`. Log:
`/tmp/mcfta-identity-substitution-native-20261014.log`.

The earlier unqualified physical identity postcondition in `Type.hs` was
false for this raw-binder case. PR #121 now qualifies the source comment.
Runtime behavior did not change. The qualified smart-binder identity law
remains a separate unproved source-correspondence target. `substitutionPlan`
rebuilds open Mu records with smart `createMu`. It intentionally does not use
the cached pattern-synonym matcher fast paths. A general physical closure
proof must account for smart cleanup. No language change is claimed.
See [repaired cold shared rows](lean/notes-fresh-cold-shared-rows.md).

## Repaired source dependencies and exact physical binding keys

`8598886f` derives full repaired plan equivalence from agreement on the
original used lexical slots. Repaired stored execution now has exact
free-binding congruence, restriction, and replay after growth. Pending
outcomes and cache effects are included by the congruence theorem.

`InternedFreshOrdinaryBindingKeys.key_agree` recovers full available values
from ordered optional physical identities in one coherent cache.
`execute_key` and `execute_key_replay` derive the exact computation and
allocation-free replay. A finite current-cache inventory covers every key
of closed available replacements. Each binding has at most
`nodes.next + 2` choices. This does not bound replacements created by future
reads and does not prove general cold-reader termination. See
[repaired binding keys](lean/notes-fresh-binding-keys.md).

## Actual stored-plan binder depth and its zero case

`7f1daf23` defines `InternedStoredPlanBinderDepth.valueDepth`, which ignores
closed captures, and `bodyDepth`, which measures the actual Mu body plan.
`encode_depth` proves exact maximum binder nesting in the emitted plan.
`Path.plan_depth_bound` bounds actual source callback crossings.
`syntax_zero` characterizes binder-free plans. `execute_zero_noNewMu` and
`unfold_zero_noNewMu` prove the zero case. Ordinary allocation remains
possible. These theorems require no preparation or semantic-cache premise.

An exploratory run checked 1,336 generated closed expressions and every
closed Mu in each constructed cache. It found no newly allocated closed
Mu whose body measure failed to decrease on unfolding. This is finite
validation, not a proof. File `/tmp/mcfta-open-rank-probe.lean`; log
`/tmp/mcfta-open-rank-probe-20261014.log`.
The depth-one checkpoint below is historical. General strict progress is
now proved by the later open-depth correspondence and allocation bound.
At this earlier checkpoint the dynamic rank budget was unproved.
`6132e4f2` and `68e790f0` later prove the reader and shared traversal budgets.
See [stored-plan binder depth](lean/notes-stored-plan-binder-depth.md).

## Actual normalization bounds and the positive depth-one case

`262242f9` proves that coherent available records satisfy
`valueDepth value ≤ value.depth`. The actual repaired ordinary placeholder
also bounds this measure. Closed captures can make the cached bound loose.
This does not make cached depth a decreasing unfolding measure.

`1e28a69c` proves open-depth bounds through actual node construction, union
flattening and merging, canonical cache readback, and root self filtering.
`InternedStoredPlanBinderDepthFlat.callback_bound` follows binder-free
callbacks with arbitrary closed captures and bounded open lexical inputs.

`InternedStoredPlanBinderDepthOne.build_new_zero` follows every actual
source branch whose maximum binder depth is at most one. Each final Mu is
an exact earlier record or has an open body plan of depth zero. The initial
cache can contain deeper Mu records. `execute_new_zero` derives the same
property for actual stored substitution with zero-depth replacements.
`unfold_new_zero` applies it to closed available input with body depth at
most one. `unfold_one_decreases` proves strict decrease for every new Mu
when that original body depth is one. It examines the complete returned
cache, including probe allocations. No preparation, source semantic heap,
or supplied successful outcome is required. Cached capture depth is unbounded.

The depth-one checkpoint audit passed 1,375 jobs and 42,935 theorem
dependency checks. Log: `/tmp/mcfta-open-depth-one-20261014-audit.log`.
The 14:07 restart snapshot contains 1,732 Lean-tree files, the root restart
documents, the retained fixture, and the exploratory probes and results.
Directory: `/tmp/mcfta-formalization-depth-one-20261014-1407/`.
`preservation.json` compares the 1,728 pre-rebase files: none is missing.
Only audit imports, the two coverage ledgers, and the two updated component
notes differ intentionally. All earlier proof and draft bytes remain.

The later general progress theorem supersedes this depth-one-only scope.
Finite repeated cold traversal and physical product language remain open.

## PR #122 preserving refresh

The current upstream base is `3ea4a9d8`. PR #122 changes only
`cfta-generator/src/Data/CFTA/Gen/Synthesis.hs`. It memoizes synthesis
terms by argument flag and size, and relevant terms by flag, size, and
ordered argument names. No Sized or interned runtime code changed. The
synthesis application still has no complete formal source model.

The 497-step preserving rebase completed at `fc81eacf` without conflicts.
Backup `backup/formalization-before-synthesis-memo-refresh-20261014-1409`
retains `e41c7f5a`. All 1,732 saved Lean-tree files matched exactly.
Evidence: `/tmp/mcfta-synthesis-memo-refresh-20261014-1409/`.
The post-rebase audit passed 1,375 jobs and 42,935 theorem checks. Log:
`/tmp/mcfta-synthesis-memo-refresh-20261014-audit.log`.
The new depth-one hash is `0d433092`; the cached bound is `d623c648` and
stored-plan compiler depth is `c269539f`. Earlier hashes remain in backups.

Both changed-library suites pass in Nix: 208 generator and 145 refinement
examples. The unchanged core's earlier 289 passing examples remain applicable.
Fourmolu passes for the changed module. Logs:
`/tmp/mcfta-synthesis-memo-refresh-20261014-tests.log` and
`/tmp/mcfta-synthesis-memo-refresh-20261014-format.log`.
No local Haskell source or test was added. Existing active-package gild
checks remain applicable because no Cabal file changed.

## General actual open-depth correspondence and unfolding progress

`482cc0e2` proves exact open depth through actual union reconstruction,
ordinary merging, canonical readback, and root self filtering.
`InternedOpenDepthSemantics` uses the existing free-name and empty-shape
observations plus separate lexical depth inputs. A closed binder result
has depth zero. External renaming and both actual probe arguments preserve
the interpreted depth. The static source plan plus its input depth bound
bounds this interpretation.

`InternedOpenDepthExecution.build_depth` follows every actual repaired
source branch. `closed_heap` and `closed_probe_equal` derive equal open
depth for every complete Mu body and its Depth probe from actual empty-
cache construction. This covers raw and smart binders, arbitrary closed
captures, canonical hits, and all probe records. The old cached-depth heap
and free-name observations determine the exact cleanup branch.
`build_bound` and `callback_bound` derive actual returned-value bounds.

`de322a41` proves `InternedStoredPlanBinderDepthProgress.build_new_lower`.
With zero-depth lexical inputs, every complete Mu in the returned cache
is an exact initial record or has body depth strictly below the original
plan depth. `execute_new_lower` follows the actual stored compiler.
`unfold_new_lower` and `unfold_decreases` prove general strict progress for
closed unfolding. Every newly allocated Mu is covered, including open
probe records. `constructed_unfold_decreases` derives all heap premises
from actual empty-cache construction. No preparation, supplied successful
outcome, or assumed progress law is used. `execute_heap` and `unfold_heap`
preserve the new body/probe invariant for subsequent actual source work.

The aggregate audit passes 1,381 jobs and 43,054 theorem dependency checks.
Log: `/tmp/mcfta-guarded-input-native-soundness-20261014-audit.log`.
The three permitted axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
The 14:38 restart snapshot contains 1,738 Lean-tree files, the root restart
documents, the retained fixture, and the new source/progress audit and live
probe evidence. Directory:
`/tmp/mcfta-open-depth-progress-checkpoint-20261014-1438/`.
Its preservation report compares all 1,732 saved pre-rebase files. None is
missing. Only audit imports, two coverage ledgers, and the depth note changed
intentionally. All earlier proof and marked-draft bytes remain unchanged.

The primary Sized source results remain intact. Later checkpoints prove
general finite cold traversal and structural final tables. General guarded
row-language preservation and physical product language remain open.

## Historical PR #121 preserving refresh

The earlier upstream base was `8e393e62`. Its only change is the `substFree`
comment qualification for smart binders and raw unused binders. Runtime code
and Sized code did not change. The 496-step preserving rebase completed at
`d8c500d4` without conflicts. Backup
`backup/formalization-before-substfree-doc-refresh-20261014-1337` retains
`d0750228`. All 1,728 saved Lean-tree files matched exactly after rebase.
The manifest and restart copies are under
`/tmp/mcfta-substfree-doc-refresh-20261014-1337/`.

The unchanged Lean audit passes 1,371 jobs and 42,877 theorem checks.
Fourmolu passes for the changed `Type.hs` documentation in Nix. Logs:
`/tmp/mcfta-substfree-doc-refresh-20261014-audit.log` and
`/tmp/mcfta-substfree-doc-refresh-20261014-format.log`.
The previous 642-example Nix suite and active-package gild checks remain
valid for the unchanged runtime source. They were not repeated for comments.
At the PR #121 checkpoint, depth proof was `d0680cbe` and repaired
binding keys were `41171842`.
Earlier proof hashes in component notes remain in the preserving backups.
The retained raw counterexample does not prove the qualified identity law.

## Remaining work and assessment

The central mathematical and source-algorithm contracts are strong. The work
has exposed and repaired real defects. It is not yet an end-to-end proof of
the Haskell library. The largest remaining obligations concern general
recursive construction/exposure, final cold exposure and
physical product-row correspondence, native SCC/split import readback and custom decoder order,
general equality propagation, and concrete runtime/dependency contracts.
No verified Haskell-to-Lean extraction exists. There is no honest single
completion percentage for these different layers.

## PR #119 preserving refresh

The PR #119 refresh used `origin/microcfta` at `c66d10ea`. Its 479-step rebase
completed at `018ae4db`. Backup
`backup/formalization-before-state-label-refresh-20261014-1220` retains
`8eeb1eea`. All 1,707 saved Lean-tree files matched exactly after rebase.
Manifest and restart copies: `/tmp/mcfta-state-label-refresh-20261014-1220/`.
Manual overlaps kept the merged constructor changelog and upstream's
identical `void` behavior in Sized. All earlier proofs, repairs, drafts,
fixtures, stashes, backups, and other worktrees remain.

PR #119 escapes at signs and backslashes in synthesis state labels. Its
native regression is retained. This application-level label codec is separate
from the proved SMT-name adapter. Sized and core refinement source did not
change. Executable package source and tests match upstream. Only the retained
four-line constructor changelog note differs. The synthesis API still has no
complete formal source model. No benchmark specification was formalized.

The post-refresh Lean audit passed 1,354 jobs and 42,506 theorem checks. All 642
Haskell examples pass in Nix: 289 core, 208 generator, and 145 refinement.
Fourmolu and both active-package cabal-gild checks pass. Logs:
`/tmp/mcfta-state-label-refresh-20261014-audit.log`,
`/tmp/mcfta-state-label-refresh-20261014-tests.log`, and
`/tmp/mcfta-state-label-refresh-20261014-format.log`.
Earlier refresh records and old proof hashes below are historical and remain
in the preserved backup branches. Current single-unfold proof: `b1994b3f`.

## Checkpoint and validation

Branch: `formalization/microcfta-sized-20261014`.
Upstream base: `origin/microcfta` at **`8e393e62`** (PR #121).
The current 461-step preserving rebase completed at `e3a33ed5`.
Backup `backup/formalization-before-producer-refresh-20261014-1014` retains
`0ca89cba`. All 1,676 saved Lean-tree files matched immediately afterward.
The manifest and extra copies are under `/tmp/mcfta-producer-resume-20261014-1014/`.
Upstream's faster two-form encoder and new regression remain. `98f633fa`
proves both tagged branches, safety, serializer identity, and injectivity.
The public preparation, encoded calls, and solver-decided Sized path use that
current codec. The older decimal-only proofs remain as historical evidence.
Executable Haskell source matches upstream; the constructor changelog note
remains local. Earlier proof hashes remain in preserved backup history.

The previous refresh record is historical:
The 398-step rebase completed at `97d79d63`. Two overlap resolutions retain
upstream's equivalent `void` call and merged recursive-union changelog text.
Backup `backup/formalization-before-sized-refresh-20261014-0036` retains `f4b5fac1`.
All 1,515 saved Lean-tree files matched immediately after rebase. Later only
intended coverage documents, the finite-key and pending-producer descent notes,
and audit imports changed among those files.
All earlier proofs, marked drafts, repairs, stashes, and worktrees remain.
`lean/repro/NestedUnaryTwoAtom.hs` remains intentionally untracked.
The latest proof checkpoint is **`0258ae86`**; later commits record this handoff.

The current Lean 4.34.1 audit passes **1,417 build targets and 43,451 theorem
dependency checks**, using only `propext`, `Classical.choice`, and `Quot.sound`.
Log: `/tmp/mcfta-guarded-input-native-soundness-20261014-audit.log`.
After PR #119, all **642** examples passed in Nix: 289 core, 208
generator, and 145 refinement. PR #121 changes comments only; the runtime
checks remain applicable. Fourmolu and active-package cabal-gild passed.
The broader gild check found formatting failures in two unchanged legacy
`microecta` package files. Those unrelated files remain unchanged. No new
production test was added locally. Exact commands and logs are in [HANDOFF.md](HANDOFF.md).

No background proof worker is active. Weekly allowance was **28% at 16:42 CEST**.
Refresh it before new work and stop all work at **1% or less**, as the latest
explicit user instruction requires. Everything remains local: no push, deployment, or
board post. Benchmark formalization remains excluded.

## Previous Sized checkpoint

The following 21:56 record is historical. The results above and the current
handoff supersede its next-target and publication statements.

Updated: **2026-10-13 21:56 CEST**.

The primary `Data.CFTA.Sized` source models now cover exact accepted terms at
each node-count size, finite class evaluation, size-major prefixes, and both
distinct-term rank/unrank inverse laws. The decided path preserves the first
Unknown error and requires explicit per-call evaluator contracts. Replies
to repeated queries may differ. Every successful relational trace is exact
under per-call adequacy. Finite per-call result witnesses give a finite
bounded result, including errors.
**Whole-implementation verification remains incomplete.**

Upstream refresh reported no change: `origin/microcfta` remains **`2200117`**.
The starting checkpoint `f8a3d48` is preserved on
`backup/formalization-before-sized-resume-20261013-2123`. All earlier proofs,
counterexamples, repairs, three marked drafts, stashes, and other worktrees
remain. The untracked `lean/repro/NestedUnaryTwoAtom.hs` is unchanged.

## Current exact-size results and repair

Two native and kernel-checked examples show that the former optimized Sized
path changed ranks. `fromFTA` can remove dead or duplicate transitions, which
can change canonical row order. Checking that trimming changes nothing does
not cover the duplicate case.

Local repair **`ea73724b`** sends the original sorted explicit rows to the
existing optimized count table and bottom-up inverse. It checks ambiguity
with a finite synchronous product. Constrained or ambiguous graphs use the
reference. The interned core remains intact. `SourceSizedDispatcher.sized_eq_reference`
proves equality of the complete query records and residual errors for the two
branches. This direct query path no longer depends on `fromFTA` or `rowsOf`.

The checked reference recurrence includes actual candidate order, equality
path traversal, first-occurrence duplicate removal, finite evaluation, signed
invalid queries, and the residual scan on trimmed rows. Successful decided
tables preserve the exact original reference order through their bound.
Empty classes do not suppress later sizes. `SourcePlanScale` extends the
existing partition proofs with positive repeated-child node counts.
`BoundedPruningFix` and `BoundedPruningCaller` prove the current local loop
bounds and preservation under explicit per-call contracts.

Read [the Sized proof note](lean/notes-source-sized.md) for the theorem map,
both order counterexamples, source repair, validation, and exact boundaries.
The source models do not verify concrete Haskell containers, lazy heaps,
machine conversions, solver IO, or extraction.

The aggregate audit passes **1,052 jobs and 37,335 theorem dependency checks**.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
Log: `/tmp/mcfta-sized-20261013-final-audit.log`.
The generator suite passed **206 examples**, including two temporary
regression cases. The permanent suite remains unchanged at 204 examples.
Both native counterexamples are retained. Fourmolu and cabal-gild passed in
Nix. No new production test case was committed. Counts are validation
evidence, not a coverage percentage.

All proof workers are stopped. All work remains local. Weekly allowance was **58% at 21:55 CEST**; refresh it
with `/tmp/mcfta-weekly-usage.py` and stop all work at 20% or less.
[HANDOFF.md](HANDOFF.md) and [NEXT-PROMPT.md](NEXT-PROMPT.md) contain the current
restart instructions. The preserved constructor and equality work remains
secondary to the direct exact graph contracts.

## Previous restart review: source wishlist and initial proof gaps

This section records the `f8a3d48` restart review before the local Sized repair.
Its next-target statements are historical. The current results above and the
Sized proof note supersede them.

PRs #107, #109, #110, #111, #112, and #113 address most of the source wishlist.
The explicit-graph decision keeps the optimized interned core. It does not
authorize or require a replacement of that core.

| Main contract | New implementation | Checked foundation and next gap |
| --- | --- | --- |
| Exact distinct terms at size `n` | `Data.CFTA.Sized.sizedReference` builds child classes at smaller sizes, checks path equalities, and removes duplicate terms. It supports cyclic and ambiguous graphs. | `RecursiveSize` proves exact-size recurrence for plain graphs; `Language` proves guarded acceptance; `DistinctRank` proves distinct indexes. Compose a new proof for the actual equality-filtered, first-occurrence source sequence. |
| Finite time for each requested size | The reference recurs only on smaller sizes. `sizedUpTo` folds over finitely many sizes and states. Empty classes do not stop later sizes. | Formalize these actual workers. Solver-decided completion requires each evaluator call to terminate. A proof of reference recurrence does not establish lazy source productivity or optimized adapter completion. |
| Size order | `termsOfSize`, `countOfSize`, `rankOfSize`, and `unrankOfSize` share one class sequence. PR #111 counts repeated child positions by node multiplicity. | Compose ascending classes into the size-order theorem. Extend source size models for `PlanScale`. Existing `terms` remains depth/marker oriented; finite `fromAutomaton` retains its own rank order and symbolic size conventions. |
| Ranking and unranking | Reference queries use the same distinct list. `sized` dispatches to the count-table decoder and bottom-up inverse where the plain unambiguous import succeeds. | Reuse `SourceCyclicAutomaton.exact_index_api`, `SourceFiniteAutomaton.exact_index_api`, and `SourceSymbolicStableIndex.stable_source_index`. Prove exact order agreement and current representation adapters for the new dispatch. |
| Full guards at a size bound | `sizedUpTo` checks each complete candidate with `evaluateConstraint`. `Unknown` gives `GuardUnknown`; it does not reject a term silently. Returned classes above the bound are empty. | Prove successful exactness under terminating and adequate evaluator contracts. Logical solver soundness alone does not prove complete decisions. |

Read [Sized.hs](cfta-generator/src/Data/CFTA/Sized.hs) and
[ADR 0004](docs/adr/0004-explicit-graph-boundary.md). `sizedReference` and
`sizedUpTo` operate directly on an explicit `FTA` without pruning or binder
construction. The optimized `sized` branch still calls `fromFTA`, then
`automatonIndex` and `automatonTermPosition`; those read interned rows.
The ADR identifies consolidation through `toFTA` as further work. It is not
evidence that every optimized query already avoids the interned adapters.

PR #109 adds `fixWithin` and `pruneRounds = 64`. Transition narrowing and
repeated recursive-node pruning now have local pass limits. Original guards
remain when the limit ends. This removes the requirement to reach an identity
fixed point in those loops. It does not by itself prove every individual
pass, recursive reconstruction, or solver call terminates. The explicit graph
reference/decided size paths do not call these loops at all.

PR #110 gives three source contracts in `CONTEXT.md`: exact transformation,
over-approximation, and representative selection. The saturated-merge
counterexample remains valid. Monotonicity of that approximation is not a
prerequisite for the direct exact-size API. The old proof drafts remain useful
for the interned and optimization paths; they are secondary restart targets.

## New representation bridges

| PR | Source change | Required proof |
| --- | --- | --- |
| #104 | Enumeration now uses continuation-passing backtracking. | Relate `allBranches` to the `StateT`/list machine in `EnumerationState`. Preserve ordered results, branch-local states, failure, choice, bind, and state operations before transferring `EnumerationExact.runs_exact`. |
| #105 | One fold descends suspended constraints into every child. | Relate each resulting `IntMap` entry to `EqualityTrie.descendScs_exact`. Compose inherited/new constraints and prove the maximum-child arity check. Valid tries must exclude empty child entries. |
| #106 | Union-find omits a compression write when the parent is already the representative. | Transfer `UnionFind.findRoot_correct` and termination through extensional forest equality. |
| #108 | The empty intersection domain has identity zero; other domain identities are raw interned identities plus one. | Adapt `IntersectionFlatMemoKeyDomain.domain_intern_correct`, `domain_identity_exact`, and flat-key injectivity. Prove zero/successor separation and revised machine bounds. |
| #111 | `PlanScale` and `scaleIndex` multiply a member's size by a positive factor without changing its rank or value. | Extend `SourcePlanPositions.Plan`, `position_replay`, and `SourcePlanPartition.partition_exact`. Use `CompactGroups.childGroups_nonempty` for a positive factor. Selection is restricted to valid counted sizes; quotient selection alone does not check divisibility. |

The source review found no new concrete public correctness defect in these
five changes. Their former models still check, but they do not include the
new representation branches. `CompactEdgeRanks` count, language, and inverse
results remain reusable; the repeated-child node-count connection needs the
new scaling proof. No new production test was added in this refresh.

## Preserved component coverage

| Area | Checked result | What remains |
| --- | --- | --- |
| Mathematical language, enumeration, ranks, probabilities | Finite-term acceptance, enumeration laws, distinct-term bijections/inverses, and exact rational distributions. | Full connection of every runtime API path to these laws. Generator members remain distinct from FTA terms. |
| Executable library components | Enumeration and symbolic count/select/rank drivers, supported lattice operations, typed recursive/mutual/n-ary families, nested joins, guard and pruning components. | Arbitrary runtime schemas, support/codec wiring, recursive productivity, and remaining primitive adapters. |
| Constructor repair | Facts, normalization, actual semantic origins, root profiles, free-name heaps, closed-output free-name absence, capture bounds, exact completed replay, arbitrary-record depth/deep heap induction, source completion, and successful stable native first execution under checked words. | Complete accepted-language correspondence, output preparation or a broader cold-reader invariant, and concrete runtime correspondence. |
| Cold comparison and merging | Prepared cold completion, original-language coverage, exact fuel stability and successful replay. Exact repaired reader and complete comparator bridges. | The repaired selection bridge has a kernel-timeout draft; whole repaired merge composition follows it. Open nested Mu reconstruction remains outside the prepared fragment. |
| Equality convergence | Repeated target merge reaches an exact fixed point within ordinary-tree height. A concrete nested unary two-atom endpoint loop has a derived bound. Actual-cache original ancestor replay and edit effects are proved. | Compose both ancestor/forest edits and root stopping. Generalize beyond fixed unary/two-atom/single-class fragments. |
| Upstream optimizations through PR #103 | Flat memo probing/copy/growth/winner retention and bounded keys; maintained enumeration indexes and exact scheduler selection. | The newer representation bridges above, native publication, concrete containers, identity lifetimes, and runtime range obligations. |

See [COVERAGE](lean/COVERAGE.md) and [API-COVERAGE](lean/API-COVERAGE.md)
for precise premises. External solver, random-source, codec, concurrency,
and Haskell runtime contracts are explicit. There is no verified extraction.

## Closed constructor defect and local repair

The old constructor's unrestricted closed completion claim is **false**.
`InternedClosedPendingBoundary` gives a scoped structural expression that
reaches pair `(86,86)`, reserved identity 87, and an absent payload with next
counter 92. Its callbacks do not inspect their arguments. Two independent
native translations exceed five seconds while forcing the root to WHNF.
The native runs establish bounded noncompletion; the kernel separately proves
the exact model pending result. This is row 23 in the repair ledger below.

Local repair **`fbc3097`** (formerly `e0e1b37`) chooses an ordinary probe above every free ordinary
level of the actual Depth observation. `matchMu` uses that same stored
observation. Both failing fixtures complete in the repaired Lean executor.
All five native probes and 620 examples passed at the earlier checkpoint.
The rebased combined suites now pass 633 examples.
The old executor and counterexample remain intact.

The repaired source proofs now retain all callback effects, including discarded
computations. Each complete Mu's free ordinary names match those of its Depth
observation and lie below the chosen probe. Returned-value freshness alone does
not settle all intermediate discarded computations. General repaired completion
is still open. Read [the counterexample](lean/notes-paired-pending-boundary.md),
[repair](lean/notes-fresh-ordinary-candidate.md),
[semantic contexts](lean/notes-fresh-ordinary-contexts.md), and
[depth work](lean/notes-deep-free-depth.md).

The second local repair, **`807e867`** (formerly `558b316`), preserves explicit recursive child
unions and fixes the five-alternative public pruning timeout. It remains
separate from the constructor repair. See row 22 and
[merged narrowing](lean/notes-merged-narrowing.md).

## A rejected general convergence argument

Saturated target merging is **not monotone** under language inclusion or
source childwise row coverage. Five explicit pairs and a compact two-row
encoding have the same five native accepted terms. Both merge results are
already fixed points, but one accepts nine pairs and the other five.
`p(a,c)` separates them.

`EqualityMergedTargetMonotonicity.saturation_not_monotone` proves input
inclusion and failed output inclusion using the actual returned-cache language.
Native execution independently confirms input equality and the `5 → 9` versus
`5 → 5` counts. This rejects a proposed closure proof. It does not demonstrate
an equality-loop cycle or prove nontermination. Preserve the
[counterexample and explanation](lean/notes-equality-merged-monotonicity.md).

## Exact restart targets

1. Prove the new `Data.CFTA.Sized` reference class worker and its four query
   laws. Add the bounded decided path and its explicit evaluator contracts.
2. Connect the optimized dispatch to the same sequence. Prove size-major
   composition and the explicit-graph adapter boundary.
3. Add positive `PlanScale` correspondence and the bounded pruning caller.
   Complete the small representation bridges listed above where needed.
4. Resume the preserved constructor and optimization targets below when the
   exact path requires them or after its main contracts are complete.

Detailed instructions are in `HANDOFF.md`. The previous restart targets are
retained here as secondary work:

1. Finish free-name membership projection for `InternedDepthSemantics`.
   Coherence and exact profile projection already compile. Use the local
   `InternedFreshOrdinaryDepthRequest` law in full syntax induction over literal
   environments to derive the depth/deep heap. Then continue general completion.
2. Resume `MergedFreshOrdinarySelection.lean.incomplete`. Its `any_eq` proof
   exceeds the kernel limit; the complete comparator bridge is checked. Then
   compose repaired selection through the cold merge worker. See
   [comparison bridge](lean/notes-fresh-ordinary-comparison.md).
3. Resume `EqualityNestedUnaryAncestorEditCompletion.lean.draft`. Retain the
   exact `node_complete` run, apply `edit_stored` and `meet_correct`, then compose
   both forest edits and the root identity stop test. See
   [actual-cache ancestor replay](lean/notes-equality-nested-unary-ancestor-replay.md).
4. Continue the broader runtime, accepted-language, and termination obligations.
   Do not infer progress from a finite carrier alone or use the refuted
   saturated-merge monotonicity shortcut.

The original `MergedAdaptiveStability.lean.incomplete` remains byte-for-byte
unchanged. Its completed sibling proves fuel independence. Both newer marked
drafts are committed and excluded from builds. The positive diagnostic
`lean/repro/NestedUnaryTwoAtom.hs` remains deliberately untracked; preserve it.
All stable modules are in the aggregate audit.

The sections below retain the detailed repair ledger and earlier component
results. Old constructor modules describe the preserved pre-repair executor
unless their names explicitly start with `InternedFreshOrdinary`.

## Previous checkpoint and required contract

The history below describes the checkpoint before PRs #104–#113. Its source
hashes and dated checks remain historical evidence. Use the current status
and restart priorities above for new work.

The continuation branch is `formalization/microcfta-resume-20261012`.
Its implementation base is `origin/microcfta` at `9508eb3`, including
PRs #97 through #103. The latest continuation rebased all 308 commits.
The earlier reset continuation rebased 274 commits onto `4897831`.
Source conflicts kept the merged upstream implementations and all local proofs.
Backup `backup/formalization-before-refresh-20261013-1306` retains the
published checkpoint `8a80947`. The rebased proof tree initially matched it
exactly. The earlier restart rebased 267 commits onto `8ac24bb`. Backup `backup/formalization-before-refresh-20261013-0418` retains
the previous checkpoint `2aacf4f`. Proof commit `721ff6d` adds full free-name
semantics and historical probe boundaries. The previous proof branch remains
unchanged. Backup `backup/lean-before-microcfta-20261012-2200` and the retained
stash preserve the pre-rebase work. Matti explicitly requested publication of checkpoint `8a80947`; it was
pushed to `formalization/microcfta` at 04:33 CEST. New work remains local.
For a constrained language, compilation and enumeration must contain every
valid finite term and no invalid term. A finite FTA language with `n`
distinct terms must have exactly `n` ranks, with both decoder/inverse laws.
Sampling must give each term its requested normalized weight. An exact
optimization must preserve both the accepted language and the weights.

Three counts must remain separate:

- A **term** is one finite ordered constructor tree.
- A **run** is one accepting derivation. Several runs can produce one term.
- A **generator member** is one indexed source occurrence. Several members
  can have equal values and equal constructor terms.

The distinct-term rank contract applies to the FTA import path. Arbitrary
generator choices, maps, and joins retain members. They are not a quotient
by term or value equality. The checked recursive example
`label N (choice [pure, occurrence, occurrence])` has two size-two member
ranks with the same complete constructor term. Its inverse correctly returns
both ranks. This is a contract distinction, not a new decoder defect.

## Repaired source defects

Rows 1 through 21 are merged upstream at `4897831`. Rows 18 through 21
were local repairs at the earlier checkpoint. Rows 22 and 23 are local repairs. Each row has a retained source reproduction and a corresponding formal
counterexample, repair theorem, or operational model. Older per-repair test
totals in the linked reports describe their historical checkpoints. The
current combined suite total is 633.

| # | Failure before the repair | Current behavior and evidence |
| --- | --- | --- |
| 1 | Quantified substitution could capture a name in an `App` function position and change `No` to `Yes`. | Rename bound function heads and substitute nullary applications as values. Reject an unrepresentable non-name function head through the checked API. [Reproduction](lean/repro/FormulaCapture.hs). |
| 2 | A tautological observation of an atomic 9:1 choice could make bounded sampling uniform after a product. | Retain within-size atomic weights and transport their size metadata. [Reproduction](lean/repro/CurrentFindings.hs); `MassRetention`, `SizeMass`, `SizeTransport`. |
| 3 | Minimization could delete the only accepted root term without installing its chosen representative at the root. | Install root representatives and recheck an accepted derivation after the complete schedule. [Detailed finding](lean/SYSTEM.md#minimization-can-remove-the-only-accepted-root-term); `MinimizeSchedule`. |
| 4 | Union inside a nested binder could discard an enclosing reference and omit valid finite terms. | Retain open union operands and resolve their epsilon closure after binding. [Reproduction](lean/repro/OpenUnion.hs); `EpsilonUnion`. |
| 5 | Pruning a valid open nested binder could raise `nodeEdges: unresolved union reference`. | Inspect the stored open body before unsafe outer-edge unfolding. [Reproduction](lean/repro/PruneOpenBinder.hs); `PruneReads`. |
| 6 | Closing grouped applications could produce support graphs that rejected every decoded term. | Close every retained private alternative and preserve the complete callback image. [Reproduction](lean/repro/GroupedSupport.hs); `SupportAlternatives`. |
| 7 | Constructor and application closing could remove private nodes across a recursive occurrence boundary. | Use one private `Recursion` boundary consistently in support, inspection, terms, and inverse ranking. [Reproduction](lean/repro/RecursiveSupport.hs); `RecursiveSupportBoundary`. |
| 8 | Grouped function spines could lose correlation between their retained child alternatives. | Preserve correlated function prefixes while closing the support and inspection graphs. [Reproduction](lean/repro/GroupedSpine.hs); `SupportSpineAlternatives`. |
| 9 | Sparse nested substitution could discharge a guard that complete evaluation rejected, admitting an invalid term. | Retain the guard and return `SolverUnknown` for the reproduced enclosing-name conflict. Safe flat ambiguous scopes can compile. This does not assert an empty language. [Pruning reproduction](lean/repro/NestedScopeCapture.hs), [compiler reproduction](lean/repro/NestedCompileCapture.hs); `PruneAmbiguity`, `SourceEnclosingRenames`. |
| 10 | Equivalent conjunctions grew from size 9 to 29 to 89 during repeated acyclic equality reduction. | Flatten outer conjunctions, remove `Top`, sort, and deduplicate while preserving scopes. The retained case stabilizes. [Reproduction](lean/repro/PruneConjunction.hs); `GuardConjunction`. |
| 11 | Combining independently interpreted guards could change an operand's meaning and admit a term rejected by an input automaton. | Allocate each outer Boolean operand independently and preserve nonempty substitution scopes. The reproduction now reports `[Yes, No, No]`. [Reproduction](lean/repro/ConjoinScope.hs); `SourceBooleanEntry`. |
| 12 | Recursive equality narrowing repeatedly expanded equivalent domains and exceeded the retained runtime limit. | Block constrained recursion while retaining the original equality constraint. The current binder constructor also removes its bare self-reference from root unions. [Reproduction](lean/repro/RecursiveReduction.hs); `ConstrainedRecursionGate`, `BinderSelfUnion`. General nontermination of the old example was not proved. |
| 13 | Observing an imported explicit union could drop every valid term and report `EmptyGenerator`. | Expose `InternedUnion` through the finite epsilon closure before ordinary observation splitting. [Reproduction](lean/repro/ImportUnion.hs); `ImportObservations`. |
| 14 | Observation filtering could reject valid recursive groups as `UnboundedGenerator` and lose their size indexes. | Filter the ascending key map directly and retain complete recursive records. [Reproduction](lean/repro/RecursiveGroupFilter.hs); `RecursiveGroupFilter`. |
| 15 | `boundDepth` could loop on retained empty binder cycles even though their outer-edge closure was empty. | Use visited `nodeEdges` exposure uniformly before recursing into constructor children. [Reproduction](lean/repro/BoundRetainedBinders.hs); `LexicalBinderClosure`. |
| 16 | A syntactic extraction such as `v == v` could be treated as an exact integer measure and remove valid expressions. | Reject fallback measures that depend on the refined value. Preserve exact singleton extraction priority. [Reproduction](lean/repro/SelfDependentMeasure.hs); `DefiningTerm`, `ParentGuardFormula`. |
| 17 | Recursive open group positioning queried cardinalities, built an empty position map, and raised `Map.!`. | Read the available group keys directly. Unsupported recursive integer closure now returns its existing explicit error. [Reproduction](lean/repro/RecursiveOpenPositions.hs); `GroupPositions`. |
| 18 | In one substitution scope, merging equal actual identities could remove the first identity replacement and expose a later replacement for the same formal. Sparse evaluation returned `Yes`, pruning admitted a rejected term, and compilation produced one invalid tuple. | Return `Unknown` when an uncertain identity replacement has a later non-identity replacement for the same formal. Later literal identities remain accepted; allocator coherence proves this refinement safe. Pruning retains the guard; compilation returns `SolverUnknown`. The existing [guard/pruning reproduction](lean/repro/NestedScopeCapture.hs) and [compiler reproduction](lean/repro/NestedCompileCapture.hs) now check both nested and same-scope cases. `SameScopeIdentityCapture` retains the pre-repair witness; `SourceSubstitutionPrecedence` proves the new check. |
| 19 | A recursive callback could inspect temporary support and select different bodies during count, term, and support rebuilds. The public bounded generator returned four terms that its support rejected. | Keep construction tokens separate from size flags. Reject payload queries until the definition completes. Nested definitions retain enclosing tokens; both recursive and finite return paths remove their own token. `RecursiveConstructionQueries` proves marker provenance, stable rejection, and completed query behavior. The existing recursive-member case in `GenSpec.hs` checks the original callback, fourteen query paths, and nested-family completion. See [the construction-query notes](lean/notes-recursive-construction-queries.md). |
| 20 | Grouped key discovery retained an earlier minimum after a callback changed its base. `minimumSize` returned zero although counts were `[0,1,1,1]` and the smallest member had size one. | Compare the final probe's keys and minima with the accumulated discovery table. Return `InconsistentRecursiveFamily` on disagreement. `GroupedProbeValidation` derives a true body fixed point for every successful check and proves that constructor programs retain their previous least-attained minima. The existing recursive-member test retains the public callback. See [the discovery-validation notes](lean/notes-grouped-probe-validation.md). |
| 21 | `mergeAlternatives` on the union of two recursive languages repeatedly unfolded the same child union. Direct recursive operands and wrapped union operands exceeded the diagnostic timeout. | Stop recursive merging at retained recursive or union boundaries. Preserve the union and its accepted terms. The direct merge and enclosing equality reduction now complete. [Reproduction](lean/repro/MergedNarrowing.hs); [proof boundaries](lean/notes-merged-narrowing.md). |
| 22 | The retained recursive child union was immediately unfolded into an ordinary node. Repeated equality passes on five recursive alternatives added six nodes and sixteen edges per observed pass. Public pruning exceeded the diagnostic timeout. | Use `createUnion` at the recursive-boundary return to retain the explicit union. The same public prune call completes. The retained fixture has idempotent merging and reaches an equality fixed point after two changing passes. This finite evidence does not prove general nested-schedule termination. See [merged narrowing notes](lean/notes-merged-narrowing.md) and [the source reproduction](lean/repro/MergedNarrowing.hs). |
| 23 | A closed structural constructor program aliases a live ordinary capture and reaches a pending Mu pair. Both native translations exceed five seconds at root evaluation. | Select a placeholder above the Depth observation's free ordinary levels and reuse that choice in `matchMu`. The kernel checks the old pending slot and repaired completion. All five native probes and 620 examples pass. General repaired completion remains open. See [closed pending](lean/notes-paired-pending-boundary.md) and [repair proofs](lean/notes-fresh-ordinary-candidate.md). |

The private `Recursion` repair changes engine-term shape. User values,
surface terms, original generator counts, distributions, and rank order
retain their semantics. Importing raw support counts the new private nodes
as nodes, so an imported node-count bound can change.

## Rebase integration and optimization coverage

The new upstream equality worker performs one pass. Its proof now describes
that operation directly. Explicit pruning and partial-reduction callers still
use fixed points where the source does. The formalization no longer attributes
an internal fixed-point loop to the public one-pass worker.

The classified similarity optimization preserves the exact ordered eligible
pair list and inference-error behavior. Its candidate comparison count is
the sum of `n * (n-1) / 2` over the classes. Classification, maps, and solver
costs remain separate. See [the similarity proof notes](lean/notes-similarity-within.md).

The indexed minimizer preserves the previous full-table schedule, including
root representatives and final copy passes. Installing a root representative
creates child links. The rebase integration now adds those parent-index
entries. Otherwise a later indexed copy could miss an inserted edge.
`MinimizeParentIndex` proves complete schedule equivalence and the required
metadata invariant. This is an integration obligation; it is not counted as
a separately reproduced public defect. See
[the parent-index notes](lean/notes-minimize-parent-index.md).

Retained size masses also move when constructors pay a size unit. Earlier
integration omitted those shifts in two paths. The source and transport
proofs now preserve the member/mass alignment.

The constructor record model omitted the current root self-reference filter.
`compileBody` now applies it at both probes and at the reserved binder identity.
The coherence, pending-record, and replay proofs include that reconstruction.
Kernel checks show that a recursive body with an added bare self operand
returns the same canonical record as the body without it. A second check
covers cleanup to an ordinary node. This repairs a source-correspondence
omission in the formalization; it is not a new Haskell defect. The lexical
`InternedBinderRebuild` and full `InternedSubstitution` worker now apply the
same filter. Their capture-avoidance, exact-language, free-reference, and
finite-allocation results remain proved.

## Recursive construction query repair

The pre-repair reproduction uses only public operations:

```haskell
recur $ \self -> case support self of
  Right EmptyNode -> oneof [pure 0, node "step" ((+ 1) <$> self)]
  _ -> leaf 99 "wrong"
```

Before the repair, the bound-three generator had four ranks and values zero through three,
each with probability one quarter. Its support rejects all four returned
engine terms. Count, sampling, and term rebuilds expose EmptyNode through
the placeholder; support reconstruction exposes its live recursive node.
The original public guardedness test accepts the body. The public API does
not state that a builder must avoid inspecting its argument.

The repair makes `support self` return `QueriedRecursiveOccurrence` in every
rebuild. The callback consistently returns the finite value 99. Its term
belongs to the returned support. Independent construction tokens remain
present during closed probes, which deliberately clear size-index flags.
The reproduction and pre-repair output are `/tmp/mcfta-context-builder.hs`
and `/tmp/mcfta-context-builder.log`; the repaired result is in
`/tmp/mcfta-context-builder-repaired.log`. The existing suite retains the
callback and the nested selected-key completion case.

This repairs the observed payload-query mismatch. It does not establish
regularity of every arbitrary callback or monotonicity of key discovery.
An empty family has no active records to reject. A callback can observe that
initial state and change its finite base after keys appear. Row 20 validates
the final discovered table before the source returns a tied family.

## Behavior that does not satisfy the stronger requested contract

**Similarity minimization preserves representatives, not every original
term.** Repairing root deletion does not make it an exact-language
optimization. A caller that requires all original expressions must not use
the representative theorem as a completeness theorem for the original set.

**Pool minimization does not preserve similarity-class probability.** It
starts a uniform distribution over the retained entries. The checked example
changes class masses from `2/3, 1/3` to `1/2, 1/2`. No discarded weight is
transferred to a representative. See
[the probability notes](lean/notes-pool-minimization.md) and
[the public reproduction](lean/repro/MinimizedPoolDistribution.hs).

**Unsupported or uncertain constraints are not empty languages.** General
quantified and nonlinear constraints lack a complete terminating solver
contract. The lattice backend rejects unsupported syntax, including `Ite`.
`Unknown`, timeout, unboundedness, and missing inspection fields remain
explicit states or errors.

**Logical alpha-equivalence does not imply identical solver verdicts.** A
sound name-sensitive callback can change `Yes` to `Unknown`. The supplied
adapter also rejects a generated actual name that collides with an unused
ambient declaration. No invalid term is admitted by that example. Exact
verdict preservation needs a name-transport/freshness contract. See
[the boundary notes](lean/notes-guard-alpha-boundary.md).

## Verified model coverage

The checked development includes independent constrained grammar derivation,
FTA acceptance, finite-term enumeration, exact finite distinct-term ranks,
symbolic count/select/rank workers with caches, supported lattice counting
and ranking, and exact rational distributions. It also covers the stated
intersection, pruning, canonical guard, minimization, and interning algorithms.
Their scope and premises are recorded in [SYSTEM](lean/SYSTEM.md),
[COVERAGE](lean/COVERAGE.md), and [API-COVERAGE](lean/API-COVERAGE.md).

The latest committed recursive work connects independent value and term
indexes, source count and sampler equations, complete inverse queries,
candidate flags, ordering, distinct returned positions, and bounded global
ranks. It includes arbitrary-branch single-root bodies and binary-choice
mutual key families. `GroupedMergeAssociativity` preserves the complete
ordered member and rank-probability fields under regrouping.

The aggregate audit now includes those results for arbitrary-branch mutual
families. The new dispatch proof distinguishes bare
singleton grouped merges from raw singleton choices that add `Choice 0`.
The original typed guard proof distinguishes a user label from a plain pay.
Both add size; only the label supplies the corresponding term-growth guard.
See [the n-ary notes](lean/notes-keyed-nary.md) and
[guard notes](lean/notes-keyed-nary-guards.md).

The recursive-join adapter now composes the actual `JoinN`, `CenterKeyed`,
and `ArgKeyed` structures through typed nested joins and mutual families.
It preserves heterogeneous argument values, aligned term ranks, retained
masses, and complete ranked samplers. The record-to-selector bridge is
complete. Mutual callback induction and the public replay filter establish
all-view and bounded global decoder preimages. Original occurrence metadata
supplies the public guards. Candidate bounds include false flags. Callback
and public rank lists are ordered and have no duplicate positions under
their local finite-leaf contracts. Ordinary `Apply` remains a separate constructor.
Support, diagnostic inspection, both sampling routes, weight flags, and
absent-term branches now have constructor-derived adapters.
`RecursiveCompleteRecord` ties these fields and the original occurrence
checks to one checked program. Arbitrary runtime schema changes remain open. See
[the join notes](lean/notes-recursive-join-fields.md).

## Evidence and its limits

- Latest source suites: **620 passing examples**, on `9508eb3` plus local
  repairs `558b316` and `e0e1b37`. Log: `/tmp/mcfta-fresh-probe-620-tests.log`.
  Fourmolu and Cabal-gild checks pass. Both retained recursive-merge source
  cases and both ordered-profile/rank-stutter source replays also pass.
- Repaired nested and same-scope source probes both report `(No,Unknown)`
  for complete/sparse evaluation, `(No,No)` before/after pruning, and
  `Right []` versus compiler `Left SolverUnknown`.
  Log: `/tmp/mcfta-scope-precedence-repaired.log`.
- Latest integrated Lean audit: **1,026 jobs; 36,839 theorem dependency checks**.
  Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.
  Log: `/tmp/mcfta-20261013-final-restart-audit.log`.
- The earlier formula capture, nested compiler capture, recursive equality,
  and open-union reproductions passed at the `de910ea` checkpoint. The independent two-key
  recurrence again checks all eight classes and 285 inverse ranks, including
  exact masses, conditional probabilities, and support acceptance.
  Log: `/tmp/mcfta-de910ea-focused.log`.
- Independent source probes covered 5,000 finite grammars; 1,536 mixed
  grouping/recursion descriptions; nine automaton-import variants; 144
  weighted descriptions across nine size bounds; and 2,080 bounded recursive
  intersection comparisons.
- The new heterogeneous `Bool`/expression join recurrence checks eight
  classes and 37 member inverses, exact masses, and support acceptance.
  Log: `/tmp/mcfta-heterogeneous-join-replay.log`.
- Earlier exact-rational recurrences checked 132 single-root and 254 two-key
  member inverses. The 285-rank delayed-third-branch probe was rerun above.
- Shared equality FTAs with `2^60` and `2^80` distinct terms passed exact
  counting and distant decode/rank round trips without enumerating their
  language. These are feasibility checks, not general benchmarks.

Efficiency has separate proof obligations. Balanced selection has checked
comparison/query bounds. Symbolic selection skips counted blocks, while
overlap preprocessing can be exponential. Polynomial evaluation and
arbitrary-precision arithmetic are not free. `groupBuilt` still enumerates
an already-built finite source during observation compilation.

The Lean sources are handwritten models and algorithm ports. The audit
checks their logical dependencies; it does not verify Haskell-to-Lean
translation. Source reproductions and finite probes support correspondence
but do not prove it for every runtime execution.

## Detailed component results and remaining obligations

The current proof checkpoint is **`073c10c`**. The integrated working audit passes
**1,026 jobs and 36,839 theorem dependency checks**. Stable proof modules
are committed and imported by the working aggregate audit. The full
formalization remains incomplete. The detailed restart order, commands,
repository safeguards, and supporting file map are in [HANDOFF.md](HANDOFF.md).

### Full nested source profiles and exact stored body tags

`InternedNestedProfiles` proves root-profile correspondence and the decoded
Mu-profile heap invariant for arbitrary full constructor `Syntax`. It covers
actual ordinary constructors, root self filtering, both probes, fresh-body
execution, smart/raw cleanup, canonical cache hits, and pending outcomes.
There is no binder-free restriction or assumed callback equation. Profiles
retain opacity and the set of literal root references. They do not retain
ordinary structure, Mu identities, or canonical union order.

`InternedStoredMuOrigins`, `InternedNestedMuOrigins`, and
`InternedProfileMuOrigins` derive the actual original source expression,
captured environment, three normalized calls, reservation, and historical
invariants for every completed stored Mu. The enclosing execution may itself
stop at another pending key.

`InternedStoredProbeTags` then proves:

- A stored body is EmptyNode exactly when both probes are EmptyNode.
- A stored body is its own reserved reference exactly when the probes are
  `RecDepth` and `RecUnint 0`.
- Smart cleanup returns EmptyNode exactly in those two key cases.

These are source-derived statements about all stored records, not finite
sample conclusions. See [the source profile notes](lean/notes-interned-root-profile-source.md),
[verified origins](lean/notes-interned-profile-reflection.md), and the dated
03:21/03:28 results in [the gate notes](lean/notes-gate-unfolding-rank.md).

### Preserved baseline constructor results

These modules describe the preserved old executor. Its general completion
claim is now refuted by the closed pending example in row 23. The repaired
executor has separate semantic heaps and still needs a general completion proof.

`InternedSpecialKeyCompletion.closed_safe` excludes pending readback at
`(Empty, Empty)` and `(Depth, Unint 0)` for **unrestricted closed Syntax**.
It has no admission grammar, callback-law, or whole-run-success premise.
The proof obtains earlier completed nested sites from the actual depth-body
trace. `InternedProfileReferenceInputs` derives the required invariance under
arbitrary literal-reference aliases.

`InternedPendingProfileBoundary.closed_remaining` restricts any remaining
hypothetical encounter to two opaque probes, or two pure probes with nonempty
fixed captured root references. `InternedPendingOldCall` independently retains
the active fresh ancestor reference and both exact probe records already
available before that ancestor reservation.

Exact local replay now covers ordinary nodes, unions, root filtering, and
cleanup through actual common cache extensions. `InternedBoundaryFreeAge`
includes free names inside old boundary Mu payloads. `InternedLiteralObservations`
derives empty-result agreement and forward bare-local reflection for actual
full-Syntax calls with arbitrary same-length literal aliases. The remaining
step is the dynamic Mu boundary/identity argument. Set equality of root
profiles cannot establish exact canonical request replay. `InternedProbeFreeSupport`
propagates free-name absence through stored probe dependencies.
`InternedProbeDependencyAge` proves strict identity descent and well-foundedness
for that graph. This is not a body-unfolding rank. `InternedOldProbeReplay`
closes the old complete-record hit case from its two smaller probe observations;
the newer smart-Mu case still needs joint boundary transport.

**Full free-name semantics and its source heap invariant are proved.**
`InternedFreeNameSemantics` covers all Syntax, with arbitrary external-name
maps. `InternedFreeNameForm` derives fixed captures and an optional argument,
including captured probe aliases. `InternedNestedFreeNames.build_free` and
`closed_heap` follow the actual mutual source execution, including cache hits,
fresh body calls, and pending outcomes. `InternedSourceFreeNames.closed_free_empty`
proves that every completed closed run has no free names.

`InternedFreeNameMuOrigins` retains both semantic tables at each stored Mu's
historical source prefix. `InternedStoredFreeNameBoundary.closed_reference_absent`
uses those origins: an old-free-name bound on the actual stored body excludes
fresh literal boundaries in both original probes. The fresh Mu-boundary half
remains open. See [the free-name proof](lean/notes-interned-free-names.md).

`InternedPureProfileIdentity.ordered_identity` identifies available pure values
from equal ordered profiles in a common normalized state. Its checked reverse
union example disproves identity from set equality. The checked warm-cache
example in `InternedPureProfileOrderBoundary` disproves exact ordered syntax
correspondence. The next proof must derive actual ordered replay; it cannot
replace profile equivalence by ordered equality.
See [the special-key proof](lean/notes-interned-special-key-completion.md),
[observed root replay](lean/notes-interned-observed-root-replay.md),
[boundary transport](lean/notes-interned-boundary-transport.md), and
[literal observations](lean/notes-interned-literal-observations.md).

### Live lexical replay and actual probe sites

`InternedFreeAbsenceReplay` proves exact raw source replay after an interned
free name disappears. `InternedLiveInputReplay` strengthens this to arbitrary
literal maps that agree at the pure interpreter's live lexical positions.
`InternedLiveInputReadiness` excludes a later pending request from an earlier
completed matching site and the later actual completed probes. It does not
assume the later binder completes.

`InternedProbeChoiceSites` extracts actual earlier sites along chosen Depth
or Unint callbacks. Each crossing retains its computed ordinary level and
chronological cache-growth evidence. `InternedLiveInputSupport` derives the
needed agreement when every changed current input is fresh and the current
probe is an older available record. General encountered scopes can also
have different Unint levels. Those differences remain an explicit gap.

`InternedProbeChoiceSites.completed_route` now retains the exact source body
at every crossing, as well as its probe choice and cache history. This
supports comparison with the actual pending descendant path. Do not assume
that a stored body's depth equals either probe's depth:
`InternedClosedProbeCostBoundary.actual_depths` checks depths `(1, 0, 0)`
in a record created by a closed source run. This is a boundary for the
proposed invariant, not a source divergence counterexample.

`InternedPendingOrdinaryMismatch.closed_depth_mismatch` now derives two
completed Depth calls of the same source body with different cached depths
from any hypothetical closed pending run. It derives the active source
origin, both lexical routes, literal contexts, and chronological histories.
No assumed callback equality or externally supplied origin is required.
The remaining ordinary-level mismatch case is not yet excluded.

### Physical comparison and cold execution

`MergedOrdinaryHeight` and `MergedMergeTermination` give a decreasing measure
for guarded recursive merge calls. `MergedComparisonSource` includes the
source EmptyNode shortcuts and ordered arity checks. `MergedPhysicalWarmup`
and `MergedPhysicalComparison` derive a finite physical inventory for the
`PreparedWithoutMu` fragment. `MergedPhysicalLanguage` proves exact finite
term semantics for its epsilon reader. `MergedPhysicalUnion` proves exact
operand-union language through actual normalization and cache readback.

`MergedColdExecution` and `MergedColdInventory` derive completion per unfold,
finite cache changes, and a finite inventory for one generated chronological
trace. They require no eager warmup and do not compare hypothetical allocation
histories. `MergedColdReaderFacts.read_closed` now proves successful ordered
source edge exposure for closed roots in that fragment. It returns resident
edges with closed children, the exact final cache, preserved facts, and exact
stability under extra proof fuel. `MergedSourceExposureLanguage` derives
actual epsilon origins for every returned edge and proves finite-term
soundness. `MergedSourceExposureCoverage.actual_exact` now supplies reverse
coverage and exact language in the actual returned cache. The full ordered
stateful comparator completes with exact fuel stability and later replay.
Its actual-cache semantic inclusion and exact child-selection language are
proved. Full cold merge composition remains active.

`MergedPhysicalGroupRoot.grouped_root_covers` proves ordinary-root language
coverage through actual child, edge, and parent effects. The checked column
worker derives filtering soundness from physical comparison and covers
singleton, retained recursive union, and ordinary union branches. Recursive
certificates apply only below the parent height. The later `MergedAdaptiveMerge.execute_complete` composes those
certificates with current-state selection and derives the complete prepared
worker result. Its remaining source correspondence boundaries are explicit.
See [physical comparison](lean/notes-merged-physical-comparison.md),
[actual union semantics](lean/notes-merged-physical-union.md), and
[cold execution](lean/notes-merged-cold-comparison.md). The new
[cold reader](lean/notes-merged-cold-reader.md) and
[physical group](lean/notes-merged-physical-groups.md) notes give exact scopes.

### Equality fixed-point termination

**Source baseline change:** PR #97 inserts `mergeAlternatives` after every
peer projection. The original `EqualityLeafProjectionRuntimeBound` still
models the previous worker. The new `MergedProjectionBound.compiled_bound`
now proves the complete merged projected-leaf schedule. It covers physical
row grouping, exact source edge and node requests, snapshot targets,
simultaneous edits, class order, required paths, and the final fixed point.
`MergedRawLeafSource.worker_actual` uses the actual runtime output cache;
no later operation executes from a proof-prepared cache. Group iteration
order is explicit and must include all source symbols. The bound remains
the original occurrence weight plus one. Endpoint domains must be leaves.

`MergedAlternativesSubsumption` proves soundness of successful bounded
recursive coverage checks, including ancestor-pair reuse. `MergedEqualityReduction`
proves full constrained-language preservation under a merge-superset contract.
The physical leaf worker now has a language-coverage theorem. Complete
group orders give equal records in a common cache, and an observed row order
derives completeness. Coverage search saturates under a complete finite pair
inventory. General recursive merge termination and the recursive physical
superset bridge remain open. See [merged narrowing](lean/notes-merged-narrowing.md).

The complete physical **projected-leaf** schedule has a derived bound of the
original occurrence weight plus one. It includes actual endpoint reads,
first-seeded target folds, recursive ancestor edits, required paths, class
order, empty propagation, and an allocation-free final fixed point in the
actual runtime cache. Endpoint domains must be leaves; ancestors may be nested.
Raw guard normalization and rejected constructor allocations are included.

Two source-correspondence gaps were repaired in the formalization. Raw leaf
pullback and dead-row trimming prevent proof-prepared caches from becoming
runtime inputs. The physical intersection model now includes the source's
ordinary-node identity orientation. The path worker uses the exact ordinary
source union branch. These were model repairs, not additional Haskell defects.
The 4,096 projected forests and 1,156 raw leaf source pairs pass again. See
[the runtime bound](lean/notes-equality-leaf-runtime-bound.md) and
[runtime trimming](lean/notes-equality-leaf-runtime-trim.md).

For one fixed **binary projected class**, `EqualityFixedProjectionInvariant`
proves that every original occurrence retains its rows after the first
reciprocal pass. `EqualityFixedProjectionTermination.run_bounded` counts missing
occurrence-row pairs in a finite complete inventory. Nested endpoint rows are
allowed. Its premises include a static commutative row relation with admitted
diagonals. The physical adapter, disappearing-ancestor phase, raw normalization,
and interaction with other classes still need composition. A public Haskell
probe with nested endpoints takes four changing passes and agrees with this
invariant. See [the binary-class proof](lean/notes-equality-projected-binary.md).

The general nested fixed schedule remains open. New checked obstructions are:

- `EqualityFixedMultiplePeers`: a convergent three-peer source-shaped example
  removes a row after the first pass. Binary occurrence growth does not extend
  directly to larger classes. Its separate abstract Steiner cycle shows that
  commutativity/idempotence alone are insufficient; it is not a source cycle.
- `EqualityFixedDegreeCounterexample`: the five-degree source leaf table has a
  nonassociative mutually reachable narrowing component. Public Haskell confirms
  the table and witness. Such components cannot be assumed to be semilattices.
- Earlier `EqualityFixedSaturationCounterexample`: alternating targets can
  return to an earlier representation even with the same recursive closure
  image. An arbitrary-target rank is unavailable.

`EqualityFixedRowProfile` derives local Boolean row behavior when higher
profiles agree. `EqualityFixedProfileMaximum` proves a removable maximum for
one finite powerset layer over a strict-ranked row base. These results do not
supply arbitrary nested lifting. Synchronized higher-profile induction is a
candidate next route. No cycle of the actual fixed source schedule is proved.

### Recursive gate rank: pure probes complete, opaque probes remain

`InternedPureProbeGate` and `InternedProbeOpacity` derive actual stored-body
unfolding completion and strict head-rank decrease from a pure depth probe.
The second probe is also pure, its level is zero, and the actual body depth is
zero. The original source syntax may have arbitrary nesting. Earlier shallow,
reachable-only, closed-nested, and marker one-step results retain their scopes.
The general case with **opaque probes** remains open.

The following checked examples rule out attempted generalizations:

- `InternedOldBodyProbeAliases`: a smart unused old body can differ from both
  normalized probes because captured sentinels are filtered differently.
- `InternedNestedProbeCostBoundary` and `InternedClosedProbeCostBoundary`:
  exact free-occurrence cost coverage fails in a completed closed source-model
  cache at slot 19. The body has external sentinel costs 1; both probes have
  those names only at cost 0. The closed program returns EmptyNode. The existing
  `FlatProbeHeap` theorem must retain its restricted scope. Haskell confirms the
  open fixture and both actual-own-to-probe substitution equations.
- `InternedSourceRankStutter`: staged scoped source-model construction with
  explicit `Depth`/`Unint 2` captures and cache prepopulation gives an actual
  modeled unfolding where both head rank and free-occurrence rank stay at 2.
  The continuation has ranks `[2,2,1,0]`. This does not establish divergence,
  closed empty-environment reachability, or universal callback admissibility.
  Haskell now confirms both rank traces and the preloaded representative. The fixture fails the unrestricted callback renaming law when the old name aliases its fixed capture. See [the source replay](lean/notes-source-rank-stutter-replay.md).
- Exact ordered root-profile correspondence is false. Reversing captured union
  operands can hit the same Mu key and return the first stored order. The
  temporary kernel check `/tmp/mcfta-profile-order.lean` passes after completing
  its inequality proof. The set-based `Equivalent` theorem remains valid.

These are proof-obligation counterexamples. They do not add production defect
rows to the repaired defects above. See
[the gate notes](lean/notes-gate-unfolding-rank.md) and
[literal profile order](lean/notes-interned-literal-observations.md).

### Other remaining source contracts

Typed nested-join families now connect support, diagnostics, both sampling
routes, weights, flags, complete inverse queries, and original occurrence
metadata. `RecursiveCompleteRecord` assembles those fields. Arbitrary opaque
Haskell builder schemas, key-discovery behavior, codecs, and lazy productivity
still require their stated contracts. Generator members remain distinct from
unique accepted FTA terms.

Full sparse Yes transports to complete logical satisfaction. Current pruning
and successful compiler classification inherit logical safety and exactness on
the success domain. A sound name-sensitive backend can still return sparse Yes
and complete Unknown. Exact backend-confirmed language equality requires
backend adequacy. The all-Int adapter derives its laws from correctly returned
external responses. See [logical read transport](lean/notes-source-read-logical.md)
and [the integer adapter](lean/notes-source-read-integer-adapter.md).

Runtime identity lifetimes, machine words, host containers, concurrency, lazy
productivity, solver IO, PRNGs, and user codecs retain explicit correspondence
contracts. There is no verified Haskell-to-Lean extraction. Similarity
minimization preserves representatives, and pool minimization starts a new
uniform distribution; neither implies exact term/mass preservation under the
stronger requested contract.

These boundaries prevent a whole-implementation verification claim. Resume
from [HANDOFF.md](HANDOFF.md), using [NEXT-PROMPT.md](NEXT-PROMPT.md). Keep the
proof checkpoint, source fixes, and all restart material local.
