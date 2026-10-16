# Current proof objective and finite ordinary target domains

Updated: 2026-10-16. Source main is `c0cc8a05`, merged into `formalize`
at `896b0a1c`. This checkpoint starts at `c47ad331`. Root FINDINGS.md
keeps the external Haskell repair handoff first.

## Top-level objective

Prove correspondence between the intended constrained tree languages and
generators and the current Haskell implementation. Each public operation
must implement its stated contract on its stated input domain. Each finite
operation must construct a terminating execution. Solver, callback, codec,
machine, and host assumptions must remain explicit.

The full objective is a family of contracts. There is no completed theorem
that verifies the whole library.

- Exact transformations preserve the accepted language. Over-approximations
  include the input language. Representative selection can remove terms.
- Exact size queries return exactly the distinct accepted terms at each
  node-count size. They terminate, give exact counts, enumerate in the stated
  order, and satisfy both rank/unrank inverse laws.
- Generator members retain their specified sizes, multiplicities, and order.
  An accepting run, a distinct term, and a generated value are different
  objects. Sampling must implement the specified distribution on those objects.
- Construction, graph readback, transformations, queries, generators, and
  sampling must compose at the same actual states and returned values.

Exact listing, counting, and ranking use the original sorted explicit graph
rows. Read docs/adr/0004-explicit-graph-boundary.md. An exact language
transformation can change row order and thus change ranks. The optimized
interned core remains the construction and transformation implementation.

## What is already proved

The Sized model has exact accepted classes, distinctness, finite class
evaluation, exact counts, signed query errors, ordered prefixes, and both
rank inverses. `SourceSizedApiLaws.Exact` collects these contracts.
`SourceSizedFiniteKeysPublic.native_sized_exact` derives them for successful
modeled dispatch on a validated original finite row map. The finite carrier
comes from its map keys. The result retains explicit solver and host
boundaries. Generator multiplicity is a separate contract.

The current outer recursive reduction model has a mutual correctness proof
for its actual completed calls. `SourceCurrentAllocatedPartialActual.root_exact`
derives full language equality for a supplied completed root reduction.
The later plain recursive proof constructs that execution in its restricted
Region. `SourceCurrentAllocatedPartialPlainRoot.constructed_root` derives
initial caller facts from covered construction and constructs finite literal
execution with full language equality. Construction success and Region remain
explicit. Region stops traversal at Mu and union. It requires empty effective
own equalities on the ordinary edges that it traverses. This is not general
constrained completion.

Current native intersection proofs also cover contextual Mu/reference meaning
at their stated boundaries. The previous finite ordinary structural proof
constructs actual checked native intersections, retains their memo invariants,
and bounds returned height by each original operand. Its initial invariants
and reached machine range checks remain explicit.

Constructor, memo, query, required-path, class-pass, generator, rank, and
probability results supply further components. The full Audit checks their
dependencies and rejects placeholders and additional axioms. A passing Audit
does not establish missing implementation adapters or pipeline composition.

## This checkpoint

Eight additive modules derive structural facts through the actual current
memo-aware target path. The finite ordinary domain contains Empty and
ordinary nodes with all their actual row children. Guards and equality
classes have no restriction. Mu, references, and explicit unions remain
outside this intermediate domain.

`FiniteOrdinaryMergeCache.Stored` ties each actual merge result to its
captured original. A warm lookup first derives complete original identity
from coherent physical readback. A miss proves the actual memo-aware body,
retains the table returned by that body, and reads its actual winning entry.
An earlier winner can differ from the new candidate. The proof preserves
that winner and its domain certificate.

`FiniteOrdinaryMergeCode` certifies the literal current body constructors.
`FiniteOrdinaryMerge` derives effects, physical Stored, structural Stored,
availability, and domain for the same completed allocated call. Its finite
endpoint constructs its own call from initial facts. `FiniteOrdinaryMergeWorker`
constructs literal worker success and all larger work/selection bounds with
the same output, full physical state, and completed memo. It does not assume
a successful worker or a future result law.

`FiniteOrdinaryProjection` proves domain closure for actual ordinary reads,
unions, projections, and forest projection. `FiniteOrdinaryTarget` derives
signed path support, complete actual target receipts, output domain, and both
native and merge structural cache invariants. Its finite endpoint constructs
its own actual target. Fold induction uses each actual returned prefix state.

`FiniteOrdinaryRequired` proves domain and height narrowing for actual required
nodes, children, and rows. Its node relation is
`DNode result ∧ height result ≤ height original`. Children retain this relation
at each position. Rows can be deleted. Its literal requireAll adapter retains
the relation for the same returned forest.

`FiniteOrdinaryShared` tracks separate certificates for native memo results,
merge results, and class-local target slots. Empty slots derive their initial
certificate. Constructor advancement retains the certificates. A target slot
needs the domain proved for its actual stored value. Actual Force derives
domain from the stored slot or from its actual Target miss. Actual Leaf uses
the native second-operand height bound to derive `NodeNarrow input result`.
Neither equal path lengths nor a bound on target height is required. The
finite Force and Leaf endpoints construct their own complete receipts and
retain all three certificates at the same returned state. Initial domain,
readiness, semantic admission, and reached ranges remain explicit.

## What is still missing

1. Compose structural preservation through shared edits, complete class folds,
   class passes, local reduction, and parent construction. Then prove a new
   finite ordinary outer recursion theorem. The existing plain returned-shape
   condition cannot describe all newly intersected children. Use a conditional
   edge domain and height certificate tied to the actual stored owner.
   Derive zero cached Mu depth and the primary scan fast branch from coherent
   domain records. This can avoid seeded queries in this restricted stage.
   A route that retains refused scan branches needs structural cache
   preservation through their actual seeded native queries.
2. Prove general constrained completion beyond this finite ordinary domain.
   Mu constraint migration, general union/reference cases, unequal-length
   classes, and repeated-pass convergence need justified progress arguments.
   A language inclusion proof or a finite local step does not give that measure.
   Reached machine ranges remain a separate obligation.
3. Complete adapters for current frontends and public errors. These include
   typing inputs, binder bounds, field pools, drawn typing fields, derivation,
   named measures, codecs, GHC instance pruning, and generator member/rank
   correspondence. Historical component proofs do not cover changed wrappers
   or their validation order automatically.
4. Prove correspondence with concrete Haskell execution: containers, lazy
   forcing, unfinished identities, memo publication, concurrency, external
   solver IO, callbacks, random draws, codecs, and machine bounds. Serial
   source models do not discharge those host obligations.
5. Complete the full pipeline theorem across construction, explicit readback,
   transformations, exact queries, generators, and sampling. Preserve row order
   where rank matters and distinguish runs, distinct terms, and values.

## Validation

Pinned Lean 4.34.1 passes the full Audit: 2508 jobs and 59107 theorem
dependency checks. All 49 public declaration axiom/signature pairs and 24
integration pairs pass. Final probes contain no warnings or placeholders.
The only permitted foundations are `propext`, `Classical.choice`, and
`Quot.sound`. The canonical build replays the historical unused-input warning.
Independent merge and shared-leaf reviews found no material defect.

Preservation checks retain all 5965 starting files except the stated restart
authority updates and additive Audit imports. All 2499 older non-Audit proof
sources retain their bytes. Thirty-four frozen manifests check 265 module
entries. Earlier repair records, stashes, and the other worktrees remain.

## Haskell handoff

This checkpoint adds no Haskell behavior change. The recursive field-pool
repair `b9219b9e` is merged by PR #65 in current main. The unchanged Chain
counterexample now returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone `holds` still treats supplied pool subtrees as opaque. The repair
rejects the invalid derivation configuration.

Root FINDINGS.md records failure, reproducer, paths, commit, checks, and
upstream status for that repair and earlier repairs. Keep that registry first.
Record each later Haskell fix there for external work. Reuse the unchanged
source validation: strict Nix all-component build, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild and metadata checks.

Preserve all older proofs, counterexamples, repairs, marked drafts, and the
optimized interned core. Evidence for this checkpoint is in
lean/restart-evidence/20261016-constrained-target-domain/. The full objective
remains active.
