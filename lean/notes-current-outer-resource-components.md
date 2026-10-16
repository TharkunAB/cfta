# Supporting proofs for cumulative outer resources

The full-library objective is still open. The target is a checked semantic
specification for languages, transformations, exact queries, generators, and
probabilities, with explicit correspondence to the public Haskell algorithms.
Exact queries must return all distinct accepted terms at each node-count size.
Counts, ordered ranks, and both rank/unrank inverses are separate contracts.
Generator members and accepting runs can have multiplicity. They do not define
the distinct-term order. Each optimization must preserve its stated contract.
Execution proofs must derive their algorithmic obligations on the supported
input domain. An assumed completed execution does not prove termination.

## Current checkpoint

Source main is `c0cc8a05`, merged at `896b0a1c`. The starting proof checkpoint
is `dcf12dc3`. Proof commits are `32d29695`, `2328161d`, and `d4cb078f`.
The evidence directory is
`lean/restart-evidence/20261016-constrained-outer-resources/`.
Three additive modules close supporting obligations. They do not close the
whole outer traversal or replace the full-library objective.

`SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources` proves the two actual
raw reconstruction steps. Edge reconstruction retains the original full field
and returned children. It makes one edge request and no node request.
Ordinary node reconstruction first compares ordered row identities.
Coherent full row readback justifies the unchanged branch. The changed branch
makes at most one node request and no edge request. Both endpoints retain the
complete existing physical receipt, native certificates, output profiles,
actual Work, final capacity, and both supply bounds. Initial step headroom
pays for requests that hit caches as well as requests that reserve identities.
Integration constructs a rejected parent and its actual contradiction
Descendants graph. Initial headroom of two edge requests pays for the parent
and the later raw rebuild at the same returned heap.

`SourceCurrentAllocatedFiniteOrdinaryLowerProfiles` retains native OutputStored
and Merge profile certificates through supplied actual Operand, Fold, Target,
Force, and Leaf reads or receipts. Each native query uses its own physical
execution trace at empty seen. A Force hit reads its causal slot domain.
A miss constructs its certificate from the same Target reads. A Leaf uses
the exact forced target and current edited input. These are verification
endpoints for supplied reads. They do not assert initial completion, numeric
warm-slot profiles, or a hereditary guard bound. No capacity plan is needed.

`SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope` bounds actual source
normalization from raw total path occurrences S and maximum path depth D.
The normalized depth is at most `(D + 1) * (S + 1)`. The class count is at
most S. The derived initial alphabet has at most `S * D` members. Finite
words over that alphabet bound each canonical class and total occurrences.
The module transfers bounds through physical payload readback, inherited-first
combination, and indexed descent. Descent shortens each retained path.
The actual live precheck returns ordered own records. It does not process
inherited records as extra local classes. The initial effective own field
therefore supplies the existing parent path-depth obligation.
These path results use the preserved natural-index model. Signed Haskell
conversion remains a separate correspondence obligation. Normalization can
extend paths, so a maximum-input-depth preservation claim would be false.

## Remaining outer proof

First retain the strong lower stores through actual Edit, Class, Pass, Stage,
Local, and Parent reads, then through all eight actual outer graph families.
The evidence file `lower-profiles-next-chain.md` gives the exact dependencies.
The new Target/Force/Leaf result does not establish that complete chain.

Prove a guard bound at every nested edge through native conjunction, Merge,
Required, edits, and class passes. The effective own field includes positive
Same extraction; a bound on the raw stored field alone is insufficient.
The new per-normalization envelope does not yet prove this hereditary bound.
Capture exact warm owners and keep each earlier Merge winner's certificate.
Language equivalence, height bounds, and NodeNarrow do not bound row or arity.

Use those producers to derive quantitative outer returned-cell certificates.
Install each certificate only after proving it for the actual owner's body.
Transport warm hits through coherent complete readback. The output shape
bound can be uniform in inherited size because the local pass processes only
own classes. Keep the actual inherited payload for keys and semantic laws.

Then derive the height recurrence in literal order: parent, returned children,
raw edge rebuild, original row suffix, and ordinary node rebuild. The two
raw-step costs are now proved. Charge every actual occurrence without a
unique-key assumption. Relate each reached prefix's Work to remaining initial
headroom and derive ParentCapacity before that parent executes.
`SourceCurrentAllocatedFiniteOrdinaryOuterNumericRoot.bounded_prepared_root`
still assumes Plan at every reached parent. Initial construction capacity
alone does not pay for the later traversal. No initial-only root theorem is
claimed here. Read `outer-profile-design-review.md` for the reviewed design.

General Mu/reference/union progress, constrained recursive selected narrowing,
repeated-pass convergence, current frontend adapters, concrete Sized behavior,
Haskell laziness, runtime containers, and full public pipeline composition remain
open. Constructor request bounds do not bound equality allocation, solver work,
instruction counts, runtime, or memory. External solver and random-draw
contracts remain explicit.

## Validation and Haskell handoff

The pinned full Audit passes 2624 jobs and 60653 dependency checks.
Only propext, Classical.choice, and Quot.sound are permitted.
All 26 public axiom/full-signature pairs and 12 integration pairs pass.
The verifier checks 164 component-manifest entries. Four historical read
references resolve exact earlier bytes: one concurrent constraint draft and
three starting restart documents. All final production hashes are checked
directly. No frozen manifest or older source is rewritten.
Public signature and integration probes, reviews, frozen module hashes, and
preservation checks are recorded in the evidence directory. The checkpoint
preserves all 7913 starting files and 2620 older non-Audit proof sources,
except the documented restart-authority edits and additive Audit imports.
All 234 starting Haskell files retain their bytes.

No Haskell change or new Haskell defect is reported. Recursive field-pool
repair `b9219b9e` is already merged by PR #65 at `c0cc8a05`. The retained
Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
Root FINDINGS keeps the external repair registry first. It records the failure,
reproducer, paths, commit, checks, and upstream status. Standalone holds keeps
its documented opaque-pool behavior. The repair rejects the invalid derivation.
Reuse the unchanged strict Nix build, 798 examples plus golden, six-file
Fourmolu, and four-package Cabal-gild and metadata evidence.
