# Quantitative outer owner certificates and current proof state

## Whole-library objective

Prove the intended contracts, then establish correspondence with the current
public Haskell algorithms. Each theorem must state its supported input domain.
Termination is a separate obligation from correctness of a completed execution.

The public contracts remain separate:

- Exact size queries enumerate all and only accepted terms of the requested
  node-count size. Counts equal the number of distinct terms. Rank and unrank
  are inverses in the specified order and within the valid index range.
- Each transformation satisfies its documented language contract. Exact
  transformations preserve the language. Over-approximations include the input
  language. Representative selection has its own refinement contract.
- Generator members, duplicate occurrences, accepting runs, and distinct terms
  retain their separate meanings. Probability results use the stated member
  space and weights.
- Validation returns the documented errors in the documented order. Supported
  executions terminate and the concrete implementation refines the model.

Exact listing, counting, and ranking use the original explicit graph rows.
Language equality alone does not preserve ranks. The optimized interned core
remains the construction and transformation implementation. Read
`docs/adr/0004-explicit-graph-boundary.md` and `lean/API-COVERAGE.md`.

There is no completed composition of these contracts for every public API.
The component proofs cover substantial finite-graph semantics, Sized queries,
constructors, memoization, equality operations, and resource reasoning.
Current frontend and concrete runtime correspondence remain separate work.

## Current conditional ordinary-root theorem

`SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeRoot.constructed_root`
constructs a finite ordinary input from source syntax. Under the existing
history, guard coverage, and numeric capacity Plan, it derives a stable literal
modeled worker execution. The same complete return retains strict Reads,
Checks, semantic Post, output availability, every earlier strong store,
ordinary domain and height narrowing, and exact full guarded-language equality.
It now also retains a universal quantitative output certificate.

The capacity Plan remains an initial premise. This theorem therefore does not
yet derive complete ordinary-root execution from initial syntax and available
constructor supply alone. It does not cover general Mu, reference, or explicit
union inputs. The modeled worker theorem does not establish concrete lazy
Haskell execution or all current public wrappers.

## This checkpoint

Source main is `c0cc8a05`, merged at `896b0a1c`. The starting published proof
checkpoint is `5c629f72`. Four focused proof commits are `ab06fc12`,
`38d45835`, `6751e604`, and `1ee825f2`.
Thirteen additive modules preserve all older production proofs.
Evidence is in `lean/restart-evidence/20261016-quantitative-prefixes/`.

TargetProfiles and SharedProfileProducer derive numeric profiles from supplied
actual Target, Force, and Leaf reads. A miss derives the slot profile before
store. A hit reads its captured earlier profile. Leaf uses the actual target
and immutable current input. The same native structural, native output, and
Merge profile stores remain at the same return.

EditShapes follows the original ordered edit inputs. Earlier edited outputs
enter reconstruction, not later callback inputs. ClassPassShapes captures the
actual class entry forest. Its right fold processes the tail first. That tail
supplies the head's input profile and retained warm tables. The returned shape
uses the existing EditBudgetNumbers and PassResources envelope functions.

StageShapes follows Scan, Required, and the same returned class pass.
ParentShapes derives row and arity bounds from the initial own guard vector,
actual precheck, and same local reads. Its bound includes the rejection result
with one Empty child. None of these supplied-read producers requires reserved
constructor headroom, a range Plan, a desired future profile, or body completion.
They verify completed reads. They do not assert that such reads exist.

ParentUniformMonotone widens the initial row, arity, height, and guard bounds.
OuterProfileNumbers defines the height-indexed complete node envelope. Each
original row first runs Parent. Returned descendants then use the produced
parent row, arity, and guard bounds at a smaller ordinary height. The outer
maximum retains the original node's row count.

OuterQuantitativeReturned gives every literal returned outer cell a universal
conditional certificate for its complete captured owner.value. EdgeCertificate
bounds Parent only. NodeCertificate includes the returned-descendant traversal.
The old domain and height laws remain in the retained structural store.
OuterQuantitativeState also retains the whole earlier strong lower store.

OuterEdgeShapes produces EdgeBody and EdgeCall laws from the same actual parent
reads. OuterQuantitativeProducer handles NodeCall, NodeBody, Rows, Descendants,
Children, and Walk. Each evaluate branch derives its universal law from the
smaller actual body before finish. Frames retain its exact evaluating handle
and captured owner. Warm readback uses Sound, table linkage, and coherent
complete-value equality before it transfers the earlier owner's certificate.
A lifecycle finish lemma alone is not used as a closed producer theorem.

The root adapter interprets the same constructed actual graph. It adds the
produced quantitative certificate without dropping any earlier conclusion.
The root integration computes initial row, arity, height, and raw guard bounds
from the original value, then instantiates that certificate at the same return.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2671 jobs and 61168 dependency checks.
All 58 public axiom/full-signature pairs and 12 integration pairs pass.
Only propext, Classical.choice, and Quot.sound occur. Final public logs have
no diagnostics or truncated signatures. Independent reviews find no material
defect in the pure transforms, owner lifecycle, actual producers, or root.

The integrations include actual missing target publication, zero-bound warm
reuse, repeated Empty edit positions, a pass followed by a native query,
raw parent rejection, exact outer owner finish, whole-state warm reuse,
returned-parent descendant order, and computed original root profiles.

The verifier checks eight component manifests with 164 entries. One review
captured an earlier ParentShapes draft. Its exact preserved source resolves
that historical input. Final production hashes are pinned separately.
A review-note filename collision was repaired by retaining both distinct notes
and restoring the earlier note byte-for-byte. Both review manifests now pass.
Failed elaboration sources and logs remain preserved.

Preservation checks retain all 8465 starting tracked files, 2657 older non-Audit
proof sources, and 234 Haskell files. Only the seven restart authorities and
13 additive Audit imports change older bytes. All 53 frozen source manifests
with 428 entries pass. Stashes and the three other worktrees remain unchanged.
Older repairs, counterexamples, and marked drafts remain present.

## Remaining work

Derive cumulative constructor Work and initial remaining headroom in actual
traversal order. Pay for each reached parent, returned descendant, original
row suffix, raw edge rebuild, and raw node rebuild. Use earlier actual prefix
profiles to derive ParentInitialCapacity and the root Plan before execution.
Read `next-initial-outer-headroom.md` in this checkpoint's evidence directory.

General recursive progress, constrained recursive narrowing, repeated-pass
convergence, current frontend adapters, signed source indexes, concrete lazy
Haskell execution, and complete public pipeline composition remain open.
Constructor request bounds do not bound normalization instructions, equality
allocations, solver work, total runtime, or total memory.
The full-library goal stays active.

## Haskell repair handoff

No Haskell source changes or new Haskell defects occur in this checkpoint.
Root FINDINGS.md keeps the external repair registry first. Recursive field-pool
repair `b9219b9e` is merged by PR #65 and locally validated. The Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds remains opaque.
The repair rejects the invalid derivation configuration.
Reuse the unchanged strict Nix source validation: 798 examples plus golden,
Fourmolu on six incoming files, and Cabal-gild plus metadata on four packages.
Record every later repair there with its failure, reproducer, affected paths,
commit, checks, and upstream status.
