# Actual edit counts and initial class-pass resources

Updated: 2026-10-16 21:37 CEST. Audited main is `c0cc8a05`, merged at `896b0a1c`.
This checkpoint starts at published `86c0416e` on `formalize`.
Proof commits are `d36739d9`, `2c293a11`, and `5912b634`.

## Full objective and current boundary

Prove that the current Haskell library implements its intended constrained
tree languages and public operations. Each operation has a separate contract.
The intended correspondence has this form:

```text
valid initial input + stated external assumptions + sufficient initial resources
  -> termination on the stated domain + the public operation's result contract
```

Exact transformations preserve the accepted language. Merge is an
approximation. Representative selection has its own reduction contract.
Exact size queries must enumerate precisely the distinct accepted terms,
in the specified order, with matching counts and both rank/unrank inverse
laws. Generator multiplicity and probability laws remain separate.
There is no completed whole-library theorem. The goal stays active.

## Actual callback counts

EditCallbackCounts indexes NodeCount, ChildrenCount, RowsCount, and ListCount
by the literal raw graph and its actual states. Node leaf calls count one.
An Empty below-edit and an ignored list-root callback count zero. Child and
row traversal add the counts of the actual preceding executions. A recursive
raw branch retains its body count; the finite-ordinary bound excludes it.
The bound uses original literal positions. Empty and repeated identities
or rows retain their own positions. Counts are not distinct-cache-key counts.

## Constructed edit resources

EditBudgetNumbers computes a uniform Leaf envelope from separate captured
forest and current input profiles. Let P be the original value-position
count, N the ordinary node occurrence count, and E the original edge count.
The conservative constructor bounds are:

```text
node requests <= P * uniformLeafNodes + N
edge requests <= P * uniformLeafEdges + E
```

The envelope charges a full target miss at every position. Actual shared
hits still preserve the same state and make no target Work. This bound
makes no aggregate claim of one miss per distinct path.

EditResources constructs node, children, rows, and list executions by strong
induction on the original input size. Leaf constructs SharedLeafResources.
Selected children use the actual preceding child's returned inventory,
heaps, slots, tables, and global bundle. Original row reconstruction retains
the original symbol and full guard. It invokes literal makeEdge and makeNode
at the returned state. Each prefix's Work derives the next initial headroom.

Every endpoint returns its own graph and strict Reads, the full existing
physical receipt, strong storage certificates, output profiles, ordered
narrowing, exact list length, height bounds, and stable literal execution.
It returns the actual Work trace, request bounds, final capacity, and supply
bounds. No supplied completed edit, future callback law, range plan, returned
profile, or desired semantic postcondition is an initial premise.

## Class and tail-first pass

ClassResources derives selected-path closure, compiled safety, and populated
edit flags from the finite-ordinary captured forest. It creates fresh
class-local target slots and retains warm native, Merge, and global tables.
It calls EditResources.list, then derives the full existing ClassReceipt
from the same actual Reads. Its cost is the forest profile envelope.

PassResources computes rows, arity, and cost by the literal right fold.
The head class uses the forest and profile returned by its tail. Its
initial-only induction constructs every actual tail, then the head at that
same state. Initial total headroom derives the head's remaining budget.
The final propagate operation retains heaps, tables, globals, and Work.
The full existing receipt supplies the scoped class-satisfaction language
law. No general exact language equality for Merge is asserted.

## Remaining producer and whole-library obligations

Read `restart-evidence/20261016-constrained-edit-resources/next-parent-resources.md`.
In this domain Scan selects all classes and makes no allocation. Compose
Required, then Pass at its actual returned state. Required already retains
the input row/arity profile and has occurrence bounds. Next construct local
and parent resources. Derive the existing universal earlier-prefix capacity
predicates by stable literal return uniqueness. A finite Pass return alone
does not imply the universal PassCapacity predicate.

The whole outer traversal needs cumulative Work accounting, constraint
record/path bounds, and causal quantitative certificates for warm returned
cells. Existing outer domain and height certificates do not bound row count
or arity. The strongest finite-ordinary numeric root still takes a reached
parent capacity plan. Replace that premise with a proved initial budget.

General Mu/reference/union progress, repeated-pass convergence, other
resource families, current frontend adapters and errors, concrete Haskell
containers and forcing, solver IO, and full public pipelines remain open.
Constructor request bounds do not prove instruction counts or total memory.
Sized query proofs remain separate from concrete whole-library correspondence.

## Validation and preservation

The pinned Audit passes 2610 jobs and 60501 dependency checks. All 55 declared
public pairs and 11 constructor pairs pass. All 14 integration pairs pass.
Combined probes print explicit full signatures without truncation. They use
only propext, Classical.choice, and Quot.sound. Independent source and
integration reviews find no material defect within these contracts.
The canonical dependency build retains the older unused-input warning.

Kernels construct one and two Empty callbacks on the same resource graphs,
retain repeated rows, compose two classes at the actual returned forest,
and construct a two-class fold. The empty pass retains all state and has
zero Work. Failed drafts and raw logs remain separate evidence. One draft
review refers to a historical Count source. The historical snapshot map
resolves that exact hash without changing the frozen review manifest.

Preservation retains 7553 starting tracked files, 2604 older non-Audit proof
sources, all 234 Haskell files, 47 manifests with 367 frozen module entries,
stashes, other worktrees, counterexamples, repairs, and marked drafts.
The optimized interned core remains. Evidence and verification scripts are
in the checkpoint directory. Run its verify-checkpoint.py and
verify-preservation.py --require-current to check the saved boundary.

No Haskell change or new verified defect. Repair `b9219b9e` is merged by
PR #65. The original Chain derivation now returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds still treats supplied
pools as opaque. Root FINDINGS retains the repair handoff first. Reuse
unchanged strict Nix validation, 798 examples plus golden, six-file Fourmolu,
and four-package Cabal-gild and metadata checks.
