# Current checked structural edits and complete class pass

Source main is `8f85ddb6`. The preceding published proof checkpoint is
`b992e324`. Proof commits are `63310da4`, `251fa392`, `1e54e3cb`,
`9cdb80c5`, and `7f00cf8e`. No Haskell implementation or test file changes.
The optimized interned core and every older proof source remain.

## Structural graph and finite completion

`SourceCurrentAllocatedSharedEditGraph` records the literal edit trie,
selected child offsets, ordered rows, recursive head exposure, and checked
leaf calls. Constructor-only steps retain equality operations, both native
tables, the domain cache, all target slots, and the completed merge table.
`children_length` proves that positional edits preserve child count.

Source `Interned/Type.hs:391–400` makes same-length setChildren call raw
internEdge with its original complete guard. The checked graph uses that
branch. It does not assume a new equality allocation or a universal guard
constructor law. Initial resident row fields grow through actual child
effects before reconstruction. The actual returned constructor rows account
for empty-child filtering and canonical hits.

`SourceCurrentAllocatedSharedEditRanges` checks only reached raw prefixes.
It asks for each leaf range plan at its actual target-force return. Later
children and rows use the state returned by the actual preceding call.
The list-root leaf is ignored and requires no native range check.

`SourceCurrentAllocatedSharedEditEffects` derives physical effects,
availability, selected path transport, historical slot retention, merge
extension, global effects, and the actual returned inventory. It follows
annotated reads. A leaf annotation contains its derived checked receipt.
A recursive annotation contains actual head reads and their global effect.
The captured base heap is fixed across every annotation.

`SourceCurrentAllocatedSharedEditComplete` constructs these annotations.
Its public finite endpoints supply no completed edit, future readiness,
admission oracle, final model, or result-language law. The finite trie and
reached range plan construct each call. Recursive head closedness follows
from the selected edit domain and a retained callback. Other ordinary
siblings can remain open. Each computed inventory and returned global
bundle enters the next selected child.

## Independent language and compiled classes

`SourceCurrentAllocatedSharedEditLanguage` proves narrowing and conditional
retention under concrete independent PCS meaning. It uses the same actual
leaf receipts and the same intermediate states as the physical proof.
It needs no generic guard-conjoin callback law.

`SourceCurrentAllocatedClassEditPlan` derives valid and populated compiled
tries, allowed original tokens, selected child domains, and exact callback
conditions from the actual class paths. No compiler law is an input.

`SourceCurrentAllocatedClassEdits` starts one class with its literal entry
forest and empty local target slots. All other state remains warm.
Its finite endpoint constructs the actual edit and its reads. Its receipt
narrows the input language and gives identical membership for terms that
satisfy that class. It retains arbitrary tracked path domains, not only the
current class domains.

## Right fold and final empty propagation

`SourceCurrentAllocatedClassPass` executes the tail first. The next class
captures that actual returned forest, checked state, merge memo, and global
bundle. Domain transport derives its selected domains. Only its local target
slots start empty. Actual-tail range plans construct the complete finite fold.

The full pass narrows its original forest. For a term satisfying all selected
classes, its input and output membership are equal. This does not assert that
every output term satisfies those classes. The outer guard remains relevant.
Literal final empty propagation preserves exact forest language and retains
the complete returned state and every memo table.

## Required paths followed by the class pass

`SourceCurrentConjunctionRequiredClassPass` starts at the literal returned
current Required receipt. Its exact record-path map derives every selected
class domain. The initial merge Stored invariant grows from the pre-required
heap through actual Keeps. Uniform ambient CacheCovers remains legitimate
warm semantic coverage. The finite pass returns its computed inventory.

Every output term belongs to the original forest and has the selected required
paths. The pure `satisfied_required` theorem derives those paths from satisfied
nontrivial classes. Therefore terms satisfying all selected classes have
identical membership before required preparation and after the full pass.
The composed effects retain original values, native machine extension, and
the same previously correct fourth emptiness table.

The range plan and initial global validity are at the actual required return.
The earlier RequiredGlobalMemos endpoint derives that global validity.
This component does not itself construct the earlier Scan or allocated entry.
Its selected record-path equation is not a new physical selection theorem.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit with 2358 jobs and 56817 theorem
dependency checks. Only standard foundations and the older unused-input
warning occur. Public probes and independent integration reviews pass.
Evidence and exact frozen sources are in `restart-evidence/20261016-checked-edits/`.

All 3948 starting tracked files remain. All 2348 older non-Audit proof sources
retain identical bytes. Seventeen frozen manifests pass. Stashes, other
worktree records, and the first Haskell fix registry remain unchanged.
Earlier unavailable external drafts are not claimed recovered or reverified.
Unchanged-source validation reuses the strict Nix all-component build,
777 examples plus golden, five-file Fourmolu, and four-package Cabal-gild.

## Next source entry and remaining scope

Next compose actual original allocation, construction, live precheck, current
Scan, and required execution with this class pass. Then reconstruct the parent
edge through the literal source constructor before inherited child descent.
Read `checked-outer-entry-next.md` in the evidence directory.

Source `Equality/Operations.hs:164–168` uses mkEdge around the reduced child
thunk. This is different from the final same-arity setChildren operation.
Type.hs:566–568 checks contradictory syntax before demanding child length.
An eager unconditional class-pass prefix therefore needs either a derived
constructor-admissibility invariant or the actual early rejection branch.
FieldAvailable alone is not that invariant. The later reduceChildren reads
the returned guarded edge, including a possible empty-edge sentinel. It
combines inherited constraints first and that returned edge's constraints
second. It then descends through the actual returned children.

The general constrained outer caller, inherited recursion, source worker
execution, and pending publication remain open. These new completed
sequential graphs do not establish GHC forcing or IntMap fold demand order.
Pure merge selection still needs its literal noConstraint CAF adapter.
Concrete containers, identity and comparison, machine capacity, external
solver IO, random draws, callbacks, codecs, broader frontend and recursive
generator adapters, and separate Sized contracts retain their boundaries.
Preserve all older constructor and equality work. The full goal remains active.

## Haskell handoff

This checkpoint adds no Haskell fix. Root FINDINGS.md keeps its external fix
registry first. Each later behavior fix must record the failure case, affected
files, commit, checks, and upstream status there. The mkEdge distinction above
is a source correspondence obligation, not a reproduced implementation error.
