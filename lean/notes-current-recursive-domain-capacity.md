# Recursive domain inventory, allocation, and compiled source scope

## Whole-library objective

Prove complete intended public contracts and their Haskell correspondence.
Derive finite execution from explicit initial support and resource conditions.
Exact queries retain distinct accepted classes, order, counts, and both rank
inverses. Transformations retain their stated language relation. Generation
and sampling have their own member and probability contracts. The full-library
objective remains active.

## Current result

This checkpoint starts at published 3d1ad127. Source main remains c0cc8a05,
merged at 896b0a1c. Seven additive modules retain every older production proof.
The proof commits are 84312e12, e1ede72e, e6732039, and ef8f7b56.

CacheFiniteInterning proves a sequential interning potential:

`final.next + missing(inventory, final) ≤ initial.next + missing(inventory, initial)`.

The trace contains actual Cache.intern calls. Each key belongs to one initial
finite list. Hits preserve the full cache. A miss consumes one identity and
removes at least one missing occurrence. Repeated calls therefore satisfy
`final.next ≤ initial.next + inventory.length`, independently of trace length.
This theorem does not assume cache validity. It does not model concurrent
losing reservations as free allocations.

SourceRecursiveIntersectionDomainInventory enumerates canonical Typed domain
keys over subsets of finite initial binder names and operand pairs. Each free
entry maps its name to that same Mu reference. Membership is equivalent to
canonical typed support in those carriers. Empty and actual Domain.extend
retain membership. The conservative list length is
`2^(binderCount + pairCount)`, including duplicate choices.

SourceRecursiveIntersectionDomainAllocation transports actual
IntersectionEmptyDomain.make histories to sequential interning histories.
The constant empty domain consumes no identity. Nonempty domains retain
their actual raw identity plus one. Valid initial cache and domain headroom
bound every represented shifted identity at the actual returned cache.

SourceRecursiveIntersectionSourceInventory derives a concrete initial carrier
from one original heap. Available node and interned reference identities lie
in its issued range. Actual Mu bindings and sorted operand pairs stay there.
The literal returned domain key belongs to the computed inventory. Node and
edge KeySafe lemmas use fixed original operand counters and a separate current
domain identity bound. They impose no bound on constructor output counters.

The uniform issued-range inventory is deliberately coarse. With N issued node
identities it has `2^(N+N*N)` entries before duplicate removal. For N=8 this is
2^72, larger than the signed domain space of a 64-bit key. It is a sufficient
finite bound, not a practical capacity guarantee for all current inputs.
The generic inventory result permits other carriers. Their actual source
closure must be proved. Query-specific reachability can reduce this bound.

SourceCurrentAllocatedNativeDomainTrace follows the CURRENT checked executor.
Only literal enter changes the domain cache. Work and optionalBinder affect
the heap. Lookup and demand affect native cells. Checked bodies affect equality
operations. One actual instruction derives its exact domain allocation event.
Arbitrary raw Steps derive allocation history and supply bounds under an
explicit Prefixes premise for local enter-key membership.

Prefixes is still supplied. This transport does not derive whole-query
inventory admission. It does not replace that missing proof with a claim of
initial-only WordRanges or recursive completion.

SourceCurrentAllocatedRecursiveDomainCode proves a local source compiler
certificate. It retains fixed original HEAP NodeScope and EdgeScope, with
current domain membership. Actual enter records the exact extended allocation
key. Literal reads recover original bound payloads from later heaps. Work,
optionalBinder, and recursive continuations use actual returned machines and
explicit physical postconditions. Node compilation covers reset, self, swap,
repeated pairs, Mu, unions, references, ordinary rows, and failure branches.
The checked body theorem certifies its literal emitted code after arity and
allocated equality checks. No Completes or Words premise is used.

SourceEqualityNativeDemandPrefixSplit closes the arbitrary checked-prefix
split. A prefix either remains inside a nonpure inner control or contains
its exact return followed by an outer continuation prefix. It retains step
counts and the full checked state. It also bounds any prefix by an actual
complete inner trace. No word or physical-trace hypothesis is required.

## Remaining raw-prefix connection

Derive the joint invariant over arbitrary SourceEqualityNativeDemand.Steps.
It must retain physical Good, semantic heap readiness, original operand scope,
domain membership, actual domain allocation history, field readiness, local
compiler certificates, and protected finish frames. At each reached request,
use original operand bounds and the already derived domain history to prove
Words BEFORE using a physical transition that requires those words.

Do not assume a PhysicalTrace as the bootstrap: its cons constructor already
contains physical Inputs, which contain Words. Recover actual warm requests
from CURRENT physical cache validity and newly derived safe keys. Do not keep
NodeReady in one fixed source Machine: new domains do not exist there.
Keep the fixed source heap separate from the current domain cache.

Finish instructions need the availability postcondition of the actual
completed smaller body and its exact evaluating owner. The local compiler
certificate's transparent finish clause alone does not supply those facts.
Use a protected frame and a simultaneous prefix or strong-body argument.

After deriving this invariant, obtain Prefixes, current domain word bounds,
and WordRanges from initial resources. Reuse the existing general recursive
native completion theorem. Its semantic Completes premise is already derived
internally. Do not redo semantic totality or transfer an older executor by
dropping current operation effects.

General constrained recursive selected narrowing, repeated-pass convergence,
current frontend and runtime adapters, and complete public pipelines remain
open. This component does not prove any of those boundaries.

## Validation, preservation, and Haskell handoff

The final pinned Audit passes 2700 jobs and 61554 dependency checks. Only
propext, Classical.choice, and Quot.sound occur. New sources and imported
public probes have no diagnostics. All 131 public and integration axiom/full
signature pairs pass. Nine component manifests retain 179 entries. Independent
reviews find no material defect. Canonical replay retains one pre-existing
unused-variable warning in InternedFreshOrdinaryClosedCompletion. Failed
sources, earlier probe expectations, and the pre-linter compiler draft remain.

Preservation retains 9010 starting tracked files, 2692 older non-Audit proofs,
and all 239 starting Haskell files. That Haskell count includes five retained
evidence probes. The 234-file Haskell set from the earlier production audit
also remains unchanged. All 56 frozen production manifests and 457 module
entries match. Only seven restart authorities and seven additive Audit imports
change older bytes. Stashes and three other worktrees remain unchanged.

Evidence is in restart-evidence/20261017-recursive-capacity/. The strict Nix
all-component build, 798 examples plus golden, Fourmolu, and Cabal-gild results
are reused for the unchanged source. No Haskell behavior changes and no new
Haskell defect are reported. Repair b9219b9e remains merged in PR65. Root
FINDINGS keeps its failure, reproducer, paths, commit, validation, and upstream
status first. Add every later Haskell repair there before historical reports.
