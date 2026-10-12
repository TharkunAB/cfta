# Parent integer settlement and retained mass

`ParentIntegerSettlement` follows the parent formula fold, kept-point ratio,
and point-closure branches in `Gen.Refinement.Internal.Compile`.
It reuses the settlement dispatch and bucket metadata in `RecipeCompile`.

`restrictedFormula` executes the source fold over renamed child formulas
followed by translated parent formulas. `retainedTuples_exact` derives its
language from finite child domains and actual tuple filtering.
`counter_domain_perm` proves that a successful `LatticeAPI.points` table
enumerates exactly those retained tuples. It uses the actual public decoder
through `OpenIntegerSource.pointDomain`. It does not assume a correct parent
count. `counter_matches_filter` derives that count from the permutation.
`counted_parent_cardinality` and `counted_parent_event` instantiate the child
domains from their actual successful point tables. Successful parsing derives
child formula scope through `LatticeDeclaredNames.points_scoped`.
These final adapters require the source count fields to contain those table
counts. They have no child semantic-domain or scope premise.

`retainedShare_exact` identifies the source ratio with the accepted share
of uniform independent finite child points. The denominator comes from the
stored child counts and the proved Cartesian tuple count.
`retained_denominator_positive` derives a positive denominator whenever
the source retains a finite tuple. An empty result takes the source drop
branch before the lazy kept-ratio value is needed.

`source_block_event` proves the event mass of actual decoder-ordered closed
points. It equals restriction of the original finite child-point block.
`settle_groups_condition` shows that kept-ratio updates, point closure,
and final normalization produce the conditioned finite block distribution.
Both results derive the mass equations from filters and counts.
They do not assume distribution preservation by a complete compiler.
Zero retained blocks contribute an empty list.

The finite probability result requires known exact child point counts.
An unavailable count remains a different case. The source uses one in its
denominator. `unknown_share` proves that one unknown child gives retained
share equal to the number of found points. This quantity can exceed one.
It describes density for later finite normalization, not a probability
distribution on an unbounded integer domain. A complete proof for mixed
unknown-count branches remains separate.

`buildBucket` follows open settlement and optional immediate closure.
Open settlement updates only outer mass. Closure also multiplies member
count and retained size mass by the point count, and adds the coordinate
count to size. `pay_close` proves that this size shift commutes with pay.
`closeOpenBucket` uses the actual counter and preserves the final source
branch order: a zero-width key skips counting, a counter error stays an
error, zero points drop the group, and nonzero points close it without
multiplying the already-settled outer mass again.

The parent formulas are inputs after `partFormula` translates guards.
This module does not prove the guard-to-formula translation, computed root
labels, complete observation transport, source grouping identities, or
all sparse mass-series operations. Child counter success and source count
record wiring remain explicit inputs. Metadata results concern the existing finite
size-class model. They do not prove the complete Haskell record wiring.

The temporary source probe `/tmp/microcfta-settlement-mass.hs` passed 108
symbolic-integer versus finite-pool descriptions. The cases vary relative
branch weights, pay counts, inner and outer restrictions, and measured open
parents versus closed parents. Three further cases bound an initially
unbounded integer leaf at its parent. The probe compares cardinalities,
global PMFs, counts and PMFs at sizes zero through eight, exact sampler
distributions, and all decoded original term ranks. Its log is
`/tmp/microcfta-settlement-mass.log`. It ran in the required Nix shell.
No source defect was found. No Haskell file changed.

Validation: `lake build MicroCFTA.ParentIntegerSettlement` succeeds with
the pinned toolchain. The theorem audit reports only standard Lean axioms.
The module has no added axioms or incomplete proofs.
