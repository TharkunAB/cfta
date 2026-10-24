# Concrete source constraint projection

Updated: 2026-10-24.
Main: `74250bd889685da436cdbfe32ac4b5a0878ffd09`, incorporated.
Proof: `1847ec2e577a9931918163716751427db2e098e2`.

## Actual equality and residual fields

The projection reads the complete source Constraint. It uses the actual
sourceEqualities accessor. A contradictory accessor result has no projection.
This checked absence does not model an enumeration rejection or the native
unsafe class-read exception. A guard that fails positive extraction retains
the stored equality payload and the complete original constraint as residual.
It is not an unsupported projection.

Positive Top, distinct-path Same and positive conjunctions omit the residual.
Reflexive Same remains residual because its path must exist. Bottom can have
a present projection with a false residual. Absence is not a decision procedure
for every unsatisfiable complete constraint.

The class list retains its source order. The existing readClasses operation
constructs one trie per class after removing duplicate paths. The stored Cached
invariant and the actual accessor derive nontrivial consistent classes.
The proof derives trie construction success, validity and exact path membership.
It excludes the classTrie's empty fallback for these actual source classes.

## Complete meaning

The returned equality tries and residual have exactly the original complete
constraint meaning for every modeled finite term and all formula and solver
parameters. EqualityHolds requires one existing subtree at every class path.
The positive branch obtains this meaning from the actual source accessor.
The residual branch retains the complete constraint. Acceptance supplies its
equality requirements. The reverse direction follows from that residual.
No callback law, desired output or Graph correspondence is assumed.

## Model and runtime boundary

The projection inherits the existing noncomputable source equality accessor.
That accessor selects a sufficient finite array-normalization bound through
an existing theorem. This result proves the concrete mathematical projection.
It does not supply an extracted executable normalizer or native container bridge.
Paths use natural indices. Native negative paths, overflow and formula encoding
remain outside this theorem. External solver correctness remains separate.

## Validation and preservation

The first strict input fails on one unused simp argument in the residual branch. The second input removes only that argument. It passes with a literal empty log under all linters and warnings as errors. The original input, failed output and exact correction remain. The selected source, complete public readback, installed build and Audit all pass. All 41 public-output lines retain both complete signatures. No proof limit changed.
The installed build passes 597 jobs. Audit passes 3690 jobs and
76149 dependency checks, with the unchanged older replay warning.
Both declarations report exactly propext, Classical.choice and Quot.sound. No project axiom is added.
The exact declarations, scoped types, defining cuts, independent reviews,
complete raw attempts and capped receipts remain. No proof limit changes.
The baseline has 130607 tracked files. The previous shallow-child checkpoint's
26 actual post-seal inputs remain, including its assessment and summary.

## Remaining scope

The actual per-edge worker still needs inherited arity checks, equality-variable
allocation, suspended descent, ordered child preparation and final residual
insertion. Terminal child merging and default canonical or weighted edge choice
remain separate. Stored identity order does not establish default term order.
Native graph/ID/index/memo2, complete enumeration/pruning, concrete typing,
lazy callbacks and scheduling, global histories, resources, practical width,
extraction, runtime/solver correspondence and convergence remain open.

H6 constructed_node_calls remains strongest combined under its stated scope.
H23 and older constructor/equality targets remain. No Haskell source change.
FINDINGS keeps all six imported Haskell repair handoffs first. All earlier
proofs, counterexamples, repairs, marked drafts and the optimized core remain.
The full goal stays ACTIVE and incomplete. This note precedes evidence and push.
