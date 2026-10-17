# Compiled emitter input certificate review

Reviewed on 2026-10-17 at 06:59 CEST. No material defect was found. No production source was changed. The reviewed source is `SourceRecursiveIntersectionCompileMassInputs.lean`, SHA `81b035d24ecd56417cf9d8ee955b57cb770ba70fda4140fffa643c6270253705`.

The three public declarations are `rows`, `le_square`, and `union`. The proofs produce local `WorkMass.Inputs` certificates for the literal node and union emitters. They do not claim full recursive-query completion or a global prefix invariant.

`rows` takes the initial complete store, both available original values, a retained initial-to-current numeric bound, an actual completed ordered row walk, and current residency of that walk's exact returned list. `WalkTrace.length` identifies the returned list length with the actual source hash-join request count. `node_pairs_mass` bounds that count by the product of the complete original operand masses. Each original mass fits the retained current bound, so the list fits its square. `Inputs.node` retains the exact current returned rows. The proof does not replace those rows by identities or assert an unproved future result property. A current store premise is unnecessary for this list-width certificate; current residency is explicit.

`le_square` requires a positive natural bound. That condition is necessary for the intended nonzero bound proof and is obtained from the actual complete store in `union`.

`union` takes the literal available original union, the original complete store, an actual completed member walk, current result availability, current complete store, and numeric retention. The original union's complete mass bounds its literal member count. The actual walk keeps exactly one output position for each member. The original bound fits the current bound, which fits its square. `Inputs.union` therefore certifies the literal returned list in its actual current heap. The proof uses the current store for positivity. It assumes no desired union result, output shape, callback law, future range plan, or completed enclosing query.

The current `WalkTrace`, retained bound, and residency or availability premises remain explicit local prefix obligations. They must be produced during a full query proof. This module does not by itself produce them for every recursive query. Its current bound is a common mass bound, not the native machine word width.

## Independent imported integration

`constructed_row_inputs` constructs an outer source node from empty storage. Its children are two distinct source nodes. Both have three rows; two rows share symbol zero, while their third rows share symbol one and have different guards. The actual same-symbol hash join emits five ordered pairs. Literal generic kernel edge execution performs all five zero-arity calls. The selected conjunction retains the first guard, so the resulting rows are exact existing source records. The kernel derives its own completed `WalkTrace` from that actual walk and derives current residency from the original source Facts and parent availability. It applies `rows` with `currentBound = initialBound + 1`, then applies `Inputs.physical` and `WorkMass.run_bound` to the exact emitted node work. No walk, width certificate, future result, or initial physical fact is supplied to the theorem.

`constructed_union_inputs` constructs an explicit union of a recursive Mu and an ordinary node from empty storage. It derives source Facts, original availability, and both member availability proofs. Two literal closed-self kernel requests return their original members and the exact same machine. Their actual execution constructs the ordered `WalkTrace`. The kernel applies `union` at the retained larger bound, derives the physical Work input check, and applies `WorkMass.run_bound` at the actual union emitter. It also proves exact warm `makeUnion` replay to the same original union and heap. The input list has two members. There is no supplied completion or desired emitter certificate.

Both fixtures use generic Nat/Bool source symbols and guards. They test the local generic kernel and Work interfaces used by these certificates. They do not assert checked equality-operation execution, a new native memo theorem, or full-query resource closure.

## Validation

`compile-inputs-review-public-1.log` contains all three explicit full-signature and axiom pairs. `compile-inputs-review-kernels-2.log` contains two substantive pairs. Both imported checks exit zero with no warnings, errors, holes, truncation, or nonstandard axioms. Failed evidence attempt 1 remains with its exact source and raw log. It failed only on evidence-level unfolding of the deliberately larger numeric bounds and a concrete inequality proof. Attempt 2 passes.

The first evidence-verifier attempt rejected the declaration scan because its name matcher included a trailing newline after `union`. The matcher now stops at every whitespace character. Its failed script and raw log remain unchanged. The final verification passes. This issue did not affect Lean source or imported proofs.

The exact production strict source check is `compile-inputs-direct-2.log`, which is empty. Its preserved source snapshot matches the reviewed production hash. The canonical copy `compile-inputs-review-canonical.log` completes 1185 jobs. Its only warning is the older unused `inputs` binder in `InternedFreshOrdinaryClosedCompletion.lean:24`.

Reviewed dependencies are `SourceRecursiveIntersectionCompileMass.lean`, SHA `78b3f1797c112d78ac26b372d94bf3f2e5d6f61b2a92094900e73caeac402287`, and `SourceRecursiveIntersectionWorkMass.lean`, SHA `2683ffd0d82b254bd5a91bc6fe6d0fd929af4856afa1ec51aea749eb88f41b3e`. The supplied source mass and actual walk count are separate from current returned payload mass. No counter difference is used as a work-count surrogate. This review changes no Haskell code and establishes no new Haskell defect.
