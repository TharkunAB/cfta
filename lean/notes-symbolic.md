# Symbolic finite equality counting

Source: `cfta-generator/src/Data/CFTA/Gen/Internal/Symbolic.hs` on
`tidy/core-formula`. The module counts distinct terms. It does not count
accepting runs. Its rank order uses constructor arity, the supplied key, and
then the symbol. This last comparison preserves distinct constructors when
user keys are equal.

## Checked correspondence

`MicroCFTA/Symbolic.lean` contains executable operations and their proofs.
The coefficient map uses a list of entries. `collect` combines equal keys.
`trim` removes zero coefficients. These operations model `Map.fromListWith`,
`Map.unionWith`, `Map.insertWith`, and the final zero filter. The model does
not implement the balanced tree storage of `Data.Map`.

| Source operation | Model and checked result |
| --- | --- |
| `countUnion.add` | `addAlternative`, `unionCoefficients`, `union_indicator`, `union_count` |
| Distinct intersection keys | `weighted_insert`, `weighted_collect`, `weighted_trim`, `collect_keys_nodup` |
| Intersection omission | `ExactMeet` requires every omitted intersection to denote the empty set. `finiteMeet_exact` proves this for concrete list languages. |
| `Fragment`, `Target`, `Obligation`, `Problem` | Explicit datatypes, `instantiate`, `targetValue`, `Satisfies`, and `Solution` |
| `edgeObligations` | `classObligations_correct`, `edgeObligations_correct`. A singleton class retains its path-existence requirement. |
| Normalized `resolve` | `resolveContext_sound`, `resolveContext_absent`. Unbound variables with a nonempty path request expansion. |
| Constructor-prefix removal in `normalize` | `followContext_sound`, `followContext_absent` |
| Substitution through bindings | `instantiate_substitute` |
| Equality ordering and identical targets | `equality_symmetric`, `self_equality_iff_exists`, `empty_path_exists` |
| `solveStep` with no obligations | `independent_product_count` |
| Variable-variable `unify` | `variable_intersection`, `equalProduct_members`, `equalProduct_count`, `equalProduct_nodup` |
| Constructor-constructor `unify` | `constructor_equality` |
| Proper-subtree rejection | `occurs_reject`, using the finite-tree path-height theorem |
| `project` | `projectStates`, `projection_covers_subterms` |
| Singleton projection in `selectAt` and `rankAt` | `singleton_projection_shortcut` |
| Meaning of `condition` | `conditioned_members`, `constructor_blocks_disjoint`, `constructor_blocks_cover`, `conditioned_nodup` |
| Constructor block choice in `selectAt` | `selectBlock_correct`, `block_count_correct`, `selectBlock_none_iff` |

`union_indicator` proves the complete left fold over alternatives. It does
not assume that the final cardinality is correct. At each candidate term,
the resulting signed sum is exactly zero or one. `union_count` then exchanges
the finite candidate sum and the signed coefficient sum. With a complete,
duplicate-free candidate list, its result is the number of distinct terms.
The finite list is a semantic reference. The Haskell implementation does not
construct it.

The pointwise intersection law remains an explicit interface in the generic
proof. It is discharged for `finiteMeet`. `Language.lean` separately proves
synchronous constrained-automaton intersection. No checked translation yet
connects interned Haskell edge identity and `intersectEdge` to that interface.

## Solver branches and remaining driver proof

The full bounded operational counter and rank driver is now in
`MicroCFTA/SymbolicDriver.lean`. Its count, decoder, inverse, overlap, nested
constraint, and negation examples are checked. See
[notes-symbolic-driver.md](notes-symbolic-driver.md) for its exact scope.
The later composed proofs discharge the internal obligations listed below.
See [notes-symbolic-semantics.md](notes-symbolic-semantics.md) for current coverage.

`countEdge` applies the signed guard interpretation to independent child
domains and the generated path obligations. `solve` normalizes the problem
before it consults the context cache. The cache key contains every remaining
domain identity and every normalized obligation. It must retain free domains:
`dropping_free_domain_changes_count` gives a checked example where deleting
an unobserved domain changes six assignments into two.

A normalized existence obligation either fails on an absent path, requests
variable expansion, or is removed after successful resolution. Equality
fails on an absent target, requests either needed expansion, or calls `unify`.
Different resolved variables merge their domains by intersection and retain
an alias binding. Equal constructor symbols and arities generate one equality
per child. Variable-constructor equality requests expansion unless the occurs
check rejects a finite tree equaling its proper subtree.

`expandVariable` replaces one domain variable by the children of one outgoing
edge. It binds the old variable to that constructor context. It appends the
edge's path obligations and processes the alternatives by inclusion-exclusion.
The fresh names must not collide with live domains or bindings. Normalization
then renumbers the domains and removes the bindings.

This module contains the local laws. The complete counter, normalizer,
selection, and inverse theorems now use them in `SymbolicTotalAPI`.
`SymbolicCacheIndependence` and `SymbolicPublicAdapter` prove the shared-cache
API. Concrete runtime representations and source readback remain boundaries.

The shortcut theorem uses the actual upper-bound relation of `project`. It
shows that every existing subtree of an accepted term equals the unique
projected term. It does not treat projection as exact: ancestor constraints
can remove projected alternatives.

## Complexity

The counter does not enumerate complete terms in the source. This fact does
not imply a polynomial bound for arbitrary overlaps and equality contexts.
`exponential_intersections_example` computes fifteen different nonempty
intersections from four alternatives. Collection and zero removal preserve
counts, but they cannot merge genuinely different intersections. No general
time or memory bound for the whole symbolic driver is asserted.

## Validation

Both `MicroCFTA.Symbolic` and `MicroCFTA.Construction` build with the pinned
Lean 4.34.1 toolchain. No proof uses `sorry`, a new axiom, or native evaluation.
The coefficient examples cover duplicate alternatives, three-way overlaps,
and fifteen distinct intersections. The context examples retain singleton
path existence and unobserved independent domains.
