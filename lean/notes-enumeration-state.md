# Suspended-path enumeration driver

`MicroCFTA/EnumerationState.lean` is an executable port of the stateful driver
in `cfta/src/Data/CFTA/Enumeration.hs`. It uses the checked `EqualityTrie`,
`UnionFind`, and `Fragments` models. The state contains the fresh-name supply,
representative forest, value slots, residual obligations, recursion ancestry,
and current expansion ancestry.

The port includes allocation, suspended-class construction, representative
lookup, raw slot writes, slot assimilation, node intersection, node and edge
enumeration, the expandable-variable scan, ordering hints, one-variable
expansion, the complete oracle caller loop, recursion-cycle truncation,
partial rendering, concrete rendering, and `runs`.

The graph interface gives each node an identity and a view. A recursive view
gives its unfolded outer body. Intersection is a graph operation. These
interfaces separate the driver from interning and binder substitution. Their
semantic correctness is not assumed as a theorem about Haskell.

## Proved invariants

- `suspended_decomposition` proves that the arity check, root equations, and
  all descended obligations preserve exactly the inherited path constraints.
  Valid trie structure is an explicit requirement.
- `arityAllows_maximum` connects the executable arity predicate to the source
  maximum-child-index check.
- `pickNext_safe` proves that a caller's ordering hint cannot select a blocked
  or unavailable variable.
- `strict_dependency_stuck_impossible` proves that a finite nonempty set of
  strict subtree dependencies cannot all be blocked under a complete finite
  tree assignment. `EnumerationProgress` derives the required slot and
  dependency facts for the actual reachable caller states.
- `allocate_exact`, `allocated_supply`, and `allocated_slot` prove the fresh
  slot update and preservation of the supply/length invariant.
- `bound_is_not_empty` distinguishes an execution bound from branch rejection.

## Checked complete-driver examples

`equality_driver_exact` executes the complete state machine for two equal
children. It returns both equal pairs and no mixed pair.
`nested_equality_driver_exact` executes nested path descent, rejects the
alternatives with an absent path, and retains both valid equal pairs.
These theorems use kernel-checked evaluation of the executable driver.

`residual_is_retained` executes a leaf with a false residual guard. The run
contains the leaf and the unchanged false obligation. The caller must decide
that obligation. Projecting the term from a run is not an acceptance test.

`recursion_marker_not_acceptance` executes an unproductive recursive
constructor with no base case. The driver returns the caller's marker even
though the finite-term language is empty. `repeated_recursion_clears_constraints`
executes the repeated-key branch and shows that its pending constraints are
cleared before rendering a marker. These behaviors match the source's stated
truncation contract. They are not counterexamples to that contract.

`constrained_recursion_is_hole` verifies that diagnostic rendering keeps a
recursive slot with pending constraints unresolved.
`unconstrained_recursion_no_callback` verifies that an unconstrained binder
receives no oracle callback.

## Representation and remaining boundaries

Sequences and maps use finite lists or finite-map functions. Path tries use
the checked trie representation. The recursion key uses a sorted list of
interpreted trie paths in place of the source's hash set. Canonical valid
tries are required to identify these representations.

The source has no explicit fuel parameter. The model uses bounds for recursive
execution and union-find lookup. Insufficient fuel returns a distinct error;
it does not produce an empty success result. `EnumerationExact` now constructs
a sufficient stable bound for every accepted finite term under the complete
graph and exact-intersection contracts.

The source checks only inherited path arity in `enumerateEdge`. Its new local
equality classes already satisfy the `mkEdge` arity invariant. The model keeps
this order. A graph supplied directly to the model must meet the same invariant.

`EnumerationExact.runs_exact` now composes union-find storage, assimilation,
scheduler invariants, expansion, and final rendering. It proves exact finite
term support after returned residual checks. Its graph contracts still need
the source adapters. The ordinary unbounded level enumerator is modeled in
`LevelEnumeration.lean`. Diagnostic recursion markers retain their separate
contract. See [notes-enumeration-exact.md](notes-enumeration-exact.md).
