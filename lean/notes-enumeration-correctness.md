# Concrete suspended enumeration

`MicroCFTA/EnumerationCorrectness.lean` extends the executable actions in
`EnumerationState.lean`. It reads those definitions directly. It does not use a
separate transition relation with assumed preservation laws.

The source is `microcfta/src/Data/CFTA/Enumeration.hs`. `UVarValue`, suspended
path tries, union-find representatives, allocation, intersection, assimilation,
node merging, residual obligations, and fragment rendering retain their source
roles. The graph interface supplies node views and graph intersection.

## Checked laws

- `initial_semantics` identifies the initial state with its root language.
- `representative_semantics` preserves all complete assignments under actual
  path compression. `union_semantics` adds exactly the requested equality.
- `allocation_semantics` adds one fresh optional node restriction.
  `suspendMany_exact` follows the actual `mapM suspend` call and consecutive
  identifiers. `suspendMany_semantics` preserves the prior restrictions.
- `intersection_semantics`, `assimilation_semantics`, and `mergeNode_semantics`
  state exact equivalences for the concrete stored slots. The accompanying
  `assimilate_exact` and `mergeNode_exact` identify actual successful state
  actions. Graph intersection uses the explicit `IntersectionCorrect` graph
  interface law. This is a graph primitive obligation, not an assumed
  enumeration transition law.
- `fresh_classes_exact` proves that fresh suspended variables encode precisely
  the original equality classes. It constructs their witness assignment and
  preserves every earlier variable value.
- `StorageValid` records the array length, finite forest support, terminating
  representatives, and bounds on every stored suspended variable and fragment
  hole. `initial_storage`, `allocation_storage`, `suspension_storage`,
  `representative_storage`, `union_storage`, `assimilation_storage`,
  `mergeNode_storage`, and `guard_storage` prove the corresponding concrete
  preservation laws. `findRoot_bounded` follows actual path compression.
- `state_assignment_congr` proves that changing fresh variables cannot affect
  any old slot or guard. `fresh_classes_state_complete` combines that law with
  the constructive equality witnesses. It derives old-state preservation from
  the storage invariant.
- `edge_equalities_from_children` reconstructs all edge equality classes from
  their descended child requirements. `edge_rule_sound` applies the finite
  graph acceptance rule with ordered children and its residual predicate.
  This rule is not a theorem about successful `enumerateEdge` execution.
- `empty_check_sound` proves that structural-empty rejection cannot remove a
  satisfying slot in the finite graph denotation.
- `getValue_success` characterizes the actual read and compressed state.
  `expandFragment_sound` and `expandUVar_sound` use fuel induction over the
  actual rendering actions. They prove that successful rendering equals the
  fragment completion or assigned UVar term and preserves the state semantics.
  `NoMarkers` explicitly excludes pending recursive marker branches.
- `descend_avoids`, `fresh_avoids`, `representative_avoids`, and
  `union_avoids` prove the local protected-class laws.
  `assimilation_frame` and `mergeNode_frame` prove that concrete writes retain
  a separate protected slot. These laws do not establish scheduler selection.

`Accepted` is an inductive finite-term denotation. An edge requires all ordered
children, all represented equality paths, and its residual predicate. A
recursive graph view requires acceptance by its exposed body. The predicate
does not admit diagnostic recursion markers.

## Source boundaries and remaining proof obligations

The full `runs` soundness and completeness theorem is not yet proved. The
primitive preservation laws do not establish the entire scheduler invariant.
In particular, `enumerateOut` stores its completed fragment into the selected
root after recursive child enumeration. The proof must establish that the
scheduler selected a live representative with no incoming suspended
references. It must then show that child allocation, union, assimilation, and
node merging cannot alias or modify that protected root before the final
write. The terminal-equality merge loop must restore the invariant that only
representatives have live slots. Storage bounds alone do not imply these facts.

The scheduler's `stuck` rejection also needs the reachable-state facts that
turn all blocked work into strict subtree dependencies. The existing
`strict_dependency_stuck_impossible` theorem applies once those facts are
established. It does not establish them itself.

The raw Lean `Graph` accepts arbitrary edge tries. Actual `mkEdge` rejects
contradictory classes and classes that exceed the edge arity. `enumerateEdge`
checks the inherited suspended paths. It relies on `mkEdge` for its own new
classes. `edge_equalities_from_children` states trie validity and the new-class
arity requirement explicitly. `raw_graph_arity_required` executes the driver
on a raw zero-arity edge with a child-zero equality. It returns the leaf, but
the finite accepted language is empty. The source constructor rejects this
graph. Thus an unconditional theorem for arbitrary raw `Graph` values is false.

The graph interface must connect `IntersectionCorrect` to the complete
interned intersection implementation. Recursive and open-union exposure must
also be connected to the corresponding graph views. The model's recursive
view records an exposed body; it does not distinguish every interned source
constructor.

Finite execution fuel reports errors. A total correctness theorem must supply
sufficient fuel rather than identify fuel failure with an empty language.
Residual guards remain paired with their fragments until the caller checks
them. The ordinary diagnostic enumerator truncates repeated recursion and
can emit markers. Full finite recursive-language completeness belongs to the
separate ordinary term enumeration path, not to marker output.

No Haskell extraction or external runtime equivalence is claimed. These proofs
use the checked executable Lean source model and explicit graph primitives.
