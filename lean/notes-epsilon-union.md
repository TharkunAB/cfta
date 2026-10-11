# Recursive union repair

The old `union = Node . concatMap nodeEdges` discarded a bare recursive
operand. The repaired union retains open operands in `InternedUnion`.
The operands consume no term constructor. Substitution visits all operands.
Closed unions retain the existing concatenated-edge path.

`nodeEdges` follows recursive and union references with a visited identity
set. It gathers the constructor edges and removes duplicate edge identities.
A closed epsilon cycle with no constructor returns no alternatives. An open
union view reports an unresolved reference as an error. It does not report
that reference as an empty language.

`EpsilonUnion.Accepts` is an independent least finite-run relation with
constructor steps and epsilon steps. `eliminate_exact` proves exact language
preservation for finite epsilon elimination. It keeps every guard and every
ordered child. `union_exact` proves that a pure union state denotes exactly
its operands. `no_constructor_no_term` excludes terms created only by epsilon
cycles.

`visit` is a terminating depth-first worklist. Its available-state list is
the complement of the source's visited set. The termination measure is the
lexicographic pair of unvisited states and pending work. `visit_spec` proves
allocation, unique visits, pending-state coverage, successor closure, and
reachability. `visit_exact` gives both directions of reachability.
`collect_exact` connects the collected constructor rows to the independent
finite-run language. An ordinary row has no epsilon successors. The source
can read such a row more than once before its final edge deduplication; this
does not change membership.

The concrete interned representation still needs its finite-view refinement:
`unfoldOuterRec` must implement binder substitution, interned identities must
be faithful, and the reachable epsilon view must be finite. The closure
proof does not assume the language-preservation result it proves. It does
state its finite graph and representation inputs explicitly.

`OpenUnion.lean` retains the old failure at `d7f7c11` and checks the repaired
epsilon graph separately. The source reproduction now requires `wrap(a)`
to be accepted. Existing core tests cover nested enclosing references,
productive and empty epsilon cycles, closed graph conversion, intersection,
and template restriction. The complete suites pass with the representation
change. The supported node sum now includes `InternedUnion`; clients that
match raw interned constructors must cover this case. Ordinary closed union
construction still uses the existing `Node` representation.

Truncated diagnostic enumeration can stop at an interned union that retains
a recursive operand, as it stops at `Mu`. Complete finite denotation uses
`nodeEdges` and explicit height bounds. Equality propagation leaves a union
boundary intact when descending would unfold recursion. Its original
constraints remain available to concrete acceptance.
