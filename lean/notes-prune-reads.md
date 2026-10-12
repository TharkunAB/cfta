# Open nested binder pruning repair

A valid closed automaton could throw an exception during pruning. Its open
nested binder contained an enclosing recursive reference in an outer union.
`readsThroughRecursion` called `nodeEdges` on that open binder. Outer closure
then reached the unresolved union reference and raised an exception before
the existing guard-retention case could run.

The concrete grammar is:

```
X = base | outer(a, Y)
Y = X | inner(a, Y)
```

The guard on `outer` observes path `[1,0]`. The observed node is the fixed
leaf `a`, so validation succeeds even though the path passes through a
recursive node. Before the repair, the standalone repro printed `Right ()`
from validation and `Yes` from recognition, then failed with
`nodeEdges: unresolved union reference RecInt 15` during pruning.

The source repair adds an explicit `InternedMu` case to `reaches`. A closed
binder still stops at the free-variable shortcut. For an open binder, the
check inspects its stored body. It does not call outer-edge unfolding. An
enclosing reference in an outer union is then detected by the existing Rec
case, and pruning retains the complete guarded edge.

The check terminates on ordinary interned finite shapes. A binder call enters
its stored body, whose nested-Mu depth is smaller. A union call enters a
stored member; `createUnion` flattens unions, and the stored member structure
is finite. An ordinary edge call enters a constructor child and a smaller
observation subplan. The check never substitutes a binder into its own body.
Bare references stop immediately. The closed-node shortcut avoids traversal
of closed cyclic graphs.

`MicroCFTA/PruneReads.lean` gives an executable model over finite stored shapes.
Its mutually recursive definitions pass Lean's structural termination check.
`reaches_exact` and `reachesChildren_exact` prove equivalence with an
independent relation that identifies planned reads through bare references.
`closed_binder` preserves the closed-node shortcut.
`enclosing_union_detected` proves the general repaired nested-binder case.
`guarded_outer_edge_regression` checks the actual `[1,0]` plan.
`detected_guard_retained` connects detection to the exact source semantic
retention branch.

The shape adapter represents cached free-reference sets by lists and sparse
child maps by indexed lists. The Haskell interning/finite-shape invariant and
cached metadata correspondence remain explicit representation obligations.
The model proves termination of this recursion-read check, not termination
of the outer recursive pruning fixed point.

Validation:

- The updated existing `PruneSpec` compares recognition and bounded concrete
  denotation before and after pruning.
- The focused Nix test filter `enclosing` passes two examples with no failures.
- The complete Nix suites pass 274 core, 190 generator and 135 refinement
  examples, with no failures.
- `lean/repro/PruneOpenBinder.hs` now prints `Right ()`, `Yes`, `Yes`.
- `fourmolu` was applied to the source, existing test, and repro.
- `cabal-gild` check passed.
- `lake build MicroCFTA.PruneReads` passes with no proof placeholders.
