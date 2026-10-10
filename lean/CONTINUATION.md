# Formalization after the first repairs

Audited Haskell revision: `ae6b97b8a8fc9282999c031671b743f8983786a3`.
This revision contains three repairs:

- `b7b1a95`: repeated paths in `Holds` share one semantic value.
- `cb770b0`: minimization skips changes that could invalidate observed guards.
- `ae6b97b`: reconstruction retains a top-level atomic size boundary.

All three original reproductions now give their intended results. The
continuation adds four proof modules and finds two remaining correctness
problems. It does not modify the Haskell implementation.

## Original cases after the fixes

| Case | Verified result |
| --- | --- |
| Repeated-path self-equality | `Yes`; compiled cardinality `Right 1`. |
| Observed top-level atomic choice | Sizes remain `[1,1]`; bounded PMF remains `[(0,1/2),(1,1/2)]`; neither member gains a smaller peer. |
| Disequal children under similarity reduction | Both `minimize` and `reduce` retain `f(a,b)`. |

Run [the original checks](repro/Counterexamples.hs) against this revision.
The old [findings report](FINDINGS.md) records the behavior before these fixes.

## New proofs

### Alias construction is sound and complete

[Holds.lean](MicroCFTA/Holds.lean) computes the first index of each path. It
also models the left-to-right insertion that retains the earlier formal name.
It proves that both computations agree, that every alias lookup exists, and
that the emitted equalities enforce exactly one value per mentioned path.

`compiledQuery_iff` proves equivalence between the emitted query and that
path-based meaning for arbitrary formulas and either polarity. It covers
empty target lists, repeated targets, and inconsistent refinements. The proof
uses the finite set of mentioned paths and requires no inhabited-value premise.

Source: `Refinement/Evaluate.hs`, `firstNames`, `aliases`, and `assumed`.
Remaining boundaries: formal-name freshness, capture-free substitution,
Fixpoint formula interpretation, the Haskell map implementation, and SMT.

### The new guard classification preserves accepted guards

[Minimization.lean](MicroCFTA/Minimization.lean) models `guardReads` and its
polarity rules. `classified_guard_preserves` derives preservation from atomic
semantics: monotone reads receive stronger refinements, sensitive reads keep
their refinements, structural reads keep their terms, and path presence stays
the same. These conditions preserve acceptance. They need not preserve a
negative solver answer: stronger assumptions can turn `No` into `Yes`.

This validates the local classification rule. It does not prove that the
Haskell graph traversal establishes these conditions. It excludes substitution
scopes. The `Subtyping` oracle must establish the needed refinement implication.
The remaining representative-emptiness defect below is independent of this
local guard-preservation theorem.

### Counted plans preserve exact rank order

[Decoder.lean](MicroCFTA/Decoder.lean) gives separate list semantics and an
executable counted decoder. The counter sums choices and multiplies products.
The decoder uses offsets and quotient/remainder. `decode_correct` proves
agreement at every rank, including rejection outside the valid range.

`decode_normalize` proves that map pushing and choice splicing preserve every
rank. This preserves arbitrary weighted replay distributions. The module also
proves the one-argument, one-function, and fused binary-application fast paths.

`compileAt` compiles a plain automaton at a height bound into a plan.
`countAt_correct`, `decode_compileAt`, and `compiled_coverage` connect its
counting recurrence and normalized decoder to the independent accepted-term
semantics. `compiled_probability` preserves event masses; the normalized
probability theorem requires an accepted term within the bound.

Sources: `Ranked/Internal/Decoder.hs` plan normalization and decoding, and the
plain sum/product structure of `Gen/Internal/Table.hs`. The bound here is
height, not the Haskell table's node-count size. The graph can be cyclic because
each recursive call decreases the height bound.

The proof retains duplicate runs. It does not claim uniform distinct terms.
It computes cardinalities rather than trusting supplied metadata. Finite list
sources, binary choices, and natural ranks replace Haskell callbacks, n-ary
dispatch maps, and machine integers. Shared decoder caches, `PlanSized`, and
the concrete recursive size tables remain unverified.

### Reconstruction must preserve the source size

[Sized.lean](MicroCFTA/Sized.lean) models source-choice sizes, product sums,
labels that do not add a choice, and atomic boundaries. It proves that the
top-level atomic repair preserves all annotated masses and size-conditioned
event probabilities for that case.

It also proves that reconstruction from term shape does not retain arbitrary
sizes. An explicit alternative, `rebuildRetained`, retains the original size
beside the reconstructed term. The proposed retention gives exact-size counts,
bounded cardinalities, conditioned probabilities, and the same strict-smaller
relation. Its grouped version preserves smaller-member collections up to order.
This proposed reconstruction is not implemented by `ae6b97b`.

The concrete first-key partition algorithm is proved to flatten to a
permutation of the original list. Thus its coverage and multiplicity are
proved, rather than supplied as premises. Positive member masses justify
sampling its normalized buckets in proportion to bucket mass.

## Remaining finding 1: observed non-atomic sources still change size

Source: `Gen/Refinement/Internal/Compile.hs`, `groupBuilt`, `rebuild`, and
`withChildren`.

The patch only consults `staticAtomic` at the top level. It still rebuilds
other members from their term forest. Source-choice size is not the number of
term nodes: `node` labels a generator without adding a source choice.

The new reproduction passes a choice through `ungroup . keyed ()`, which
retains its data but makes it a `Built` source. Its two values are leaf `a`
and `wrap(b)`. Neither requires an atomic marker to have size one.

```text
source sizes                 [1,1]
sizes after observation      [1,2]
PMF at bound 1, before       [(0,1/2),(1,1/2)]
PMF at bound 1, after        [(0,1)]
```

A built product containing an atomic child fails more strongly:

```text
source sizes                 [2,2]
sizes after observation      [3,4]
PMF at bound 2, before       [((0,7),1/2),((1,7),1/2)]
PMF at bound 2, after        Left EmptyGenerator
```

Both use a tautological observation. The new proofs establish the mathematical
reason, and the Haskell reproduction confirms the current implementation.

Proposed repair: retain each original member's size and mass when partitioning
and rebuilding it. A top-level atomic flag cannot recover nested boundaries or
the distinction between labels and source choices. A singleton size-indexed
plan is one possible representation; no production repair is included here.

## Remaining finding 2: an empty representative can remove all solutions

Source: `Refinement/Minimize.hs`, `hasFiniteDerivation`, `losesFinal`,
`productiveStates`, and their interaction with `Prune.hs` residual guards.

Let a representative `a` have refinement `v >= 0` and a guard that rejects
every concrete term. Let `b` have refinement `true` and an accepting guard.
The standard `refinementSubtypingOn` adapter correctly proves that the declared
result type of `a` is a strict subtype of that of `b`. This strict relation
makes the reproduction independent of interning order.

The root has alternatives `f[A]` and `f[B]`. Only `f(b)` is accepted.
Minimization removes `b` and redirects its parent to `A`, which is structurally
productive but semantically empty. The parent guard check passes because the
parents have no constraints. The result has no accepted term.

The simple guard `Satisfies [] false` demonstrates the direct `minimize` bug.
Pruning removes that representative, so `reduce` preserves the simple example.
However, pruning can retain an unresolved guard. The stronger reproduction
uses simultaneous substitutions of two distinct compound actuals with the
same root observation. Sparse substitution identity is unknown. The pruner
retains the guard, while complete evaluation rejects the representative.

```text
original denotation          {f(b)}
prune kept original          True
pruned denotation            {f(b)}
denotation after reduce      {}
```

`RejectedRepresentative.guarded_representative_counterexample` proves that
a before/after graph can lose every accepted finite term while remaining
structurally productive. The Haskell reproduction establishes the actual
rewrite and the residual-substitution case. The Lean module does not verify
the sparse substitution evaluator or the complete minimizer.

Proposed repair: require semantic nonemptiness of each chosen representative,
in addition to context compatibility. Structural reachability and an unresolved
guard do not provide an accepted witness. Preserve a safe fallback when this
obligation cannot be established.

## Reproduce and validate

From the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc lean/repro/Counterexamples.hs'
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc lean/repro/RemainingFindings.hs'
```

The first artifact checks the repaired cases. The second prints the remaining
counterexamples. Full `Data.Tree` output corresponds to the abbreviated terms
above. Both artifacts use Z3.

The complete Lean package and transitive axiom audit pass. Existing Haskell
suites pass with 261 core, 182 generator, and 128 refinement examples: 571
total, zero failures. The new reproductions expose cases outside those tests.
