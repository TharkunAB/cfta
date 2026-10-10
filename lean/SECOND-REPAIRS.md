# Formalization after the second repairs

Audited Haskell revision: `adb1f012b336ba0d1673f8fd7f310ad75bdfaf04`.
The spike branch was rebased onto this revision without conflicts. Both prior
local commits retained their patches. The backup branch is
`backup/lean-before-rebase-20261010-1620`.

The earlier reproductions now pass. Two public correctness defects remain:
an observation can change bounded atomic-pair probabilities, and minimization
can delete the initial state's only accepted alternative. This continuation
adds Lean proofs and standalone reproductions. It does not change production
Haskell code or establish soundness of the complete implementation.

## Verified repairs

- `bf0c370` rejects the earlier semantically empty representative. Both direct
  minimization and reduction retain the accepted term, including the case in
  which pruning retains an unresolved substitution guard.
- `8fa39f0` retains each rebuilt member's source size. The non-atomic and nested
  atomic cases retain sizes `[1,1]` and `[2,2]`, respectively. Their bounded
  probabilities and smaller-member results now agree with the originals.
- The later changes retain per-size masses through grouping and integer
  closure, remove the artificial pairing choice, and count each integer leaf.
  The new proofs below verify finite versions of these operations with
  explicit ordering, mass, and point-table requirements.

[Counterexamples.hs](repro/Counterexamples.hs) checks the first repairs.
[RemainingFindings.hs](repro/RemainingFindings.hs) checks the second repairs.
Their original findings remain in the historical reports.

## Public finding 1: an observed atomic pair loses its bounded weights

Construct an atomic choice between `a = 0` and `b = 1`, with weights 9 and 1.
Pair it with a constant leaf `c = 7`. Add a tautological observation of child
zero. Both outcomes have size two before and after compilation.

```text
                              (0,7)    (1,7)
original PMF                   9/10     1/10
original PMF at bound 2         9/10     1/10
observed PMF                   9/10     1/10
observed PMF at bound 2         1/2      1/2
```

The observation accepts every member. It must not change these probabilities.
This case uses public `Gen.Refinement` functions and does not invoke an
explicit grouped join with a separate weighting policy.

In `Gen/Refinement/Internal/Compile.hs`, `groupBuilt.sourceWeight` returns
`Nothing` for an atomic source. Its singleton observation buckets therefore
lack `keyedBucketMasses`. The scalar bucket masses retain 9:1 for unbounded
sampling. Pairing makes non-atomic buckets. Their size-class merge falls back
to member counts, which are 1:1, and loses the relative atomic masses.

`SizeMass.atomic_pair_count_fallback_changes_probability` proves the exact
9/10 versus 1/2 difference. `split_merge_probability` proves why retaining
each bucket's original mass prevents this loss in the finite model.

Repair direction: retain atomic group masses on the appropriate per-size
scale through pairing and merging. A singleton's normalized local weight
cannot represent its original share of the source class.

## Public finding 2: minimization can delete the only accepted root term

Let the initial state contain the accepted leaf `b : true` and an alternative
`f[A]` whose guard always rejects. State `A` contains an unconstrained leaf
`a : v >= 0`. The standard subtyping adapter proves that `a` is a strict
subtype of `b`, which fixes the rewrite direction independently of interning.

The representative `a` passes `unconstrainedBelow` and remains accepted.
However, the rewrite deletes `b` from the initial state. Redirecting incoming
child references does not put `a` at the initial state. The surviving `f[A]`
keeps that state structurally productive, so `losesFinal` does not reject the
rewrite. No root term is accepted afterward.

With a simple `Satisfies [] false` guard, direct `minimize` fails. `reduce`
first prunes the rejected alternative, so its structural check prevents the
loss. A second case uses a substitution guard that pruning retains as
unresolved. This case also fails through `reduce`:

```text
original language             [b]
prune kept original           True
language after prune          [b]
language after minimize       []
language after reduce         []
```

Source: `Refinement/Minimize.hs`, `copyAlternatives`, `applyStep`, and
`losesFinal`. The retained-guard construction is in
[CurrentFindings.hs](repro/CurrentFindings.hs).

`Productivity.RootDeletion.root_deletion_counterexample` proves that the
representative passes the executable below-check, the original root accepts
a term, the representative remains accepted, and the final root is
structurally productive but rejects every finite term. The reproduction
establishes that Haskell performs this rewrite; the whole schedule is not
formally translated.

Repair direction: preserve an accepted representative at the initial state
when a rewrite removes an initial transition. A conservative option is to
skip such cross-state rewrites. Representative productivity alone cannot
establish the required root property.

## Internal limitation: product indexing assumes positive operand sizes

The exposed internal `productIndex` prepends a zero count at size one and
marks recursive occurrences as guarded. Both operations assume that each
operand consumes at least one source choice. `PlanSized` can now represent
size-zero components.

```text
operand sizes    stored product counts    lookup at actual size
0 and 0          [(1,0),(0,1)]            0
0 and 1          [(1,0),(1,1)]            0
1 and 0          [(1,0),(1,1)]            0
```

Each example contains one member. Lookup stops at the leading size-one entry
and misses it. Pairing a recursive probe with a size-zero sibling also clears
`isUnguarded`, although the recursive call does not decrease the size.
`productMassIndex` uses the same size-one prefix. The new finite
`pairMassIndex` omits it.

These are confirmed internal precondition failures. Public compiler
reachability is not established: public `pure` has size one, and integer
closure adds the variable count to its internal zero-size placeholders.
The positive-size invariant at each recursive product remains a proof
obligation. Removing the prefix globally could break lazy recursion.

`Sparse.seeded_product_correct` proves the prefix is safe for strictly
ordered finite operands with sizes at least one. The two adjacent
counterexample theorems prove its failures at zero. `ZeroSize` also proves
that a zero-size sibling does not decrease recursive size and that a seeded
same-size recurrence with a recursive copy has no finite natural count.

## New proof coverage

| Module | Checked result | Explicit boundary |
| --- | --- | --- |
| [Productivity.lean](MicroCFTA/Productivity.lean) | Finite fixed-point convergence; exact descendant closure; structural productivity with cycles; accepted representatives from the concrete below-check; root-deletion counterexample. | The state list covers the whole modeled finite state type. Clear metadata implies a true guard. The below-check and productivity use the same graph snapshot. Haskell checks intermediate and final graphs, so schedule preservation and the finite-table embedding remain unproved. |
| [SizeMass.lean](MicroCFTA/SizeMass.lean) | Exact count-scaled member weights; nonnegativity, normalization and positive support; product splits; repeated merges; concrete key partition and split/merge probability preservation. | Live group masses are positive. Local weights sum to group count. Sparse support and the Haskell sampler callbacks must satisfy these invariants. |
| [Sparse.lean](MicroCFTA/Sparse.lean) | Executable sparse merge and convolution equal independent full-sum semantics. They preserve strict key order. Lookup equals the size-split sum for natural counts and rational masses. | Finite lists, nonnegative sizes, and strictly increasing input keys. Zero coefficients are allowed. Lazy infinite series and recursive knots are outside these proofs. |
| [ZeroSize.lean](MicroCFTA/ZeroSize.lean) | The corrected split limit preserves the complete ordered pair list, including zero-size components. Integer closure adds variable count, multiplies cardinality, preserves support, and has exact replay ranks and size counts. | The finite integer-point table supplies exact coverage and injective tuple ranks. The lattice counter, `pointRank`, and `fillHoles` correspondence remain unproved. |

These strengthen the existing language, decoder, alias, and probability
proofs. They do not verify all Haskell callbacks, the observation trie,
intermediate graph rewrites, infinite size tables, SMT, machine integers,
randomness, or the complete lattice eliminator.

## Validation

- A clean build passes with the pinned Lean 4.34.1 toolchain. The package has
  374 named source theorems, including 114 added in this continuation. The
  automatic audit checks 970 theorem declarations, including generated
  declarations, and permits only the three standard Lean axioms.
- Existing Haskell suites pass: 263 core, 182 generator, and 136 refinement
  examples; 581 total, zero failures.
- All three standalone audit artifacts run in the project Nix environment.
  The earlier cases pass. The current artifact reproduces both public defects
  and the separate internal limitation above.
- Fourmolu accepts the artifacts. Cabal-gild accepts both packages.

Run the new artifact from the repository root:

```sh
nix-shell --run 'export PATH=/usr/bin:$PATH; cabal exec -- runghc lean/repro/CurrentFindings.hs'
```

The host compiler path is the same workaround for this WSL host's existing
Nix/GHC `-lgmp` linker failure used in the earlier audit.
