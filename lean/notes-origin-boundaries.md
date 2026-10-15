# Inherited and physical-node boundaries for the next caller measure

The [closed caller cycle](notes-outer-caller-cycle.md), proved in `eed062bd`,
supersedes the unconditional rank target at the end of this historical note.
It uses main `239feb64`. The finite inherited and node-factor observations
below remain valid.

Proofs and reproductions: `b163ddd4`.
Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
Continue on `formalize` and push checkpoints. This note follows
[the finite physical constraint inventory](notes-constraint-inventory.md).

## Exact small normalization receipts

SourceEqualityNormalizationReceipt.fixMaybe_unique proves that any two
completed reference schedules return the same result. array_eq identifies
each completed reference receipt with the actual source array result.
observed_eq is an exact evaluation equation. It uses a small completed
receipt and retains the actual source call if that receipt is incomplete.
This equation avoids evaluation of the conservative normalization bound in
the retained kernel checks. It changes no production source operation and
adds no evaluation axiom.

## A fixed local constraint does not bound inherited propagation

Use the raw local classes `0 = 1.0.0` and `0.1 = 1.0.1`. Normalize them with
the actual source array operation. Read the resulting complete constraint
with its Top guard through the actual own-payload accessor. The maximum
path length in this fixed local payload is 4.

Start with EmptyConstraints. At each step, combine the current inherited
payload with that same local payload. Descend the actual physical result
through child 1. SourceEqualityInheritedGrowthBoundary.finite constructs
every finite prefix and its well-formed physical trie payload. Kernel
evaluation of the first five observations gives maximum path lengths
`[0,3,4,5,6]`. Three steps therefore exceed the fixed local bound of 4.

The first descended class is `{0.0.1, 0.1}`. Lift that readback to a complete
constraint with a Top guard for comparison. The complete source conjunction
closure of the original local constraint and Top contains exactly those two
values. Actual conjunction is idempotent on this normalized local constraint.
The lifted first inherited result is neither value. first_not_literal_derived
therefore rejects membership in that entire literal conjunction closure.

This does not contradict finite physical edge constraints. Inherited payloads
are separate records. Descent does not emit the lifted comparison constraint
as a new edge annotation. The earlier physical heap theorem remains intact.

[The retained Haskell reproduction](repro/InheritedPayloadGrowth.hs) checks
the exact classes through seven source steps. It reports `Just True` and
maximum lengths `[0,3,4,5,6,7,8,9]`. These are finite observations. No theorem
here proves infinitely many distinct inherited states. No outer node graph
is shown to reach every step of this recurrence.

## Repeated intersection does not absorb a repeated physical factor

Use these fixed closed unary inputs with Top constraints:

```text
A = mu x. a | u(x) | u(u(x))
B = mu x. a | u(u(x))
C = intersect B A
D = intersect C A
```

[The retained Haskell reproduction](repro/RepeatedIntersectionGrowth.hs)
checks distinct physical identities for B, C, and D. Their exact counts of
ordinary nodes, all physical nodes, and edges are `(2,3,3)`, `(4,6,7)`, and
`(12,19,26)`. It also checks closure and confirms that two actual local
equality prefixes return the same first children as these intersections.
The Nix run reports `Just True`. Absolute identities are allocated during
the run and are not a cross-run contract.

The unary grammars describe all finite unary a-chains for A and even-length
chains for B. That language calculation does not identify their physical
intersection results. In particular, a set of distinct source factors is
not a canonical physical key for repeated intersection. These two changes
do not refute every possible finite node inventory.

The two-prefix kernel candidate did not finish within more than three
minutes of verified evaluation. A smaller first-prefix candidate did not
finish within thirty seconds. Their exact running handles were stopped.
No kernel identity theorem was established. Both unverified drafts and
the limits are preserved at:

- `/tmp/mcfta-intersection-growth-boundary-draft-20261015.lean`
- `/tmp/mcfta-intersection-growth-first-kernel.lean`
- `/tmp/mcfta-intersection-growth-kernel-limit-20261015.txt`

The closing preservation snapshot includes them. No unverified theorem
is imported by Audit. The observations do not prove infinite growth or
nontermination. The manually repeated local products do not constitute
an actual recursive outer caller trace. That caller stops when it receives
a Mu or union input. A termination argument must retain this distinction.

## Validation and next target

The two new proof modules pass focused builds. The aggregate audit passes
1,890 jobs and 48,594 dependency checks with only propext, Classical.choice,
and Quot.sound. The older unused inputs warning remains. Log:
`/tmp/mcfta-origin-boundaries-20261015-audit.log`.

Both retained Haskell reproductions pass in Nix. Fourmolu and all three
active Cabal formatting checks pass. Logs:
`/tmp/mcfta-retained-inherited-growth-20261015.log`,
`/tmp/mcfta-retained-intersection-growth-20261015.log`, and
`/tmp/mcfta-origin-boundaries-format-20261015.log`.
The system compiler path avoids the Nix linker failure for libgmp.
No production Haskell changed. The earlier 650 examples, affected benchmark
build, and metadata checks were not repeated. Older proofs except audit
imports, counterexamples, marked drafts, stashes, and other worktrees remain
unchanged.

Next derive a decreasing rank or finite dependency argument for actual
constrained outer child continuations. Follow local narrowing, physical
combination and descent, Mu cleanup, returned ordinary children, and the
actual stopping branches at Mu and union. Test each proposed node-origin
bound against the retained source cases. Original ordinary height, original
literal conjunction closure for inherited payloads, and physical absorption
of a repeated factor are unavailable shortcuts. Do not assume a future
finite node inventory, completed caller graph, or successful receipt to
prove general existence.

General constrained caller termination, the outer reduction memo table,
open contexts, repeated fixed points, getAllAtPath, native containers,
GHC scheduling, and extraction remain open. Preserve Sized exact classes,
finite size execution, size order, both distinct rank inverses, the optimized
interned core, and older constructor and equality proofs.
