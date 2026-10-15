# Main 54f4c272: template exclusion

Current source main is `54f4c272e72c0ab4c9457d56c66653459f5c6f31`.
The preserving merge is `29c6cfc7`. The prior proof checkpoint is
`7489c506`. Backup reference:
`backup/formalize-before-main-54f4c272-20261015-1802`.

The upstream delta changes five files. It adds template exclusion to
`Data.CFTA.Template`, its changelog, and three existing test modules.
Equality reduction, conservative emptiness, Sized, native operations, and
generator source remain unchanged. All Lean definitions remain unchanged.
The captured-task proofs and their source limits therefore retain their
previous scope. Read [their next target](notes-source-emptiness-tasks.md).

## New API and intended contract

`matchesNone templates term` rejects a term if any template matches it.
`exclude` filters an interned node. `excludeFTA` filters an explicit automaton.
`Obligation wanted unwanted` records the templates that each result-state
term must match and those that it must not match.

The required public law is:

```text
term belongs to exclude templates input
  iff term belongs to input and matchesNone templates term
```

This is exclusion at the root. It does not independently forbid matching
descendants at every position. Transition annotations remain unchanged.
The stronger internal law retains original terms that match all wanted
templates and none of the unwanted templates.

The empty template list is an identity. Hole or AnyPrefix [] excludes all
terms. Wrong root symbols and incompatible arities have no effect. A
forbidden matching nullary root yields no transition copy. Duplicate
templates and their order do not affect accepted terms. Nontrivial interned
traversal requires bound recursive inputs; its raw Rec branch raises an
error. Identity and trivial-rejection shortcuts can bypass that branch.

`edgeCopies` partitions a transition by the child-template matches. It keeps
an unwanted parent template active while all earlier children match it.
At each child it records which remaining templates match and which fail.
A copy with an unwanted template still active after the final child is
discarded. Hole parts force a match. A template must fail at its last
constrained child if all later parts are holes.

## New proof obligations

Existing Lean Template matching and restriction proofs remain valid.
Their source definitions are unchanged. They do not verify exclusion.
There are no Lean definitions or proofs for the new exclusion worker yet.
Constructor callback templates are a separate feature.

First prove that edgeCopies is a complete disjoint partition of concrete
child forests with the required parent matches. Prove exact child counts,
all index bounds, forced-hole and last-constrained-child cases, and unique
satisfiable copies. Prove canonical obligation normalization preserves meaning.

Then prove explicit cyclic FTA acceptance by finite-run induction. Derive
finite reachable obligation closure and ranked validation. Connect interned
nodeEdges, setChildren, and node construction to the same language law and
actual cache effects. Derive recursive completion from finite template depth
and the actual head-unfolding behavior.

Disjointness must establish unambiguity separately from language equality.
The source tests permit ambiguous run multiplicities to change through
interning and equality sharing. They check retained language and no new
ambiguity for terms with one input run. Do not claim general run-count
preservation or bypass existing count/rank eligibility checks.

This adds a target to the full library coverage. It does not replace the
captured-task semantic invariant, progressive row demand, checked native
transfer, general completion, other public API gaps, or runtime correspondence.
Keep the optimized interned core and all earlier proofs and counterexamples.

## Validation

The repository instructions require Nix validation. The strict build covers
all libraries, executables, tests, and benchmarks with -Werror. All six test
suites pass 704 examples plus golden checks. Fourmolu passes for all four
changed Haskell files. Cabal-gild passes for the four active package files.

Logs:

- `/tmp/mcfta-main-54f4c272-build-tests-format-20261015.log`
- `/tmp/mcfta-main-54f4c272-metadata-20261015.log`

All Lean source files are byte-identical to the prior checkpoint. The full pinned
audit passed 2,014 jobs and 51,484 dependency checks with permitted axioms
only. It was not repeated. Sized source is unchanged; its prior separate
rank probes were not repeated. Source production definitions match main.
Only the retained constructor changelog entry and caller-repro comment differ
in the package trees. All repros, drafts, stashes, and worktrees remain.
