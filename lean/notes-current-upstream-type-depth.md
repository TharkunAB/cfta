# Current main incorporation and proof impact

Updated: 2026-10-24. Refreshed main:
`a5fbb66eec52b8c28a4beacd982f00626c9e279a`.
Merge on formalize: `65f237954c3e867570c06d2de22681f55ca64fcd`.
The refresh at 01:38 CEST found no newer main commit.

All current main commits are ancestors of formalize. The latest merge imports
PR #168, which rejects negative type-depth bounds. Upstream repair
`75cfc19b8af8f8814e9f4f26b5abcae0dd9a26ad` has the same source as local repair
`058b11fe8f3706460156d7a1fc454063406a4634`. The merge therefore changes no
file bytes or modes. The formalize tree before and after this merge is
`e5c76044861f4945a83eea3351e61960d3515d7d`.

The earlier functionality import is also retained. It includes partial
enumeration, phase-4 program enumeration with incremental typing, refinement
memoization within each exclusion, and optional term orders. Read
`notes-current-upstream-program-enumeration.md` for the source evaluation,
native counterexamples and validation. That historical report predates the
upstream repair and the checked enumeration bridge.

## Formal coverage

The checked model now includes the shared bounded enumeration driver.
`EnumerationUntilBridge.no_stop_eager_successes` proves that its no-stop,
identity-narrowing, eager specialization has the same ordered successful rows
as the earlier eager model. The theorem retains duplicate rows and complete
final states at the same finite bound. It requires read-only callbacks and
the same modeled scan scheduler. See `notes-current-enumeration-until.md`.

The actual Haskell selector reads cached expandable and canonical waiting
indexes without compressing representative paths. The older modeled scan
can compress paths. Equal offered choices alone do not establish equivalence
of the complete drivers. The next proof target is the canonical cache
invariant and the observation relation for this difference.

The other source obligations remain explicit:

- Partial results can contain holes with no accepted completion. Complete-term
  acceptance theorems do not apply without a completion argument.
- Phase 4 needs typing and narrowing preservation, pruning preservation,
  type-alternative correlation, and runtime correspondence.
- Refinement memoization needs transparency and isolation between exclusions.
- Parallel state merging and cancellation need source correspondence.
- Optional LPO still has the retained comparator transitivity and application
  context defects. KBO remains the default. No LPO repair is claimed.

H6 `SourceCurrentColdFiniteWarmCalls.constructed_node_calls` remains the
strongest combined execution and finite-tree language theorem under its
existing premises. This refresh does not remove the full-pipeline, resource,
machine-width, solver correspondence or convergence gaps. The goal is active.

## Validation and preservation

The latest merge has the same complete tree as the preceding checked
checkpoint. No Haskell or Lean implementation changes in this refresh.
The prior checks remain applicable to those exact source bytes: the CFTA
suite passed 325 examples, the Specftacular goldens passed, strict library
builds passed, and the focused negative-depth and enumeration probes passed.
The goldens cover phase 1. The small phase-4 probe covers its signature only.
The subsequent Lean bridge passed strict checks and Audit.

Those checks were not repeated for this identical-tree merge. Current
verification checks main ancestry, tree identity and preservation of tracked
sources, drafts, evidence, stashes and worktrees. The external repair index
remains first in FINDINGS. It now records PR #168 as merged, with no external
import action required. Both LPO repair requests remain open.

Evidence for this status correction is in
`restart-evidence/20261024-upstream-type-depth`. The preceding sealed evidence
is unchanged. Earlier reports retain their historical main identifiers.
