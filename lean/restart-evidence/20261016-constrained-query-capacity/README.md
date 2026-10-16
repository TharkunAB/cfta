# Numeric query-entry capacity checkpoint

Baseline: `a86c09dd`. Audited source main: `c0cc8a05`.
Source merge: `896b0a1c`. Proof commits: `baffd471`, `a66edeb5`, and
`bb913e55`. Read lean/notes-current-constrained-capacity.md for the full
objective, proof boundary, validation, and next target. Root FINDINGS.md
keeps the Haskell repair handoff first. This checkpoint changes no Haskell.

## Validation

Pinned Lean 4.34.1 passes the full Audit: 2551 jobs and 59587 dependency
checks. Thirteen new production modules have matching frozen snapshots.
The final all-public source and all-public-2.log check all 88 declared
public names, including indented mutual and noncomputable declarations.
The earlier all-public-1.log checked 84 names before that coverage expansion.
Component probes also check selected constructors and fields.
Thirty-nine imported integration pairs pass. All final selected probe logs
contain no error, warning, or placeholder. Only the permitted foundations
occur. Canonical builds retain the historical unused-input dependency warning.
Earlier failed direct and canonical attempts remain as raw diagnostics.

verify-checkpoint.py checks public coverage, paired signatures and axiom
reports, integration logs, component manifest hashes, frozen snapshots,
and the final canonical Audit. verify-preservation.py checks the starting
file map, all older proof sources, active Haskell files, historical repair
block, stashes, and other worktrees. Its report records the verification
phase HEAD. Do not rerun frozen evidence scripts after this package is
published. SHA256SUMS checks all package files from this directory.

## Scope

Numeric entry plans replace future native word checks through Target, Force,
Leaf, simultaneous edits, Class, Pass, Scan stage, precheck, Parent, and one
complete outer edge call. Initial readiness and causal certificates remain
separate inputs. Earlier raw prefix graphs select later entries. Their
reads and returned invariants are derived before the current query begins.

Primitive Work and atomic schedules count actual reservation actions.
Losing candidates still consume reservations. QueryReservations counts
actual raw yielded prefix requests. Its budget adapter does not supply a
static bound on all future reduction work. Constraint-interner and host
actions remain separate.

Ordinary source construction has static input-only reservation bounds and
constructs its own return. InitialCapacity composes these with complete
initial caller admission and actual field preparation. Later entries still
need their own numeric plans.

The frozen whole-root completion still requires OuterEntries.Plan. Read
outer-capacity-next-review.md: raw-Reach admission must first construct and
verify earlier prefix reads at the exact current state. Then numeric parent
plans can imply the global range plan. Initial-only total reduction budgets,
general Mu/reference/union progress, repeated-pass convergence, frontends,
concrete Haskell execution, and full pipeline remain open.
