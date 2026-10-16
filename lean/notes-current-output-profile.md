# Native output profiles and serial constructor reservations

Updated: 2026-10-16. Source main is c0cc8a05, merged at 896b0a1c.
This checkpoint starts at published a3db345a. Proof commits are 1c24089f
and 5f2bf869. Root FINDINGS.md keeps the external Haskell fix handoff first.
No Haskell file changes.

## Full objective

Prove that the current Haskell library implements the intended constrained
tree languages and generators. Retain separate language, termination,
transformation, exact size, count, order, both rank inverses, probability,
frontend, runtime, and pipeline contracts. No whole-library theorem is
complete. Keep the optimized interned core and all older constructor and
equality proofs, counterexamples, repairs, and marked drafts.

## Returned native certificates

OutputStored relates each returned result to its own stored request.
For an empty seen list and both operand profiles R,A, the node result has
profile R*R,max(A,1). The edge result has the same profile. The predicates
bound every ordinary descendant, not only the top row list. Requests outside
these conditions impose no profile obligation.

Empty tables derive Stored without result assumptions. Lookup, demand,
machine advance, and protected finish preserve it. Finish requires a local
producer certificate for the exact evaluating owner. A warm hit identifies
its complete captured request before it reads that owner's certificate.
This lifecycle result alone does not prove the producer.

OutputConstructors derives profiles for actual makeEdge and makeNode
results. Coherent cache hits retain the requested complete children or
canonical rows. Empty-child filtering and canonical selection cannot add
rows. Ordered All₂ results retain their exact list length and profiles.

## Actual producer trace

OutputCode gives each recursive call its own conditional result certificate.
OutputNode proves the actual node dispatcher and joined rows satisfy the
local code certificate. The source join emits at most R*R row pairs.
OutputEdge proves accepted child zips, rejected sentinels, arity mismatch,
and actual checked-body yields satisfy their local certificates. Guards and
combined fields have no added restriction.

OutputExecution interprets those certificates on the actual checked trace.
Strong induction uses shorter actual body traces. Each body derives its
profile before its protected finish installs the result. Frames retain the
exact evaluating owner through intervening calls. Warm hits use the initial
or earlier derived OutputStored certificate. No successful recursive callback,
supplied result profile, or historical eager execution is a public input.
The node and edge trace endpoints retain OutputStored at the same returned
checked state and derive the actual returned value's profile.

The max(A,1) arity is necessary for a common node and edge bound. A rejected
edge contains one Empty child, including when the original arity is zero.
This is the intended source sentinel. It is not a new Haskell defect.

## Initial profiles reserve later native queries

ProfileBudget proves that computed literal row and arity limits fit every
uniform input profile. The complete native constructor budget is monotone
in row count, arity, and height. Thus an R,A,H profile bounds the literal
computed query budget by N(R,A,H), with the existing recurrence:

```text
N(R,A,0) = 1
N(R,A,H+1) = 1 + R*R*(1 + A*N(R,A,H))
E(R,A,H) = 1 + A*N(R,A,H)
```

OutputFinite.finite constructs its own physical receipt from initial Good,
semantic readiness, old structural Stored, OutputStored, Idle, resident
operand profiles, a height bound, and initial constructor headroom.
The same receipt supplies final Idle, semantic readiness, both stored
invariants, the output profile, both original height bounds, empty free names,
final capacity, and both supply increments. OutputFinite.cold derives both
stored invariants and Idle from literal empty native tables.

OutputFinite.serial constructs two actual queries. The second uses the first
returned result and the original right operand. With initial profile R,A,H,
reserve N(R,A,H) + N(R*R,max(A,1),H) before either query. The first receipt
derives the second operand profile, residency, cache invariants, and remaining
headroom. The final profile has row limit (R*R)*(R*R) and arity max(A,1).
The second result's profile or completion is not supplied.

This is a conservative whole expansion. It counts repeated occurrences and
does not require memo savings. It is not a polynomial complexity result.

## Remaining caller accounting

The native returned-profile gap is closed. The outer numeric plan is still
an explicit premise. Projection can concatenate selected row lists. Merge
can enlarge descendant row lists when it builds child columns. Domain and
height alone do not supply the required row limits.

Read next-cumulative-profile-review.md in the evidence directory. Next prove
actual Projection forest profiles, height, and constructor counts. Then prove
Required profile retention and the memo-aware Merge producer profile and
reservation. A reentrant keep-first Merge finish must use the stored winner's
bound, not its losing candidate's bound. Compose Operand and the literal
rotated Target right fold before edits, class passes, local/parent calls,
and outer reduction. Thread the new native output invariant through these
actual returns. Do not assume the numeric plan that this accounting must prove.

The current native domain admits arbitrary guards and equality classes.
It excludes Mu, references, and explicit unions. General recursive progress,
repeated-pass convergence, current frontend adapters, concrete Haskell
execution, and full-pipeline composition remain open. Constructor Work does
not account for equality-interner, sidecar/domain/thunk resources, storage,
unrelated host interleavings, losing concurrent candidates, or repeated lazy
forcing. Modeled packed-key bounds do not prove signed host-counter bounds.

## Validation and preservation

Pinned Lean 4.34.1 passes the full Audit: 2570 jobs and 59925 dependency
checks. All 54 declared public axiom/full-signature pairs and 21 integration
pairs pass. Declaration coverage includes Unicode All₂ names and named
sections. Final diagnostics checks include both error: and error(...) forms. Only propext,
Classical.choice, and Quot.sound occur. The canonical build retains the older
unused-input warning. Evidence is in
lean/restart-evidence/20261016-constrained-output-profile/.

Preservation retains 6867 starting files and 2561 older non-Audit sources.
Forty-one frozen manifests check 327 module entries. Seven restart authorities
and one additive Audit import may change. Historical repairs, counterexamples,
drafts, stashes, other worktrees, and the optimized interned core remain.

No Haskell change. Reuse strict Nix validation, 798 examples plus golden,
six-file Fourmolu, and four-package Cabal-gild and metadata checks. Repair
b9219b9e is already merged by PR #65. Add each later Haskell repair first in
root FINDINGS with failure, reproducer, paths, commit, checks, and upstream
status. The full-library goal remains active.
