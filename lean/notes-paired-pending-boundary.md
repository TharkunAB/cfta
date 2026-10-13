# A closed constructor expression reaches a pending key

Updated: 2026-10-13 16:29 CEST.

The unrestricted closed constructor no-pending statement is false for the
source executor model at upstream `9508eb3`. `InternedClosedPendingBoundary` gives a closed
expression made only from lexical variables, smart binders, raw binders,
ordinary nodes, unions, and empty nodes. No callback inspects a reference.
`expression_scoped` proves that every variable is in scope. `pending_result`
proves that execution from empty caches stops at a pending key.
`not_all_closed_complete` refutes universal scoped closed completion.

`pending_slot` checks the exact stopped state. Both key components are
ordinary node reference 86. Identity 87 is reserved for that pair. Its
record is absent. The next node counter is 92.

The expression has three parts. Actual enclosing callbacks produce the
captured names. A crossed binder changes its ordinary level through the
existing nested cleanup effect. A target binder uses that changed local
and both relevant enclosing captures. Discarded node edges keep all these
construction effects. The active ancestor returns a different surviving
operand with the same pair as the later target. That target reads the
ancestor reservation before its body record is complete.

Context marker edge 42 separates earlier probe histories. The target node
11 contains its ordinary local and two enclosing captures. The ancestor's
node 11 contains the corresponding existing ordinary capture and the same
context fields. These fields prevent earlier closed wrapper callbacks from
installing the target pair before the relevant reservation. Simpler closed
wrappers complete because they install that pair earlier. Their failed
pending assertions are diagnostic evidence, not retained theorems.

The preceding checked results remain valid:

- `InternedPairedProbeReplay.pair_equal` proves exact equality of both
  normalized probes under a direct replacement of one captured interned
  name, when both current probes omit that name and all calls complete.
  Depth equality also identifies the actual ordinary callback arguments.
- `InternedPairedRouteBoundary` shows that this result does not extend to
  an entire route whose crossed ordinary levels change. Both later target
  probes omit the fresh ancestor reference, but both pair components differ
  from the earlier target probes. `targetPair_prefix` retains the actual
  ordered source calls. A closed wrapper retains the changed route and both
  complete target records and returns empty.
- `InternedPairedPendingBoundary` checks a smaller pending expression with
  explicitly supplied captures `[Depth, Unint 0, Unint 1]`. It stops at the
  pair `(Unint 1, Unint 1)`. These open captures alone do not establish a
  closed-source defect. The separate closed module supplies that evidence.

The exact earlier and current joint-key witnesses, indexed producer paths,
and enclosing pending-callback theorems are preserved. The new example
shows that their remaining mismatch case can occur. It cannot be excluded
by another unrestricted no-pending theorem for this executor.

## Native source validation

Two independent Haskell translations of the closed marked expression fail
to return within an internal five-second timeout. One translation evaluates
the source syntax. The other uses named binder callbacks directly. The
direct translation times out while forcing the root to WHNF, before any
`freeVars` or `numNestedMu` traversal. Both use the actual source constructors.
The original closed level-change control completes immediately as EmptyNode.
The simpler tagged closed candidate also completes.

These runs used GHC 9.14.1, `-O0 -threaded`, the Nix/cabal source package,
fresh processes, `+RTS -N1`, and an outer 15-second process limit. The
constructor source files match `origin/microcfta` at `9508eb3`. The source
evidence establishes bounded noncompletion. The kernel theorem separately
establishes the precise pending outcome of the formal executor.

The translations are in `/tmp/mcfta-paired-pending-open.hs`. The detailed
native report is `/tmp/mcfta-paired-pending-source-validation.md`.
The exact precursor closed Lean expression is
`/tmp/mcfta-paired-pending-closed-marked.lean`; its durable version is
`MicroCFTA/InternedClosedPendingBoundary.lean`.

## Validation and next obligation

The four new baseline modules build with Lean 4.34.1. Their focused audit
checks 9,584 theorem dependencies and permits only `propext`,
`Classical.choice`, and `Quot.sound`.
The log is `/tmp/mcfta-paired-pending-audit.log`.
All earlier proofs, counterexamples, and the marked unfinished draft remain
unchanged. This baseline adds no Haskell source change.

Local repair `e0e1b37` chooses an ordinary placeholder above the
ordinary names free in the Depth probe. Constructor readback must use that
same choice from the stored Depth probe. Using the actual body's depth
does not recover it. The repaired executor completes both fixtures. Native
validation and proof boundaries are recorded in
[the repair note](notes-fresh-ordinary-candidate.md). This counterexample
remains evidence for the preserved pre-repair executor.
