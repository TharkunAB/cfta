# Finite Required exposure from actual union normalization

Updated: 2026-10-17 17:25 CEST.

The new finite_exposure theorem derives ExposureSafe for any Needed from
SemanticReady, an actual UnionNormal certificate, availability, cached
depth zero, and an empty free-name list. It assumes no finite-ordinary input
predicate, plain guard heap, or future successful Required computation.
Ordinary node guards can contain nonempty equality work.

UnionNormal states that every stored union fails ordinaryEdges. Actual
makeUnion stores a union only in this branch. First-writer readback retains
an earlier certified payload. Actual edge/node construction, self filtering,
Mu completion, and Mu requests retain the invariant. The repaired mutual
build/buildMany/buildEdges induction discharges every callback preservation
condition. It covers hits, pending reads, reservations, and fresh bodies.
Its public build, source, execute, and unfold endpoints have no future
callback or completed-result hypothesis. They apply at every stopping state.

The finite proof uses the existing Normal.flat and Normal.members fields.
A union member cannot be an empty or nested union value. Coherent free-name
metadata excludes a reference when the parent is closed. Coherent depth
metadata excludes Mu at depth zero. If all remaining members are ordinary
nodes, ordinaryEdges succeeds, contrary to UnionNormal. Ordinary children
inherit both metadata conditions, so availability induction derives their
own ExposureSafe certificates.

The old SemanticReady structure does not include UnionNormal. This package
does not assert the SemanticReady-only implication. It adds and derives the
separate causal certificate. No formal countermodel to that implication is
included. Callers must retain UnionNormal through actual effects. Arbitrary
heap growth alone does not establish it.

All 18 public definitions/theorems have imported full signatures, full
prints, and axiom checks with explicit proof printing and threshold 254.
The final logs have no omission markers, errors, warnings, or sorryAx.
Only propext, Classical.choice, and Quot.sound occur in successful checks.
Both production strict logs and the printer-free integration log are empty.
The final canonical build passes 1082 jobs. It replays one pre-existing
unused-input warning in InternedFreshOrdinaryClosedCompletion. Neither new
production source has a warning. Every execution used a 4 GiB cap and zero
swap. The final integration strict peak was 201 MiB.

Three constructed integrations pass. A closed syntactic union of two
constrained ordinary nodes normalizes to a finite ordinary result. It is
not source-unconstrained, and it supports every Needed. A raw binder stores
a genuine union containing a reference. Its actual warm Mu request returns
the existing winner despite a callback that would be pending, and actual
unfolding retains UnionNormal. A separately reserved incomplete Mu request
returns its actual pending key and retains the invariant without a
successful callback premise.

All failed immutable snapshots and raw logs remain. Union strict attempt 1
needed constructor/run reductions. Finite strict attempt 1 needed the
Option.map reduction. Kernel attempt 1 needed an explicit empty namespace,
removal of an unused helper, and reduction of a local witness. Kernel attempt
2 left local let definitions opaque to cbv. Kernel attempt 3 unfolds those
local definitions and passes. The failed logs are not validation evidence.
No production source outside the two new modules was changed. This package
does not establish general node-owner disjointness or outer termination.
