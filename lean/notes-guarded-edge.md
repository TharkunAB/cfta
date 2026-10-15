# Actual guarded-edge reconstruction and source guard readback

Updated: 2026-10-15 07:04 CEST.
Proofs: `5ac49f0a`, `dbd22112`, and `70d3e67c`.
Source: `TharkunAB/cfta`, `origin/main` at `f201deda`.
The retained traversal repair is `61f2c939`. Continue on `formalize`.

The unrestricted source guard-law target below is now discharged at the
existing independent PCS meaning. Public agreement holds on normalized
annotations. Original construction and optional binders derive the annotation
heap. Native and shared-edit output annotation preservation remains next.
Read [the current note](notes-normalized-annotations.md).

## Actual source payload

Equality/Operations.hs rebuilds reduceEdgeIntersection with the original
edge symbol, reduced children, and complete original edgeConstraint.
Constraint.hs equalities reads staged positiveEqualities. It retains the
stored payload for absent positive syntax and the EmptyConstraints shortcut.
Otherwise it runs combineEqConstraints. Reflexive Same remains residual.

SourceEqualityGuardReadback.NormalClasses records active, consistent,
canonical classes. Cached is the corresponding optional payload invariant.
Completed mkEqConstraints, the actual bounded parent-array normalizer,
source combination, empty shortcuts, and sourceEqualities derive it.
It describes source representation, not a supplied language law.

accepted_equalities proves complete constraint acceptance implies the actual
accessor equality indicator. Positive guards use the staged normalization
semantics. Residual guards retain the stored equality conjunct. The support
theorem derives the accessor branch. value_exact and accepted_sat convert the
indicator to independent existing-path equality satisfaction.

SourceEqualityPhysicalPayload.read runs the actual recordsOf class builder.
It retains contradiction and the malformed-trie failure text. Completed source
normalization derives successful trie construction, canonical path readback,
coherence, nontriviality, and exact physical payload satisfaction. own reads
the actual edge constraint. own_complete derives the own facts needed by the
complete native pass. No guard-to-payload or whole-edge language premise is used.

## Literal edge function and graph

SourceEqualityGuardedEdgeGraph.Graph retains actual own readback, the complete
native child pass, and literal makeEdge. Ranges checks only the actual payload
and the reached child native word requests. The constructor retains the original
symbol and complete guard. Its returned heap advances the same native state.

SourceEqualityGuardedEdgeWorker retains accessor errors, child errors, and
actual incomplete child observations. It resumes edge reconstruction only
after successful complete children. runArray retains actual parent-array
normalization. WorkerProofs derives successful function/graph agreement in
both directions, stable six-bound execution, eventual array agreement, and
uniqueness of the rebuilt edge and entire native state.

Effects derives final idle native validity, semantic cache readiness, constructor-cache
histories, edge residency, exact children, and closed children. Constructor
readback derives the literal symbol and full guard. It does not assume that
edge interning returns the requested payload on a canonical hit.

## Independent guarded-edge language

SourceEqualityGuardedEdgeLanguage.language gives unconditional output inclusion.
Under inherited equality satisfaction, input and output edge meanings agree.
The original complete guard is retained. Its acceptance supplies own class
satisfaction through actual accessor semantics. Contradiction, unchanged, and
live branches use the complete one-pass theorem.

The theorem retains clearTrue, topTrue, and conjoined from the generic native
language proof. These are explicit constructor contracts. The new theorem does
not establish them globally for arbitrary raw Constraint values.

## Concrete constructor laws and the next boundary

SourceEqualityConstraintConstructors.conjoin copies source conjoinConstraints:
stored equality combination and canonical outer guard merge. Top is the literal
empty-equality Top constraint. top_cached, conjoin_cached, top_true, conjoined,
and plain_true derive physical invariants and public evaluator laws.
The conjunction and plain truth laws require normalized stored operands.

singleton_storage_boundary checks a malformed stored singleton at a missing
path. The public stored equality indicator rejects it. Source combination
normalizes that singleton away. This input is outside the source representation
invariant. The example explains why the normalized local law cannot discharge
an unrestricted law quantified over every raw Constraint.

Next prove the invariant on actual original annotations and retain it through
constructor-cache growth, native conjunction, and shared edits. Restrict the
generic language proofs to actual reached guard payloads. Discharge each local
law with the concrete normalized constructor theorem. Do not hide this boundary
with an unrestricted assumption or claim completed full Haskell correspondence.
Then connect inherited descendant processing and the complete reducePartially
traversal. Repeated fixed points, open contexts, getAllAtPath, concrete native
containers, GHC lazy scheduling, and extraction remain separate.

## Original source entry and kernel checks

SourceEqualityGuardedEdgeSource.complete derives finite execution from the
actual source node, semantic constructor heap, closed children, stored payload
invariant, and actual reached ranges. It retains both source gate memo call
graph certificates. source_edges derives cache and closed-child premises from
original closed construction. source_edges_exact combines source completion
and independent guarded-edge exactness with its explicit local contracts.

Examples checks reflexive Same residual readback, zero-bound unchanged and
contradiction branches, actual makeEdge allocation, full original labels, exact
children, and unchanged native memo counters. An unresolved child is deliberately
retained by the unchanged branch. This checks branch control without claiming
closed semantics for that fixture. A local classical equality instance is never
forced by the checked empty edge cache.

A proof-file elaboration check found that section type-class binders written
through local type notation omitted their Formula parameter. Lean then omitted
the theorem declarations. Explicit types in those section binders fixed the
problem. All five worker theorems are checked in the imported environment.
No compiler option or placeholder remains from the diagnostic.

## Validation and preservation

All ten new modules pass focused Lean 4.34.1 builds. The aggregate audit passes
1,782 jobs and 47,576 dependency checks. Only propext, Classical.choice, and
Quot.sound occur. Only the older unused inputs warning remains.
Log: /tmp/mcfta-guarded-edge-20261015-audit.log.
Snapshot: /tmp/mcfta-guarded-edge-checkpoint-20261015-0704/.
It retains 2,186 Lean-tree files and four root documents. Older proofs except
audit imports, all counterexamples, marked drafts, production source, stashes,
and other worktrees are unchanged. The earlier 645 Haskell examples and formatter
checks apply to the unchanged source and were not rerun.

The Lava paper motivates explicit function and graph agreement. Its call-by-value
theorem and assumed termination do not supply the finite bounds proved here or
GHC lazy execution correspondence. No Lava or Rocq dependency is added.
