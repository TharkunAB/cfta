# Original constraint origins and the outer height boundary

Proofs: `c77bb8c4` and `56c94073`.
Source: `TharkunAB/cfta`, `origin/main` at `33148e6d`.
Continue on `formalize` and push checkpoints. This note follows
[closed warm completion](notes-closed-warm-completion.md).

## A closed normalized counterexample to ordinary-height descent

Use the class `0 = 1`. Let `a` be an ordinary leaf. Two raw unused binders
have bodies `{left(), p(a,a)}` and `{right(), p(a,a)}`. Each `p` edge has
that nonempty equality class. The original root is
`root(w(rawLeft), w(rawRight))`, with the same class on its two children.
The binders use the public createMuDontCleanup constructor. They are closed.

The gate reaches the ordinary `w` endpoints. It returns false there without
visiting the constrained binder below each endpoint. Native intersection
then removes the unused binders and retains their common constrained `p`
body. It returns `w(p(a,a))` at each child position.

MergedOrdinaryHeight stops at recursive boundaries. The original caller
root has height 2. Its original children have maximum height 1. The actual
local prefix returns children with maximum height 3. These children exceed
the original caller root, before its recursive continuation starts.

SourceEqualityPartialHeightBoundary proves source closure and normalized
literal payloads. actual_heights uses kernel evaluation of repaired source
construction and the actual guarded-edge worker. At word width 16 and stage
bounds `(4,4,2,2,2,64)`, it returns exactly `(2,1,3)`. The proved source array
normalizer equation supplies the computational reduction rule. No native
evaluation axiom is used. not_parent_height_bound rejects the proposed bound.

[The retained source reproduction](repro/PartialReductionHeight.hs) calls the
actual reduceEdgeIntersection and reducePartially implementations in Nix.
It reports `(2,1,3,4)` and `Just True`. Both narrowed children retain their
nonempty inner equality payload. Node reconstruction after the local prefix
is identical to the completed public single pass. The focused probe therefore
confirms the same boundary in the live implementation.

The expanded exploratory sweep completed all 147 closed cases. Its log is
`/tmp/mcfta-outer-origin-expanded-20261015.log`. The minimized retained fixture
is the source evidence for the stated counterexample. No case in that sweep
establishes general termination. This example refutes a proposed measure and
the assumption that every newly exposed recursive part is equality-free.
It is not a termination counterexample or a source defect.

## Constraint closure through actual native execution

SourceRecursiveIntersectionConstraintClosure proves a stronger physical heap
rule. The conjunction rule requires the property of its two actual operands.
The compiled edge reads both resident source guards from the real returned
child heap. It then checks the emitted conjunction. Arity mismatch uses the
actual empty guard. Native Bounds.constraint_heap follows cold bodies, warm
hits, optional binders, completion frames, and later continuations.

SourceEqualityConstraintClosure carries the rule through actual captured
projection, merge, first-seeded right folds, first forcing, and target reuse.
SourceEqualityConstraintEditClosure uses the actual mutual edit graph.
SourceEqualityConstraintPassClosure composes required paths, selected classes,
the native fold, final empty propagation, and literal guarded reconstruction.
Every intermediate physical scope comes from actual completed effects.

These proofs require no unconditional property of arbitrary conjunctions,
final constraint heap, future scope, or whole-operation preservation law.
The earlier annotation theorems and all their source contracts remain intact.

## Original source inventory and finite exact local completion

SourceEqualityConstraintOrigins.guards reads a finite literal inventory from
the actual source syntax. It includes complete guards inside both raw and
smart binder bodies. constructed derives the initial physical constraint heap
from that inventory. closed derives initial Scope and closed available input
from original normalized source construction, without a supplied build result.

Derived records an original literal, source Top, or the actual source
conjunction of two derived constraints. complete composes the real finite
guarded prefix with this relation at an arbitrary closed warm scope. The
returned heap has only derived constraints. It also has both source gate memo
receipts, recursive Scope, both histories, closed resident children, stable
six-stage execution, narrowing, and exact public language under inherited
satisfaction. Actual reached native word ranges remain explicit.

Only the literal inventory is proved finite. Its conjunction closure is not
proved finite. These origin derivations are not a decreasing measure. General
outer recursion still needs a separate termination argument or counterexample.

## Validation and next target

The six new Lean modules pass focused builds. The aggregate audit passes
1,882 jobs and 48,456 dependency checks with only propext, Classical.choice,
and Quot.sound. Only the older unused inputs warning remains.
Log: `/tmp/mcfta-constraint-origins-20261015-audit.log`.

The retained Haskell fixture compiles and passes in Nix. Fourmolu checks it.
All three active Cabal formatting checks pass. No production Haskell changed.
The earlier 650 examples, affected benchmark build, and metadata checks were
not repeated. Older proof bytes except audit imports, counterexamples,
marked drafts, stashes, and other worktrees remain unchanged.

Next carry the original literal inventory through the actual outer recursive
graph. Use the real local prefix, physical combination and descent, returned
child scopes, Mu cleanup, row tails, and modifyNode. Connect this origin
invariant to checked bounded caller success. Then study a measure that
accounts for constrained bodies below ordinary selected endpoints. Do not
assume a future origin heap or caller graph to claim general existence.

General constrained caller termination, the outer reduction memo table,
open contexts, repeated fixed points, getAllAtPath, native containers,
GHC lazy scheduling, and extraction remain open. Preserve Sized exact classes,
finite size execution, size order, both distinct rank inverses, the optimized
interned core, and older constructor and equality proofs. No Lava or Rocq
dependency is added.
