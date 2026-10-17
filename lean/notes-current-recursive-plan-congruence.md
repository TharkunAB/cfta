# Recursive normalized construction and stored substitution

Proof commit is `6cef8154`. Source main is `c0cc8a05`, merged locally at `896b0a1c`.
Read notes-proof-status-20261017.md for the whole-library target and gaps.
This checkpoint extends node-row congruence through every nested constructor.
It does not derive the required relation from arbitrary retained Mu writers.

## Initial recursive plan congruence

SourceCurrentNormalizedPlanRelation defines a pure recursive relation.
Node rows match by occurrence in both directions. Their orders and duplicate
counts can differ at every nested depth. Each paired row keeps its exact
symbol and complete guard. Children and union members keep their order.
Lexical slots can differ when their complete captured values agree.
Binder policies agree. Bodies relate under every common reference argument.
The relation contains no execution or desired output equation.

SourceCurrentWarmConstructionParts derives each actual stage of a warm
completed call at the same heap. A prefix replays to that heap. Determinism
then identifies its intermediate heap. This proof does not assume that
four-table growth is antisymmetric or that counters are unchanged by growth.
The helpers expose ordered child calls, full row calls, node and union
requests, and both raw binder probes with their actual filters and request.

SourceCurrentNormalizedPlanCongruence.warm proves exact returned Value
equality from the pure relation, Facts at a common heap, available captures
there, and both actual calls returning to that heap. The proof follows the
first plan's finite syntax. Node calls have identical complete row sets.
Resident rows then give identical normalized requests, including dead-row
filtering. Union calls have identical ordered member results.

For a binder, the actual raw Depth returns agree. Their actual filtered
Depth values therefore agree. Both calls choose the same ordinary marker.
The raw ordinary returns and filters then agree. The two actual requests
read the same key from the same final nodeRecords table. Their selected
stored winner and finish agree. This uses the actual winner, including an
earlier cached record. It assumes no equality of reserved callback bodies.

The completed theorem replays two actual executions after both histories
grow into a common heap. It requires captures to be available at that heap.
Grows alone does not supply issued-reference extension. The initial theorem
constructs both executions in sequence from initial Ready and available
captures. It derives readiness, growth, and issued history from each call.
Both return one identical Value, with separate intermediate and final heaps.
No future successful call or result equality is supplied by the caller.

SourceCurrentNormalizedPlanEmbedding includes the earlier ordered plan
relation as a special case. The embedding is pure and includes nested Mu.

## Stored reconstruction adapter

SourceCurrentStoredNormalizedPlans defines the corresponding pure relation
on stored values and replacement environments. Closed captures agree
literally. Open nodes permit nested row occurrence matching. Open union
members and children remain ordered. Each open Mu maps its original own
name to the same arbitrary replacement Value on both sides.

The encoding theorems derive related syntax plans in independently covered
capture layouts. The complete theorem constructs both actual stored
substitutions in sequence with one exact result and both Keeps histories.
Its inputs are initial Ready, available roots, available replacement values,
and the pure structural relation. Closed roots are included. The theorem
has no open-root restriction and no promised future result law.

The nested plan integration derives its own source-built Ready heap. It
uses different capture slots, a captured Depth alias, full false guards,
dead rows, duplicate rows, and reordered rows below a used raw binder.
Both actual calls return the same open Value and replay at their final heap.
The stored integration independently builds distinct open roots with a Mu
whose stored body has three rows on one side and two on the other. Its pure
relation holds for every common binder replacement Value. Both repaired
substitutions return one exact value. The warm-parts integrations separately
construct allocating nested binders and expose exact node, union, row,
and child calls.

## Boundaries and next producer

The relation handles node-row normalization. It does not equate every pair
of syntax plans with the same language. It does not discard an unmatched
dead row, equate Empty syntax with an empty node, change a binder policy,
or reorder mixed-union alternatives. Closed captures remain exact.

Separate cold runs can assign different canonical edge identities to the
same source rows. A finite boundary uses two reversed nullary rows. Both
cold outputs have the same numeric node identity but different complete
row payloads. The sequential initial theorem uses one actual cache history.
Do not replace it with independent cold full-outcome equality.

A checked actual source refutes general physical commutation of union
normalization and stored substitution. Let A and B be distinct ordinary
leaf nodes, and let x and z be available bare references. Start with the
ordered members `[union[A, rawMu(y.x)], z]`. The raw inner Mu does not use y.
Replace x by B. Normalizing the original members first flattens the union.
Stored reconstruction then returns `union[A, B, z]`. Reconstructing the
original inner member first merges A and B into an ordinary node AB.
The later outer union returns `union[AB, z]`.

The fixture derives its initial Ready heap and available values from actual
source construction with available open captures. It proves both exact
sequential execution outcomes, all Keeps histories, final availability,
and different complete Values. It separately proves equal open observations
at every finite depth in every common view. The observations retain both
full rows, their guards, ordered leaf children, and the bare reference z.
This is a failure of the stronger physical commutation statement. It is not
a Haskell behavior defect or a refutation of the specific retained-Mu
body-versus-ordinary reconstruction equality.

The general actual-writer producer remains open. Derive an adequate row and
ordered-child relation from source syntax and causal selected writers.
Use open observations or another explicit grouping relation where physical
union structure changes. Exact recursive plan congruence remains available
when the pure normalized relation is derivable. Retain fixed captures,
unused raw Mu cleanup, earlier warm winners, and bare-reference returns.
Do not retry the disproved universal physical union-fusion statement.

Then derive retained-used Mu row and ordered-child provenance and compose
it with actual native callbacks and protected edge histories on one trace.
General outer progress, nonempty live walks, full mutual completion,
repeated-pass convergence, current frontend/errors, concrete runtime
adapters, and full public Haskell correspondence remain open.

## Validation and Haskell handoff

Full pinned Audit passes 3105 jobs and 68281 dependency checks. Effective
MemoryMax and MemoryHigh are 4 GiB, with zero swap. Audit peak is 366 MiB.
All five final strict source logs are empty. Canonical builds pass.
Read restart-evidence/20261017-recursive-plan-congruence/ for exact selected
public and constructed probe counts, raw attempts, and preservation checks.

No Haskell change or new production defect is added. Root FINDINGS retains
the external repair registry first. Field-pool repair b9219b9e remains merged
and validated. The unchanged source retains the earlier strict Nix build,
798 examples plus golden, Fourmolu, and Cabal-gild checks. Earlier proofs,
counterexamples, repairs, marked drafts, optimized interned code, stashes,
and other worktrees remain preserved.
