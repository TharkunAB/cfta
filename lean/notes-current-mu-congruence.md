# Stored alpha relations and actual node congruence

Proof commit is `df79f802`. Source main is `c0cc8a05`, merged locally at `896b0a1c`.
Read notes-proof-status-20261017.md for the whole-library target and gaps.
This checkpoint supplies construction rules for retained-Mu correspondence.
It does not derive the general relation from arbitrary Mu writer histories.

## Pure lexical relation

SourceCurrentStoredAlphaPlans compares two different stored values.
Alpha keeps a closed capture literally equal. For open references, it
compares their resolved replacement values. Open nodes retain full symbols,
full guards, row order, and child order. Open unions retain member order.
An open Mu binds each side's original own name to the same argument value.
That argument is universal. No execution equation defines Alpha.

The relation gives equivalent encoded plans in independently covered leaf
contexts. Their complete repaired execution outcomes agree at any common
heap. This includes nested binder effects and pending outcomes. Source
coherence and availability justify each original capture lookup. The current
execution heap needs no validity, completion, or desired result-law premise
for this exact equality.

The constructed example builds a used outer Mu with a used inner Mu and an
exact closed leaf capture. Its stored body and ordinary probe are physically
different. The proof establishes Alpha for every replacement value and then
derives exact execution equality at every common current heap.

## Reordered actual node rows

SourceCurrentRowPlanReplay follows each literal row's ordered child build
and exact edge request. A completed row-list execution supplies every
original row's full replay at one common later heap. The input is one
actual completed row-list call, its initial validity, and real later growth.
The caller supplies no future per-row completion. Arbitrary nested binder
children are included.

SourceCurrentNodePlanCongruence pairs row plans by occurrence in both
directions. Row order and duplicate count can differ. Each paired row has
the same symbol, complete guard, and equivalent ordered child plans.
Actual row replays yield the same complete physical row sets. The node
constructor then has the same normalized request. Physical empty-child
filtering is included because the paired complete rows are equal.

The initial theorem constructs both node calls in sequence from Ready and
available captured values. Both return one identical canonical value. It
retains readiness, table growth, issued-reference extension, and available
output. The caller supplies neither a successful call nor a final equality.
The integration includes nested Mu, different capture slots, reordered rows,
duplicate rows, and a dead row. Exactly two live rows remain.

SourceCurrentStoredAlphaNodeReconstruction connects these results to stored
substitution. RowsAlpha matches original row occurrences with exact fields
and ordered Alpha-related children. Its encode_rows theorem derives the
required encoded row-plan relation. Initial Ready, two available open node
roots, available replacement environments, and RowsAlpha construct both
actual repaired substitutions with the same returned value and both heaps.
No future result relation is an input.

This result permits arbitrary nested Mu children when their pure lexical
Alpha relation is established. It does not generate that relation from an
arbitrary selected writer. Alpha inside children still keeps row and union
member order. The new node adapter permits row permutations at its exposed
row list. Do not generalize it to all nested row permutations or arbitrary
mixed-union permutation. The physical union model keeps alternative order.

## Open observations and necessary boundaries

SourceCurrentOpenObservationConstructors composes exact common-view seed,
node, and union observations. Matching ordinary rows keep full symbols and
guards and relate children in order. Actual union normalization retains
both complete row origins and bare-reference origins. Actual node
normalization requires matched surviving input rows.

This survival premise is necessary. A checked actual ordinary leaf and
Empty have the same depth-zero reference observations. Placing them under
the same parent row yields different depth-one observations: one child
causes the row to be removed. Same alone does not justify physical
empty-child agreement. The constructor theorem does not assume it silently.

Four additional finite kernels prove full reconstruction value equality
through union self filtering, duplicate and dead rows, nested used Mu,
raw unused inner Mu, empty replacements, and captured-name aliases.
One source is `mu x. (x | mu y. (y | x))` with both binders raw.
Its outer local is marked used, but reconstruction returns a bare self
reference after inner cleanup. Used-local evidence does not imply an
ordinary-row result. General provenance must retain reference and epsilon
cases. These examples do not prove universal reconstruction fusion.

Two buffered executable explorations did not finish. The first reached its
five-minute cap. The second was stopped as redundant after the focused
kernel cases passed. Both raw attempts are retained and excluded from the
selected success evidence. Evaluation cost is not a semantic counterexample.

## Next producer and full scope

Derive the normalized lexical reconstruction relation from actual source
syntax and causal selected Mu writers. It must handle normalization at
every nested row list, root union filtering and merging, raw unused Mu
cleanup, arbitrary live fixed captures, and earlier warm winners. Preserve
exact closed captures and full guards. Keep physical survival information
in the induction invariant. Do not replace this producer with Alpha as an
assumed desired output law.

A pure reification or plan relation avoids a promise about arbitrary future
Ready heaps. If the proof instead uses operational future heaps, their
required invariant must follow from actual execution. Four-table Grows does
not imply issued-reference extension. Ordinary and reserved marker freshness
must come from actual creation. Depth can alias an outer capture. Replacement
values may also alias existing names. All Same observations use one view.

Then derive retained-used Mu recursive row and ordered-child provenance.
Compose it with native callbacks and protected edge histories on one trace.
General outer-node progress, nonempty live walks, full mutual completion,
repeated-pass convergence, frontend/error adapters, concrete runtime effects,
and complete public Haskell correspondence remain open.

## Validation and Haskell handoff

Full pinned Audit passes 3100 jobs and 68149 dependency checks. The effective
limits are 4 GiB MemoryMax, 4 GiB MemoryHigh, and zero swap. Audit peak is
364 MiB. Final strict source logs are empty. Read the evidence README and
checkpoint-validation.json for exact public and constructed probe counts.
Evidence is in restart-evidence/20261017-mu-congruence/.

All earlier proofs, repairs, counterexamples, marked drafts, source files,
and frozen evidence are retained. No Haskell change or new production defect
is added. Root FINDINGS retains the external repair registry first, including
merged and validated field-pool repair b9219b9e. Its derivation rejection
remains distinct from standalone opaque-pool holds evaluation. Unchanged
source retains the earlier strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation.
