# Current Merge primitive and selection resource control

Validated 2026-10-17 09:29 CEST. The final additive production source is 86882352a5fbed05fc8cf507af060380077b2f958f1d61465fbb0aec83d8de0c. No earlier production file was edited.

## Scalar contract

`Fits q heap` reuses the empty-pending unfold-history resource invariant. It bounds both complete payload maps and both issued counters. Its pending-work field is zero. `initial` at lines37-42 derives it from causal stored mass and the original counters through `max (max N E) B`.

`primitiveGrowth width q` at line46 is `max (q+1) (inflate width q)`, where `inflate width q = max q (1+width*(1+q))`. The extra unit pays one literal identity. The other term pays the complete ordered input-list mass, including list cons units. Growth is inflationary and monotone in both input width and current scalar bound. `values_mass` and `rows_mass` derive list bounds from actual available or resident records; no callback result-mass premise is supplied.

## Actual constructor results

`edge`, `node`, and `union` at lines92-159 use the literal constructor results. Their causal store bounds include earlier keep-first winners. They do not identify the output with a losing candidate. Each theorem retains a full scalar bound at the actual returned heap, a mass bound for the exact returned value or edge, and its literal node/edge counter transfer. Edge Work changes no node supply; node and union Work change no edge supply. The other supply grows by at most one.

`ordinaryUnion` at lines162-183 applies to the literal row-copying fast path. Copying all ordinary input rows costs no more mass than the complete input value list. Mu, union, reference, and Empty input shapes contribute no rows to that function. The resource theorem therefore needs availability and length, not closedness or an ordinary-only input predicate. This is an allocation and mass statement about that exact function, not a claim that it implements general union semantics at recursive boundaries.

The source imports the separately proved generic `HeightOrderControlledMonotone` module. The earlier private dimension proof has been removed. Private helpers compare the initial history bounds and numeric reader/comparison fuel as original counter bounds increase. No desired future weight or resource equality is assumed.

## Selection and current winners

`selectionGrowth q = UnfoldHistory.heapBound q q q`. It is inflationary and monotone. `selection_replay` at lines240-258 starts from actual successful selection and initial semantic, available, closed, and scalar heap facts. The actual selection recorder supplies an unfold history. That history derives the returned heap ceiling. Monotonicity converts the original counters to the same scalar q. The actual selected values and full heap replay at `comparisonFuel q q q` and every larger fuel.

`selection_complete` at lines261-271 constructs its own successful selection from initial facts, then applies that exact-return transfer. It has no completed call, callback, desired result, or future resource bound as an input. Full Mu and explicit union values are allowed. The scalar resource law does not restrict input shapes to finite ordinary values.

`winner_bound` at lines276-281 combines the physical current memo and current scalar heap bound. An old completed entry uses its own available payload. A newly installed candidate uses its actual availability. This endpoint bounds the exact current winner, including when it is larger than the new candidate.

## Constructive imported checks

All19 public declarations pass full explicit signature and axiom checks. Two strict-clean kernels construct their own source heap and derive every required initial fact.

`work_then_selection` runs literal edge Work followed by node Work before selection. It derives the exact intermediate resident/available inputs and semantic heaps. It applies the new scalar transfers at each Work return. The selected original family includes an actual raw Mu and a real union. The actual selection increases both node and edge counters. The constructed `MemoMergeGraph.Run` retains those exact Work and selection boundaries, selected values, complete returned heap, scalar ceiling, and all larger-fuel replay. No old completed selection is a caller premise.

`published_warm_winner` publishes an actual pure-body Mu call at that returned heap, then takes the same-state warm hit. It supplies a later Empty candidate, proves that the earlier Mu entry remains the winner, and derives its mass from the current physical memo and scalar heap bound. The retained winner is strictly larger than Empty. No winner or result-mass law is supplied by the caller.

Final absolute strict direct3 log is empty. Canonical2 passes1236 jobs. The canonical log replays the older ClosedCompletion unused-variable warning. All new source and imported probes are strict-clean and use only standard Lean axioms. Failed production direct1 and kernel1 sources/logs remain preserved. Direct2 and canonical1 retain the successful historical version before the generic monotonicity import; they are not current production hashes.

## Boundary

These are local full-heap transfers for actual primitives and selection. They do not bound all recursive requests of a general Merge body, derive a whole initial Merge forecast, or establish general constrained-reduction termination. Heap scalars and majorants are mathematical constructor resources, not memory bytes or runtime estimates. Haskell lazy publication, concurrency, and runtime behavior remain outside this completed sequential graph.
