# Direct Merge body cost

Reviewed at 2026-10-17 09:32 CEST.

The frozen source is `SourceCurrentMemoMergeDirectCost.lean`.
Its SHA-256 is `b39d56e51e0ece329453808961f15fc993fe16f2f3d986edc57cd5b776693580`.

`Counted` follows the actual `SourceCurrentMemoMergeGraph.Run` instructions.
Pure, Work, select, and request each cost one direct instruction.
Bind adds the two actual costs and one sequencing instruction.
Each request retains its actual completed Call and all captured heap and memo fields.
Its nested body cost is separate.
The count is not a final-counter difference.

`of_run` constructs the ordered request list and count from the supplied completed graph.
`Counted.erase` returns the same `RequestBounds.Direct` receipt.
`Counted.graph` returns the same graph.
`map_cost` retains exact output length and ordered traversal.
It bounds map cost by the sum of local costs plus `3 * inputs.length + 1`.

`body_cost input bound mass actual` proves `cost ≤ 100 * (bound + 1)^3`.
It does not need a semantic, closure, or desired-result premise.
It covers open ordinary passthrough, Empty, references, Mu, and union passthrough.
A closed ordinary root uses the actual complete row groups.
Group count is bounded through the nonempty groups and their flatten permutation.
Each group is the actual input filter at its first key.
No identity injectivity premise is used.
Small groups use the original child-list lengths.
Large groups use the actual column count and a constant upper bound for each retained-column branch.
Mass ignores guard and key metadata.

`body_bound` additionally takes the legitimate initial SemanticReady, CostHeap, physical memo Stored, and Available facts.
It derives `Reached (height input)` for every event in this same counted receipt.
Each event retains its actual input, initial and returned heap, and initial and returned memo.
This theorem does not replace a captured old winner by a newly computed candidate.

The public checks contain 15 full signature and axiom pairs.
This total includes the inductive type and its five constructors.
The three integration checks build literal source fixtures from empty.
The two-row fixture constructs a small-group body.
The five-row fixture constructs a large-group body.
Both construct their own finite body Run and apply the bound to that same Run.
The third check constructs an actual five-child select, ordinaryUnion Work, and recursive Call.
Its direct column count is exactly five and its event list has exactly one request.
It constructs an exact warm Call from the same returned memo entry.
These checks use no caller-supplied completion or local resource bound.

The result bounds completed direct graph instructions.
Selection comparison instructions, internal constructor jobs, and nested recursive bodies are not charged here.
The module does not prove one initial bound for the complete recursive Merge worker.
It does not model pending lazy publication or concurrent Haskell forcing.
No Haskell source changed and no new Haskell defect was found.

The next quantitative producer must combine direct costs with nested request costs at the captured states.
It must retain physical memo Stored and causal first-winner resource bounds across each interposed Work job.
Direct Work width classification is not proved here.
That proof must retain map output lengths, select output subsets, grouped row counts, and ordinaryUnion row concatenation at each actual Work heap.
It must derive availability or residency there from the actual physical effects.
An unfold-only history cannot substitute for the effects of ordinary constructor jobs.
