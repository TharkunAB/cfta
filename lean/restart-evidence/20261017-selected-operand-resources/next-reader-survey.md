# Next initial reader and Operand resources

The complete public contract remains open: valid inputs and initial supported resources must construct a terminating public operation with its stated result. This survey adds no production theorem. It preserves the next target in `20261017-generated-query-resources/next-initial-operand-resources.md`: an initial numeric selected Operand forecast, then Target in source order and an actual Force miss. Mixed editor and class completion, general outer descent, repeated convergence, and public frontend, solver, runtime, capacity, IO, randomness, and user-code correspondence remain separate.

## Exact present boundary

The repaired reader already terminates for available closed inputs in its semantic, coverage, and open-depth heaps. `collect_complete` returns some successful fuel; `read_closed` adds exact effects and stability. See `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:71` and `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:211`. Neither exposes a pure initial upper bound on sufficient fuel.

The new `execute_bound` and `unfold_bound` bound all actual stopping heaps from an initial causal `Stored B`. They include full Mu bodies, both probes, unions, references, and keep-first readback. Unfolding fits `Stored (ceiling B)` and node/edge increments `charge B`; a successful returned payload fits the same ceiling. See `lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:41` and `lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:61`.

`collect_bound` and `read_bound` then prove resources of the SAME supplied successful read. They need initial semantic/coverage/availability/closedness and `Stored B`, plus the explicit read fuel and its actual done equation. They do not assume a future local resource law. `read_bound` uses `massAfter (fuel+1) B`, `credit (fuel+1) B`, the row-length bound `(fuel+1)*massAfter (fuel+1) B`, and actual row residency. The extra one pays the initial Mu unfolding outside the fallback collector. See `lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:96` and `lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean:241`.

`check_bound` and `select_bound` similarly derive envelopes from initial causal stores and supplied successful fuel. Their local recursive resource callbacks are discharged in their proofs. `select_complete` constructs its own return from existing eventual completion, but its envelope still contains that existentially chosen fuel. It is not yet an initial computable forecast. See `lean/MicroCFTA/SourceMergedComparisonMass.lean:318`, `lean/MicroCFTA/SourceMergedSelectionMass.lean:111`, and `lean/MicroCFTA/SourceMergedSelectionMass.lean:131`.

## Why the original node counter does not bound reader fuel

The general measure is a fixed-dimensional descending vector. Its lowest coordinate is `workWeight pending`; coordinate `degree+1` counts unseen canonical Mu identities of that actual stored body degree. See `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:22`. Canonical identities are read from the current issued map and complete record map. Duplicate reservations do not count as separate canonical Mu records. See `lean/MicroCFTA/InternedMuDepthInventory.lean:20` and `lean/MicroCFTA/InternedMuDepthInventory.lean:95`.

An ordinary step lowers structural pending work without increasing higher counts. An unseen Mu consumes its own degree. Its actual unfolding can create arbitrarily many records at smaller degrees while leaving higher degrees nonincreasing. See `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:31` and `lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean:49`. The new-record theorem gives the exact earlier record or a strictly lower stored-plan body depth, not a global NoNewMu law. See `lean/MicroCFTA/InternedStoredPlanBinderDepthProgress.lean:261`.

Thus the original issued node count bounds only the initial counts. It does not bound all future counts or the total number of unfoldings. A fixed-radix conversion that uses that initial count as every later digit ceiling is invalid. `HeightOrder` deliberately permits unbounded lower coordinates; its well-foundedness alone supplies no numeric length estimate. See `lean/MicroCFTA/HeightOrder.lean:19`.

The older reader has a different premise. `MergedColdReaderTermination.collect_complete` uses `Prepared`, an initial remaining-identity list, and `NoNewMu`. It cannot replace the general repaired proof. See `lean/MicroCFTA/MergedColdReaderTermination.lean:72`. Do not introduce PreparedWithoutMu, noMu, or whole-forest closure to obtain a smaller completion claim.

## Smallest sound new numeric producer

First prove a controlled-descent length lemma, then instantiate it on the actual collector transitions. Use initial `Bounded before limit` with `limit = maximumDepth(nodeInventory before)+1`; `initial_bounded` already derives it from facts. The vector dimension is `limit+1`, including structural work. See `lean/MicroCFTA/InternedMuDepthInventory.lean:72`.

One control number Q can bound the current node and edge supplies, causal payload mass, pending structural work, every vector coordinate, and an elapsed logical-step counter. Initially take a conservative maximum of initial node/edge counters, B, and `pending.length*(B+1)`, with a positive spare. Availability alone does not bound duplicate pending positions; its length must occur. Prove the small structural lemmas `weight value <= Mass.value value` and `workWeight pending <= Mass.values pending`, plus `count <= state.nodes.next` from the filtered issued range.

For a Mu transition, `unfold_bound` bounds the returned payload by `ceiling B`, node/edge growth by `charge B`, and the reached causal store. Replacing one pending Mu by that result increases pending weight by at most `ceiling B`. Other collector transitions allocate nothing and lower structural work. Consequently a conservative monotone control step can be `g(Q) = Q + charge Q + ceiling Q + 1`. The final one also pays an elapsed logical step. Monotonicity of ceiling and charge is already available. See `lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:35` and `lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean:44`.

A candidate pure majorant is defined by dimension: `F(0,Q)=Q`; `F(d+1,Q)` iterates `x -> g(F(d,x))` exactly `Q+1` times from Q. This is a PROPOSED recurrence, not a proved theorem in this checkpoint. The required proof partitions a finite descending vector path into at most Q+1 blocks at its highest coordinate. Lower-dimensional descent controls each block; g pays its boundary step. The elapsed counter then bounds path length. Prove the finite-prefix lemma with explicit coordinate and control hypotheses before using this recurrence in a resource endpoint.

The collector endpoint should have this form, with all numeric functions pure and initial:

```text
collect_numeric limit before semantic covered depthHeap bounded
  seen pending available closed B stored :
  exists rows after,
    collect (collectFuel limit before.nodes.next before.edges.next B pending.length)
      before seen pending = done rows after
    and the same semantic/coverage/depth heaps and fixed degree bound
    and the same reached Stored/massAfter, node/edge credit, residency, and row-length bounds.
```

Derive exact stability for every larger fuel. Then add `nodeEdges_numeric` for the literal direct ordinary path, initial Mu unfold, and collector fallback. Use the existing successful-transfer theorem at this computed fuel. Do not bound every successful fuel: stable execution also succeeds at arbitrarily larger supplied fuel. Bound consumed steps or a sufficient/least successful fuel instead.

Existing existential completion is useful only after an independent numeric upper bound is proved. Choosing its witness, applying `read_bound`, or returning `exists fuel, done and Resources(fuel)` does not produce an initial computable forecast. A bound defined from the returned heap or the selected witness would preserve the same gap.

## Comparison, selection, and the complete next target

Comparison has an additional descent argument. `check_eventually` orders unfinished-Mu degree counts above the number of remaining issued pairs. An allocating prefix decreases unfinished degrees; an unchanged prefix adds the ancestor pair and decreases the remaining-pair allowance. These are unfinished counts, not the reader's per-read seen counts. See `lean/MicroCFTA/SourceMergedComparisonCompletion.lean:27` and `lean/MicroCFTA/InternedFreshMuUnfoldBudget.lean:48`. The pair universe also grows after allocation. A second controlled-descent theorem must include actual row/cover/child stages and their reached causal bounds. Reader numeric completion is a prerequisite, not a complete comparison fuel proof.

`comparisonBound` and `selectionBound` already account for actual reached local resources at supplied fuel. Selection performs ordered comparisons against at most an input-length recursive scan for each input, but calls later comparisons at earlier returned heaps. Initial sufficient comparison fuel must therefore cover that actual order and growing stores. No desired local callback law should be supplied to the final producer. See `lean/MicroCFTA/SourceMergedComparisonMass.lean:126` and `lean/MicroCFTA/SourceMergedSelectionMass.lean:24`.

Then derive complete memo-aware Merge Run/Call resources, including small rows, large columns, selection, ordinary unions, and actual winner rereads. The four new `SourceCurrentMemoMergeMass` laws already transport the actual winner bound from current physical and mass invariants; they do not establish recursive numeric preservation. See `lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:42` and `lean/MicroCFTA/SourceCurrentMemoMergeMass.lean:58`.

Use those results to forecast selected projection plus Merge from initial counters, B, original forest occurrence count, and signed path length. Preserve `ForestClosed`: a proper path follows only the selected original root and selected ordinary children. Unrelated open ordinary roots remain permitted. A Mu or union head still uses its actual whole-value closedness premise. See `lean/MicroCFTA/SourceEqualityProjectionPathDomain.lean:36` and `lean/MicroCFTA/SourceEqualityProjectionPathComplete.lean:84`.

Retain the full Frame and exact Operand receipt at the literal return. Target must then run head Operand, recursive tail Fold, and the checked query in that source order. Construct the first Force miss and its fixed captured record/forest/path law before storing it; a repeated hit must retain the exact whole state. The intended constructive integration still includes productive plain Mu, a finite constrained ordinary value, an unrelated open sibling, an unselected union, unequal-length admitted paths, three Operands, and first-miss/repeated-hit Force. It must supply no completed graph, future range plan, intermediate profile, or later-entry numeric condition.

These are logical payload, constructor-credit, and proof-fuel bounds. They do not account for all Haskell forcing, membership/sorting time, solver work, memory bytes, or repeated reduction convergence. The broader source gate and complete public library composition remain open.
