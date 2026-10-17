# Next computable initial semantic-rank bound

This is a proof design. It adds no production theorem.
The current `InitialInstructionBudget.initial` constructs its own complete checked receipt and derives instruction, mass, and supply bounds from initial facts (`SourceCurrentAllocatedNativeInitialInstructionBudget.lean:71`).
Its `nodeBudget` is still mathematical: it selects `requiredFuel` through semantic `Completes` (`SourceCurrentAllocatedNativeInstructionTrace.lean:27`).
`requiredFuel` uses `Classical.choose` (`IntersectRequiredFuel.lean:43`).
The next target is a computable upper bound on that rank, independent of a completed checked receipt.

## Existing decrease and finite carrier

`IntersectTotal.call_eventual` uses the exact termination tuple
`(size roots.left + size roots.right, measure pairs localWeight call)` (`IntersectTotal.lean:274`, `:444`).
`measure` is `(unseenPairs.length, (localWeight, swapBit))` (`IntersectProgress.lean:56`).
Fresh Mu entry decreases unseen pairs; reference, union, row, and child transitions decrease local weight; canonical swap decreases the last bit (`IntersectProgress.lean:108`).
A closed-environment reset can restore the unseen-pair count.
It instead decreases the closed-root size sum (`IntersectTotal.lean:112`).
Therefore the unseen/local/swap tuple alone is insufficient for a global numeric rank.

The actual source carrier is `.empty` followed by four tags for every issued node identity (`SourceRecursiveIntersectionInputInventory.lean:19`).
It has length `1 + 4*N`, where `N = source.nodes.next`.
`inputPairs` is its full ordered Cartesian list before pair canonicalization (`IntersectStructure.lean:105`).
Take `P = (1 + 4*N)^2`.
No distinctness premise is required: the existing unseen proof permits duplicates (`IntersectProgress.lean:26`).
`OriginalInput.inventory`, body/child/member retention, and `closed_reach_inventory` provide membership (`SourceRecursiveIntersectionInputInventory.lean:43`, `:49`, `:62`, `:79`, `:112`).
`inputBounds` already joins these facts to the semantic model (`SourceRecursiveIntersectionInputExact.lean:67`).

## Proposed numeric flattening

Use a computable structural payload size `s(input) = InternedValueMass.value (payload source input)`.
`payload` is an actual tagged read with an Empty default (`SourceRecursiveIntersectionInputView.lean:31`).
A causal `InternedValueMassHeap.Stored S source` bounds all such reads by `S`, including unit-mass references/defaults (`InternedValueMassHeap.lean:17`, `:74`).
The computed `initialBound source` supplies this store (`:39`, `:54`).
Mass includes all three Mu fields and every literal list occurrence (`InternedValueMass.lean:17`).
Its strict body/child/member laws are available (`:120`, `:130`, `:137`).

Do not assert that the existing `InputView.weight` is bounded by mass.
It is `sizeOf (payload ...)` (`SourceRecursiveIntersectionInputRanks.lean:14`).
Mass omits keys, free metadata, symbols, and guards; its existing comparison is only `mass <= sizeOf` (`InternedValueMass.lean:156`).
Build an alternative mass-based `InputBounds`, rather than reverse that inequality.
The required local weight is `localSize s`, which is zero at Mu, one at references, and `s` elsewhere (`IntersectStructure.lean:114`, `:130`).
Physical readback and the existing closed-reach-to-payload bridge must supply its structural fields (`SourceRecursiveIntersectionInputBounds.lean:46`, `:66`).

For the same source, let `W = 2*S + 1`.
For each ready call use:

- `r = s roots.left + s roots.right <= 2*S`;
- `u = unseenPairs.length <= P`;
- `w = localSize sum` for a node, or `edgeWeight localSize` for an edge, with `w <= W`;
- `b = swapBit <= 1` (zero for an edge).

Define `flat = ((r*(P+1) + u)*(W+1) + w)*2 + b`.
Every local transition strictly decreases `flat` by the existing lexicographic decrease and these bounded lower components.
Every reset decreases `r` and can restore all lower components without increasing `flat`.
The uniform bound is `K(N,S) = 2*(2*S+1)*(P+1)*(W+1)`, with `flat < K`.
A quantitative version of `call_eventual` should prove stable success at `flat+1`, hence at `K`.
`requiredFuel_le` then gives the desired semantic-rank bound (`IntersectRequiredFuel.lean:52`).
This uses recursive depth, not a sum of completed traversal lengths.
The existing semantic walk takes a maximum of child sufficient fuels (`IntersectTotal.lean:241`).
The separate instruction recurrence pays the full branching expansion.

**Preferred first theorem:** `mass_inputBounds`, with the exact existing `InputExact.inputBounds` arguments and result type, but size `s` and local weight `localSize s`.
Next prove `call_rank_sufficient` for ready semantic calls with finite size/carrier bounds.
Then export `initial_requiredFuel_le` from initial Facts, original/available closed operands, and computed `S`.
None of these proposed theorems is proved in this checkpoint.

## Result-fed numeric forecast

To reuse the exact current `sourceBranching` definition, prove from `Stored S` and source counters `N,E` that
`rows <= N*S`, `members <= N*S`, and `arity <= E*S` for its issued-payload sums (`SourceRecursiveIntersectionSourceProfile.lean:32`, `:36`, `:45`).
Then use `L(N,E,S) = max 1 (max ((N*S)^2) (max (N*S) (E*S)))`.
A fully numeric query forecast is `T = InstructionProfile.budget L (K N S)`.
Parameter/rank monotonicity is already proved (`SourceRecursiveIntersectionInstructionProfile.lean:43`, `:50`, `:57`).
The new rank, mass-based InputBounds, payload-sum bounds, and their monotonicity remain unproved.

For a first query define `C = MassTrace.credit T S`, `M = MassTrace.massAfter T S`,
`N1=N+C`, `E1=E+C`, and `D1=D+T`.
These are independent of the returned value (`SourceCurrentAllocatedRecursiveMassTrace.lean:107`, `:112`).
For the next query, conservatively bound the newly recomputed `initialBound` by
`S1 = 1 + (N1+E1)*M`.
The returned `Stored M` alone does not imply `initialBound nextHeap <= M`: initialBound sums all issued payload masses.
The extra sum bound is necessary when composing the current public endpoint.
`MassMonotone.massAfter_mono` and `credit_mono` provide the resource widening (`SourceCurrentAllocatedRecursiveMassMonotone.lean:63`, `:83`).
An initial multi-query reservation can then require all forecasted entry bounds, including
`N1 < 2^bits`, `E1 <= 2^(bits+2)`, and `D1 + 2^(N1+N1^2) < 2^(bits+1)`.
Iterate the same pure forecast for a finite serial query schedule.
Do not replace this with supplied later entry counters.

## Existing exact semantics to retain

`NativeInventoryRebase.extend/rebase` computes the next source and `oldRoots ++ [left,right]` at the same actual pre-query state (`SourceCurrentAllocatedNativeInventoryRebase.lean:22`, `:48`).
`NativeAdmittedQuery.inventory_agreement` transports semantic ranks from actual record growth and issued history (`SourceCurrentAllocatedNativeAdmittedQuery.lean:22`).
`CheckedJointRebase.rebase` transports joint cache laws using captured origins, not old vacuous implications (`SourceCurrentConstrainedCapCheckedJointRebase.lean:96`).
`JointInventoryQuery.generated_complete` already constructs the actual result-fed warm query and retains its full receipt, context, stores, origins, cap, and semantic inventory (`SourceCurrentConstrainedCapCheckedJointInventoryQuery.lean:119`).
`Receipt.inventoryAt` supplies the next model state (`:55`).
`JointInventoryCold.cold_complete` constructs the first such receipt from initial data (`SourceCurrentConstrainedCapCheckedJointInventoryCold.lean:25`).
The remaining numeric work should apply the new forecast to those same receipt traces and remove renewed counter premises.
It must retain their availability, closedness, idle/scoped cache, causal guard heap, and inventory assumptions.
This does not prove termination of general selected outer reduction or whole Haskell implementation correspondence.
