# System claim and writer-history scope review

Read-only review. No new Lean jobs or proof pairs were added. Exact source hashes are in `target-system-claim-pins.json`.

## Strongest concise claim

The Lean model proves that a completed closed source construction represents exactly the finite trees specified by its expression. A completed root reduction from the derived logical initial state, with empty inherited constraints, preserves that exact language. This requires covered valid field allocation and the stated numeric resource bounds. General termination and correspondence with the Haskell implementation remain unproved.

This is a conditional correctness result for actual modeled executions. It is not a whole-library termination or implementation-refinement result.

## Exact theorem support

`InternedGuardedExecution.closed_language` (line 201) takes the literal `FreshOrdinary.build expression [] empty = .done value heap` equation. It proves equality with the independent guarded syntax semantics for every supplied guard interpretation and ambient environment. The syntax includes arbitrary nested raw and smart binders. No BinderFree, finite Cap, or supplied probe-language heap is required at this closed entry.

`SourceCurrentConstructedRootCall.root_call` (line 34) composes that construction result with the actual bounded root call. Its conclusion supplies final result availability and exact language equality with the original source expression. The actual empty inherited allocation makes the general NodeLaw lower bound exact. It does not assert that arbitrary inherited constraints hold on all returned trees.

The essential root-call premises are:

- A completed closed FreshOrdinary construction from the empty source heap.
- An actual original equality-field allocation history with a valid starting interner and coverage of every source guard.
- The supplied guard formulas and solver semantics.
- Initial physical Fits and a finite guard carrier containing the actual heap guards.
- Room for the complete pure outer schedule at width `bits + 2`.
- A literal successful bounded root call with the actual empty inherited value.

The theorem derives the logical caller Context, root availability, initial guard heap and Frame. It does not receive these as caller certificates. Its logical empty caller and global tables do not establish a reset or initialization of concrete Haskell global caches. Arbitrary initial warm cache correctness is not derived by this closed-start endpoint.

The general inherited contract is exactly `L(input) intersect Sat(inherited) <= L(result) <= L(input)`. It preserves every inherited-satisfying input tree and creates no input-external tree. It does not require all output trees to satisfy inheritance. The current notes state this distinction correctly.

## Main remaining gap

The largest mathematical gap is general outer completion from initial support. The successful-call premise has not been removed. Active-owner exclusion and a valid bound on fresh recursive requests after native edits remain necessary. Effective own-pair gains and causal writer histories supply local facts; they do not yet supply a finite global progress measure. Repeated-pass convergence is separate.

The largest implementation gap is refinement to Haskell: lazy demand, cache publication and lifetime, field preparation, machine integers, logical startup versus CAF state, and public adapters. The all-Generated fixed-reader simulation is an auxiliary open observation contract. It is not a premise of the intrinsic closed-language or completed root-language theorem.

## New writer-history endpoints

`SourceCurrentTargetMergeHistory` derives physical historical Writer provenance through actual successful operand, fold, target, force and shared leaf calls. It uses initial physical Good/Stored/availability and Raw. Its native stages retain the exact merge table.

`SourceCurrentLowerMergeHistory` threads this Raw invariant through actual edits, edit lists, class calls, the actual right fold and class pass. It obtains every intermediate Good and residency fact from completed earlier physical operations. It does not assume semantic Reads.

`SourceCurrentParentMergeHistory` carries Raw through actual Scan/required/class schedules, precheck branches and Parent returns. Live field/inherited/child support remains conditional on the literal noncontradictory branch. Rejected branches retain the table.

`SourceCurrentOuterMergeHistory` now derives Raw through all six successful outer phase workers, edge bodies and cold/warm edge calls. `reached` (line 326) derives it at literal unfinished phase entries from the actual prefix; no future whole-call success is required. `busy` (line 337) covers the exact node-busy diagnostic. `initial_node` (line 347) and `initial_reached` (line 358) derive initial Raw automatically from the logical empty merge table, given initial physical Good, ProbeHeap and request readiness.

These statements do not cover every internal failure state of an unfinished lower worker. They do not admit arbitrary warm tables without an initial Raw certificate. They do not assert general completion or semantic source descent.

## Required notes update

The reviewed notes say: “The whole outer caller must still derive the writer history and compose these projected sources through native edits and Mu row reconstruction.” The first part is now stale.

Suggested replacement: “Actual completed outer calls and their unfinished phase prefixes now derive the physical Merge writer history from the logical empty table and initial physical support. The remaining source-anchor proof must compose projected row sources through native edits and Mu row reconstruction.”

No other material mismatch was found in the reviewed system-claim statement. All source and evidence changes remain outside this read-only report.

Final outer source readback: SHA256 `924b86184a14f39805a274206357d0d5fddef4e6117959daca48b9ec5a98f430`. The only change from the reviewed direct2 snapshot moves private `empty_raw` before the `DecidableEq Node` section variable. The public statements and proofs are unchanged. This removes an unused private instance parameter. No Lean job was added by this review.

The final central note now points to `notes-current-writer-history.md` and states the corrected successful-call, unfinished-phase-prefix, initial-support, warm-history and lower-failure boundaries; this wording matches the reviewed theorem scope.
