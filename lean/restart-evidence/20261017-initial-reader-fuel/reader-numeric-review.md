# Independent computed reader review

Reviewed 2026-10-17 08:55 CEST. No material issue found. This review covers the three final root modules and their imported signatures. It does not modify production.

## Initial bound and controlled completion

`InternedValueMassBinderDepth.lean:16-61` proves that the stored-plan binder depth is smaller than the complete payload mass. The measure treats closed captures as constants. The mass includes all three Mu payloads. `stored_bounded` at lines 63-70 applies the actual record bound to each stored Mu body. It derives one fixed initial degree limit without bounding numeric identities, cached depth, guards, or symbol sizes.

`SourceCurrentAllocatedReaderNumeric.lean:23-32` defines the numeric inputs and fuel. `initialControl` bounds both issued counters, causal payload mass, and the literal pending-list occurrence count times that mass. `collectFuel` uses the computable controlled-vector majorant with dimension `mass+1`. No successful fuel or final heap occurs in these definitions.

`path_control` at lines 36-59 constructs a controlled path from each actual collector successor. It obtains the next physical invariant and resource bound from `ReaderControl.Step.good/fits`. The vector decreases at each successor. Future lower coordinates can grow. They are bounded by their current control, not by the original control.

`control_complete` at lines 61-77 uses the earlier general termination theorem internally to obtain a successful witness. It extracts the exact consumed path, bounds its length and final control by the initial majorant, and reconstructs the same ordered rows and full final heap at that computed fuel. The witness fuel does not occur in the result bound. This use of qualitative termination is not an input completion premise.

`collect_complete` at lines 79-92 derives the fixed degree limit from initial `Stored mass`, and the initial control from the original counters and pending-list length. Its public premises are initial semantic/coverage/depth facts, availability and closedness of pending values, and causal stored mass. It accepts duplicate pending occurrences and arbitrary initial seen lists.

## Literal row-read order

`SourceCurrentAllocatedRowReadNumeric.lean:23-25` pays one controlled step before the majorant. `complete_bound` at lines 29-95 handles Empty, reference, and ordinary-node direct returns, plus union collection. The Mu branch performs the actual repaired unfolding first. Its numeric and physical effects are derived by the literal `mu_fresh` step.

The Mu direct-node case returns the actual unfolded node rows and middle heap. The other cases collect the ORIGINAL Mu at that same middle heap with an empty seen set. Lines 83-90 retain that original root through actual heap growth. They do not substitute the unfold result as the fallback root. The fixed original degree limit remains valid because the existing actual unfolding theorem permits only lower-degree new Mu records.

`complete` at lines 97-117 constructs the exact `SourceEqualityProjectionRead.Read` from the computed successful equation. It obtains `Keeps`, full semantic readiness, actual resident closed rows, and larger-fuel stability from that same equation. `Stored` and both absolute supply bounds refer to the same returned heap.

## Imported validation

The public source checks all 13 declarations with explicit arguments, proofs, universes, deep terms, full names, and a large print step limit. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

Three integration theorems construct their own closed source from empty state. They derive initial readiness, availability, closedness, and the computed causal mass bound from that construction.

- `nested_duplicate_collect` uses nested raw Mu and literal union syntax with pending `[input,input]`. It constructs its own actual consumed run, derives the initial-only count/resource bound, obtains exact larger-fuel replay through `Run.stable`, and proves warm replay at the first returned full heap.
- `productive_mu_read` proves by reduction that the actual source result is a raw Mu whose stored body contains a nullary productive row. The computed read returns its actual graph, physical/semantic facts, supply bounds, and exact full-state warm replay.
- `explicit_union_read` proves by reduction that the actual source result is a union containing a raw Mu. It exercises the closure fallback with the same computed read and warm-state conclusions.

The nested fixture includes a nested binder with an outer-reference body. These tests do not separately assert that a particular collector step inserts a new lower-degree Mu. That case is covered by the general `Step.good/decreases` proof; no extra concrete insertion claim is made.

Final absolute strict production logs are empty. Imported public and integration logs contain no errors, warnings, admitted axioms, or truncated signatures. Canonical logs replay one older unused-variable warning from `InternedFreshOrdinaryClosedCompletion`; the three reviewed production sources and all new standalone probes are strict-clean. Failed root direct attempts and the first failed integration attempt remain in the component manifest.

## Scope

This closes initial computable fuel and absolute mass/node/edge bounds for this actual repaired collector and row reader. The majorant can be extremely large. No executable performance estimate is claimed. Full comparison/selection initial fuel, full selected Operand resource forecasting, broader mixed reduction termination, and whole-library Haskell correspondence remain separate obligations.
