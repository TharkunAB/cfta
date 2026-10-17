# Independent initial comparison numeric review

Reviewed 2026-10-17 09:11 CEST. No material issue found. Final `SourceMergedComparisonNumeric.lean` hash is 84882dded44f4c8c232d58a1388351ed6fee3b19b3bb89f5162a95db06742cbb.

## Initial origin and numeric allowance

Lines25-33 define only pure numbers. The global heap ceiling is `heapBound` of the original node counter, edge counter, and stored mass. The uniform reader fuel uses that ceiling for all three numeric inputs. Comparison fuel is one plus the square of the ceiling plus uniform reader fuel. It does not inspect a future trace, chosen successful fuel, or final cache.

`read_replay` at lines38-56 applies the actual origin-to-current unfold history to recover current stored mass and both counters at that SAME original ceiling. `RowReadUniform.of_read` constructs a numeric read and identifies its full returned heap and rows with the supplied earlier graph through actual read uniqueness. The arithmetic then extends that exact read to any large enough selected fuel.

`check_replay` at lines59-125 handles the literal empty, same-reference, and visited-pair branches first. For a fresh pair, initial-history bounds and current physical facts derive both actual identities below the original ceiling. The pair belongs to the fixed finite ordered universe. Adding it to the ancestor list strictly reduces `remainingPairs`; arbitrary duplicates or other entries in that list do not invalidate this argument.

The recursive proof is an induction on the earlier successful comparison's fuel. It uses the smaller earlier fuel to justify the induction, and the remaining-pair inequality to show that the NEW fuel is sufficient. This distinction avoids assuming that the original fuel already had a numeric bound. Each path has enough pair credit, while each demanded row read retains the same uniform reader allowance.

## Exact source order and full heap replay

The first demanded narrow read occurs before the wide row search. Its actual history extends the original prefix at line123. `SourceMergedComparisonReplayStages` then replays each ordered stage at its exact earlier full heap.

- `children_replay` retains the current prefix before the first child. A successful child extends that prefix before the remaining zip. A rejected child returns its exact intermediate heap.
- `anyCover_replay` retains failed matching candidates and their effects before the next original candidate. Header mismatches retain the unchanged heap.
- `allRows_replay` records the wide read, then its cover sequence, before the next original narrow row. It transports actual remaining rows and inputs through those effects. A rejected cover ends at its exact middle heap.

The local callback replay premise is discharged inside `check_replay` by its smaller-fuel induction. The local callback recording premise comes from the completed-read `check_recorded` proof. These premises are not required by `check_complete`.

`check_complete` at lines128-159 obtains a qualitative successful witness internally, replays it at the initial computed fuel, and derives exact effects, history ceiling, explicit mass/counter resources, and all larger-fuel returns from that SAME actual comparison. The old witness fuel is absent from the public numeric bound. No future completion, resource, callback, or result law is a public input.

## Imported and constructive validation

All5 public declarations pass imported full explicit signature and axiom checks. The constructed kernel builds an ordinary root containing two actual selected values: a productive raw Mu and a real union containing that Mu. A reduction proof checks those shapes and a literal successful comparison at16. The kernel independently invokes the new initial-only `check_complete` from source-derived semantic readiness, causal stored mass, availability, and closedness. Common larger-fuel stability identifies the same Boolean and complete final heap with the literal execution.

The comparison returns false and increases the node counter. It retains the new endpoint's full `Effect`, global history ceiling, and explicit resource bound. Every larger cold fuel returns the same result and full heap. The literal warm comparison at the first returned heap performs no further heap change; stability lifts it to computed fuel plus16. That is an exact same-state warm test, not a supplied warm law.

The final captured forest also includes an unrelated open depth reference. The kernel proves that the whole forest is not closed, while both selected root domains hold. It does not run an Operand or claim a resource forecast for that forest. The unrelated sibling is a literal reference, not a newly constructed open ordinary node.

Final source direct2 is empty and canonical1224 jobs pass. The canonical log replays the older ClosedCompletion unused-variable warning. New production and imported probes are strict-clean, with only `propext`, `Classical.choice`, and `Quot.sound`. Failed root direct1 and both failed integration attempts are preserved. Integration1 used an incorrect child-projection name; integration2 left concrete list membership goals after reduction. Final integration3 proves those memberships and contains no admitted proof.

## Boundary

This endpoint supplies initial computable fuel and resource bounds for the actual general repaired comparison on closed available operands. It permits full source Mu, union, and repaired reads. The numeric majorants can be extremely large. It does not supply initial selection, Merge, Operand, whole reduction, or result-fed caller resource forecasts. It does not establish whole-library Haskell correspondence.
