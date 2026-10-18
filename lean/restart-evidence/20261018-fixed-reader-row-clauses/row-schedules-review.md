# Actual historical row schedules

Reviewed at 2026-10-18 22:04 CEST.

The production source is `lean/MicroCFTA/SourceCurrentGeneratedRowSchedules.lean`.
Its SHA256 is `f28a97ebc653d952b65686f20eb1bd529593bced46b4b67db2c02681eb3e9982`.
The sole public theorem is `node` at line 303.

## Contract

The theorem retains both historical node source builds and their Contexts.
It retains live Aliases, lexical Inputs, both replacement maps, forward Grows to one Ready reader, and availability of both raw values there.
It takes a selected physical raw row on the first side.
It takes that row's actual RowCalls at the same reader.
It also takes actual RowCalls for every physical raw row on the opposite side.
It does not take either whole raw-node stored execution.
It does not take any semantic output comparison or child Empty agreement.

The result retains both historical buildEdges calls and makeNode effects.
It recovers one common source row index and the complete RowCall receipts on both sides.
These retain the actual prefix, child call, edge allocation, suffix, source symbol, full guard, ordered values, and growth to the reader.
The selected first raw row equals the first historical output.
The second historical output is a physical raw row of the opposite value.
Both original child source lists replay at the same reader.
The result retains the actual opposite reconstructed row call.
The two reconstructed rows have equal source symbols and full guards.
Their ordered child outputs satisfy All₂ Mutual Generated at that reader.
The result does not assert uniqueness of the source index when duplicate raw rows occur.

## Proof

The private schedule helpers factor the frozen GeneratedNodeSchedules proof.
They retain the exact original row execution and child source contexts.
The selected raw row survived original raw normalization.
Its original child Empty bits agree with those of the same source row on the opposite side.
This derives opposite raw-row membership before substitution.
Only this original live source row needs child Aliases.
The proof does not require reader availability for unused lexical captures.
Available raw rows supply availability of their actual child inputs.
StoredCallsReplay gives each exact warm stored child call from the supplied RowCalls.
The public historical_pair theorem then supplies both Generated directions for each ordered child pair.
The source RowCall fields and actual RowCalls fields supply the full symbol and guard equalities.
No whole reconstructed node call is built or used.

## Fragment boundary

RowCalls contains ordered stored child calls and a warm makeEdge request.
It does not contain a makeNode request for the whole reconstructed ordinary group.
A reconstructed row may have an Empty child and be discarded by a later makeNode normalization.
The theorem therefore does not assert that either reconstructed output is a physical row of a reconstructed node.
It also does not assert an Origin, row survival parity, Directed, Same, or a language law.
The total opposite-row-call premise is explicit actual execution support at this reader.
It is not a claim that arbitrary cold rows already have warm calls.
A consumer must derive or prepare those actual row receipts.
The later causal row-fragment consumer owns the extra History-based Empty and survival proof.
This module has no History premise because it proves generator membership only.
Arbitrary nested Mu source children remain permitted.
No BinderFree, Cap, closedness, or source-root restriction is added.

## Evidence

`row-schedules-direct-1` exits 0 with an actual zero-byte strict log.
`row-schedules-canonical-1` exits 0 with a warning-free 628-job build.
`row-schedules-public-1` exits 0 with one full signature, proof, and axiom report.
The hardened checker verifies all eight required printer and linter options, standard axioms only, and no printer omissions.
Every selected Lean job uses Lean 4.34.1, four GiB max and high limits, zero swap, and a five-minute cap.
This component owns one public pair, zero constructed pairs, and zero auxiliary pairs.
There are no failed or unselected attempts.
The manifest uses an explicit allowlist.
It excludes root helper state, root peaks, mutable root selections, and other components.
