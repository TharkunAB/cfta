# Actual Required and projection publication histories

Frozen 2026-10-19 13:22 CEST. The final source is `SourceCurrentRequiredPublicationHistory.lean`, SHA 92178786551d33349633ef66dc97df3331d474030ff0dbbfb7dad354a88c82f4. Selected strict `head-direct-4` has a literal empty log. Canonical `head-canonical-1` completes 1020 jobs and replays only the unchanged ClosedCompletion unused-input warning. `head-public-1` passes the hardened full11/all8/std3 check. Its log contains 170370 bytes.

## Contract

The 11 public theorem heads are `unfold`, `read`, `head`, `readAll`, `union`, `project`, `projectRows`, `forest`, `required`, `children`, and `rows`.

`unfold value before ready available` returns `Nonempty (NativeMuPublication.History before (unfold value before).state)` for the actual outcome. Each graph endpoint takes `actual semantic costs available` and returns `Nonempty (History before after)`. Values use `Available`, lists use `Values`, and row lists use `Edges`. No closedness premise is needed. No initial empty-table History is required. A caller can compose this exact interval with an earlier history.

## Proof

A stored Mu unfolds by the repaired encoded source body executor. The proof derives its actual source Context from Ready, body availability, and the local replacement that maps the exact self name to the complete Mu. Full source `build_history` supplies the publication history, including pending outcomes. Other stored values return the same state.

The private cold worklist induction follows exact fuel and seen identities. Unvisited Mu values use the actual unfold and its source history. Existing open unfolding effects supply semantic heaps, cost heaps, and the exact available next worklist. Seen Mu/union branches retain the original skipped schedules. Prepend and canonical row ordering retain the same state.

The public read theorem uses the literal successful read equation. Head and source Union compose this read history with the literal final makeNode effect. That effect adds no Mu. Projection induction follows exact selected children and skipped missing slots. Required induction follows selected and unselected children, rejected rows, actual edge rebuilds, Head exposure, and final node rebuilds. Existing actual effects supply each next phase's physical inputs. A True annotation is used only to project old physical effects without adding a user annotation premise.

Every `.retain` segment is justified by its literal constructor effect. The proof never converts arbitrary Grows or Keeps into publication history. It never identifies the numeric AllocatedUnfoldHistory with this source publication history.

## Evidence and limits

There are 6 actual capped Lean runs: strict1, strict2, strict3, strict4, canonical1, and full-public1. Every run records 4 GiB MemoryMax/MemoryHigh, zero swap, and a 5-minute timeout with pinned Lean 4.34.1. Strict1 failed at one unresolved constructor type annotation. Strict2 failed at the corrected Union constructor binder count. Strict3 was clean. Strict4 removes an unused private effects helper and is the final selected source. These attempts are preserved. No resource failure is claimed.

This component owns 11 public pairs, zero constructed pairs, and zero auxiliary pairs. The separate arity fixture constructs a real nested-used-Mu cold reader; it is excluded from this manifest. No new tests or independent Lean review runs are counted.

This foundation supplies actual forward publication chronology. It does not prove all-depth guarded row comparison, selected older-body/current-callback alignment, original binding ancestry, a source renewal bound, general traversal completion, or Haskell correspondence. It does not infer an earlier history from a later history.
