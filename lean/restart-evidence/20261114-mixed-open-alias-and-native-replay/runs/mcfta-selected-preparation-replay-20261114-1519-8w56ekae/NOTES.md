# Successful selected-preparation replay candidate — 2026-11-14T15:21:40.374369+01:00

Status: UNCOMPILED CANDIDATE. Root owns validation and live writes. No compiler, Nix/Lake/heavy job, Git operation, live write, board request, or child task was used.

The candidate adds one standalone module with TWO proofs. It changes no operational definition or existing header. `candidate.patch` adds that module only. The public `SourcePruningEnumerationSelectedValue.run_done_moreFuel` dependency is byte-identical to the supplied private strict-PASS source after its `#print axioms` line is removed. It is also present in the current live source at SHA 5f6e5e1057f86a4151da3fc952a8e5aeb62443d12da0634bfc052564210572b4. No namespace overlay is used.

`SourcePruningEnumerationEntry.enter_success_raw_moreFuel` starts from an actual successful entry. It preserves the ENTIRE raw entry result at every larger entry bound. It uses the checked public laws `EnumerationExecution.getValue_moreFuel`, `EnumerationPartialExact.getValue_exact`, `EnumerationExecution.representative_moreFuel`, and `EnumerationPartialExact.representative_success_exact`. The first read is the representative-backed getValue operation. The second read captures the root. Both exact reached core states are retained. The following native lookup and expansion-ancestry write then receive the same complete state and data. No totality, Ready, Packet, realized-handle, future bound or resource premise is added.

`SourcePruningEnumerationSelectedPreparation.successful_run_moreFuel` has the EXACT header frozen in the earlier all-budget route. It starts from the actual successful constructor pair:

```text
([.ok ((target, handle, scs, decoded), entered)], some (.done value heap))
```

Both the entry and native bounds change from `fuel` to `fuel + extra`. The proof projects the actual pair, uses exact entry replay, and calls checked `SelectedValue.run_done_moreFuel` on the extracted native `.done` observation. The conclusion retains the complete pair, not only its native value or emitted fragment.

The actual `SelectedPreparation.run` result contains a raw Core row and native heap, rather than a separately returned caller or Cached value. Its consumers construct `SelectedValueCaller.advance caller heap` and `EnumerationExpandableIndex.frame entered before`. The exact replay therefore supplies the SAME complete advanced caller and SAME reconstructed Cached state. That cache retains the input waiting and expandable functions. It also retains the exact entered union-find forest, values, counter, obligations, per-slot recursion ancestry and expansion ancestry. The caller's Context and any existing receipt refer to those same states; the replay proof does not manufacture a Context or Post without its producer.

The only observation premise is the concrete small-bound success of the operation being replayed. No future result/resource/callback law, fake Key/fits/admits choice or alternate initializer is assumed. No readiness premise is needed for equality replay.

Checks performed without Lean: exact main-header comparison against the previous frozen producer; byte comparison of the checked native primitive; static project-import traversal (1584 modules, no cycle); added-file patch reconstruction; no sorry/admit/axiom/unsafe declarations; source-pin equality during freeze. These are preparation checks, not proof validation.

Remaining scope: this candidate does not replay raw empty entry rejection, a failed native preparation, shared child dispatch, scans or callbacks. Continuable child replay still must cover native-completed rejection and singleton success with exact caller/query/cache endpoints. The actual stopped-output inclusion/history proof at every common work bound remains OPEN. Eventual worker resources alone do not supply it. ONE finite accepted common original-root term/assignment, parked backward recompletion, and every original typing/language/LPO/stream/count/weight/rank/runtime clause remain OPEN.
