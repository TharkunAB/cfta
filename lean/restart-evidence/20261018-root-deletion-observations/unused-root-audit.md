# Actual unused binder deletion audit

Reviewed on 2026-10-18 at 20:09 CEST. No material issue was found in `SourceCurrentNativeUnusedRootDeletion.build`. This is a read-only source review. No Lean run or production edit was made. No new public or constructed pair is counted.

The reviewed production source is SHA-256 `d79eb619b6ccbffbfbceda7662f715ec0269fb862fcc8f1f02ae5837fbe1c648`.

## Exact causal route

The theorem takes a joint initial `Context`, an actual `History empty before`, and the literal successful smart-binder call. The unused decision remains an implication on the actual returned probes. It is not inferred for every binder.

At lines 42–45, `NativeBinderExecution.decompose` derives the current Depth and ordinary callbacks, the exact raw ordinary source call and filter, the return contexts, and physical plus issued growth from the raw return to the whole return. These are actual calls of the current request. They remain actual on a warm cache hit: source construction executes both probes before it performs Mu lookup. The theorem does not claim that a warm hit executes a new reserved-body callback.

At lines 46–49, `NativeRequestWinner.winner` obtains the exact selected final cell. `InternedProfileHeap.stored_probes` identifies its depth and ordinary components with the current physical probes. This keeps the protected old winner; it does not replace that winner's body with the current source body's result.

At lines 50–51, actual `build_history` is appended to the supplied initial empty-table history. This derives `History empty after` in the forward direction. At lines 59–60, `history_unused` uses the exact selected cell in this derived return history. Its result is the literal equation between the returned cleanup and bare-self erasure of the current ordinary probe. No backward history inference or supplied final history is used.

At lines 61–65, `StoredRootDeletionErasure.erased_filter` is instantiated at the actual raw ordinary heap. Its normality and raw availability come from the actual source context and verified build. Rewriting the actual filter and exact unused return gives deletion of the raw strict-body result with the original cuts extended by the current ordinary name. This is the algebraic helper identified in `arity-causal-route-review.md`.

Neither the statement nor this derivation assumes `StoredMuProfileContract.Correct`, `StoredMuRootContract.Correct`, or a heap of either predicate. `history_unused` uses its older, independently established causal unused-readback law. It is not the pending parametric payload producer. No new `Ready` premise, whole lexical reader availability, source restriction, or desired output equation is introduced.

The theorem returns exact raw-return growth and issued extension. It does not prove a full two-run source comparison or the retained-Mu case. It also does not show that every smart binder is unused.

## Next smallest source proof step

First add the actual common-reader form of this reduction. The proposed source law in the frozen route review supplies `History empty reader` and `Grows after reader`; it does not supply `History empty before`. The reviewed `build` therefore cannot be applied directly inside that law by inferring an earlier history. Keep its initial-prefix endpoint, but derive a separate form from the same actual decomposition: send the exact selected cell to `reader` with `growth.nodeRecords`, then apply `history_unused` at that reader. The erasure proof still runs at the actual raw ordinary heap. No readiness of the reader or intermediate history is needed.

Then prove the two-sided smart-unused constructor clause from only the strict current-body induction hypothesis. The common-reader reduction supplies the two actual raw body calls and their combined cut predicates. It removes the need to compare or recurse on an earlier selected writer's syntax.

There is one concrete assignment step before applying that strict-body IH. The two actual ordinary names can differ. First derive that each finished value has no free occurrence of its own ordinary name. `NativeCallbackErasure.callback_result` derives this for the erased current callback from its actual context, callback, and unused decision. Exact `history_unused` identifies that erased value with the whole return. Therefore `StoredRootDeletion.congr` permits a common local profile shadow on the finished value.

Apply the reviewed `build` reduction with that shadowed assignment. The useful one-call form is:

```text
Equivalent (deleted cuts value rho)
  (deleted (fun name => cuts name || (name == ordinaryName)) raw
    (shadow ordinaryName commonLocal rho))
```

`commonLocal` can be Empty. It is chosen equally on the two sides. The strict-body IH then compares the actual raw calls under these shadowed assignments and extended cuts. Actual ordinary freshness on live source support supplies the local alias condition. The profile extension is already in `ScopedProfileInputs`; the matching Boolean cut extension still needs proof. Keep the original live aliases and cut compatibility explicit. Unused captures and dead rows need no freshness requirement.

This two-sided constructor clause is a substantive next source step. The retained branch still needs the old payload contract, actual closed/open status, and a common fresh marker for the two ordinary-probe profile reductions. The frozen causal heap adapter supplies the forward prefix needed by the separate chronological old-contract producer. It does not prove that producer's candidate law.

## Source pins

| Source in `lean/MicroCFTA/` | SHA-256 |
| --- | --- |
| `SourceCurrentNativeUnusedRootDeletion.lean` | `d79eb619b6ccbffbfbceda7662f715ec0269fb862fcc8f1f02ae5837fbe1c648` |
| `SourceCurrentStoredRootDeletionErasure.lean` | `17ad9906ada92e1b02cc640f2e4302dd7288bdd38a191980c79fe8db575f97c2` |
| `SourceCurrentNativeBinderExecution.lean` | `52800a69fd008c7eaa8c4ccaeaf5b1534792dfbe741b3958e3789fe3a447f3e7` |
| `SourceCurrentNativeRequestWinner.lean` | `2e6d9e5e5bb68ed86501e9f995c97befb878eef12f1dc04ec740bd6d3debdac6` |
| `InternedProfileHeap.lean` | `db598f138438f97540bfb2113e7d898acb945877b740bd1773fe7dd548d0ef88` |
| `SourceCurrentNativeNormalizedComparisonExecution.lean` | `9d2f9e64c62396b76e32c76428369188fc09371c1b19e100f8c0ca79b80e1a00` |
| `SourceCurrentNativeCallbackErasure.lean` | `33a654079ed23f616c2935b5942d9f789d1b31f2bfaeaecc7ee78a9cdd6c8b60` |

The linked frozen route review has SHA-256 `b7270463f2d62b29df7ce531a5104845435d127887a7113a33ee354f24ae0804`. The frozen `SourceCurrentCausalPublicationHeapInduction.lean` has SHA-256 `038c9e9b5b2e7b47c45bf578a5ec2f7e8aa98285a999a893e81fe6e99bfdfe4b`. Neither frozen component was changed.
