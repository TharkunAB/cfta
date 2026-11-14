# Exact next semantic obligation — OPEN, not a theorem

Use ONE same accepted `SourceSynthesisCurrentConstruction.firstOrderRaw` result and the SAME `InternedFreshOrdinaryConstruction.build` initializer as `accepted_initial_identity_emitted_history`. Keep every allocation receipt, Context, ProgramSlots, ValueFields, width, eagerReserved, stable exact worker outcome and OutcomeResources clause. Keep the literal identity narrow, Unit metadata, empty templates, no stop callback, default slot order, original traversal, and fixed recursive depth. Add no original-term, model, future callback/result, trace, prefix, or removed-Holds provider to the inputs.

For each output `o` in the actual worker's `emitted` result, derive:

```text
exists finite term t and ONE assignment rho : Nat -> Term Symbol,
  rho 0 = t
  and InternedGuardedLanguage.meaning
        (SourceEqualityPCSGuard.holds formulas solver)
        ambient originalBuiltValue t
  and EnumerationCorrectness.Satisfies
        (native handles at o.caller's actual heap)
        (fun guard term => PCS holds guard term = true)
        rho o.cache.core
  and every supported path/alias/residual on o's causal branch is realized by rho
  and each true-clear event (uv, actual removed scs) on THAT branch satisfies
        forall sc in scs, Suspended.Holds rho (rho uv) sc
  and actual rootPartial readback at o's heap completes to t under rho.
```

Derive the causal-branch execution certificate from actual emitted membership. Do not take it as an input provider. It must retain the actual prefix/read/check/write receipts, alias updates and any captured-cache restoration needed to identify that output. It is per output, not a union of events from independent scan alternatives. Nondeterministic siblings may reuse fresh IDs and need different assignments.

Use the SAME original root and same complete assignment in the initial model, final model, path/alias interpretation, historical removed Holds, and readback completion. If a branch-state proof uses assignment extension at allocation, compose the extensions to one final assignment and prove agreement on each earlier allocated domain. Native heap growth must preserve each used earlier handle's meaning via actual Keeps/readback laws. No full finite term is supplied as a premise.

The immediate parked subgoal, after extracting an actual reachable true-check receipt, is EXISTENTIAL COHERENCE:

```text
For this emitted causal branch, construct rho such that
  rho satisfies the reached output's domains, aliases, fragments and residuals
  AND forall sc in the actually removed bucket,
        Suspended.Holds rho (rho selectedUv) sc.
```

Do not replace it with `forall rho, postClearModel rho -> removedHolds rho`. That stronger statement does not follow from the checked iff law. Do not assume the pre-clear state already has a model unless its model has been derived from this same emitted history.

Two possible proof routes are open:

1. Derive actual ancestry provenance plus generated-Type closure. Use it to construct one compatible finite solution and lift that same solution across each clear.
2. Derive generated-Type closure plus a decreasing measure that proves repeated true-clear unreachable for this current source. Then prove joint finite productivity for the remaining pending domains. The source-only no-other-binder theorem is not the required operational closure theorem.

Pure proper suspended cycles and least-language productivity are separate. The checked selected-clear cycle laws preserve one existing obstruction. They neither construct a model nor show the current source can reach an emitted endpoint with that obstruction. Any counterexample claim must exhibit the accepted source input, same actual native build, exact worker branch, relevant clear/merge operation, emitted partial root and an independent no-finite-model argument. It must also identify the matching Haskell operation. No such trace is supplied here.

This packet does not settle every-small-budget output safety. The prior all-budget route remains a separate prerequisite. Even a proof for one stable outcome would not settle all earlier `.stopped` partial outputs without their actual inclusion/history producer.
