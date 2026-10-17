# Full repaired construction result mass

Reviewed on 2026-10-17 at 06:33 CEST.

`InternedFreshOrdinaryResultMass` derives a bound from the original full syntax and one initial bound. The initial bound covers every stored node payload, every stored edge payload, and every captured input value. The metric includes all three Mu payloads and every list position. It excludes keys, symbols, guards, and cached metadata.

The three actual producers cover `build`, `buildMany`, and `buildEdges`. Every outcome retains the computed store bound. A successful outcome also bounds each returned payload. The list producers retain the exact original list length. These theorems do not require successful execution, physical validity, available inputs, callback certificates, future counters, or a restriction on binders and unions.

The binder case evaluates the body bound three times in source order. The proof follows the actual depth probe, ordinary probe, and fresh body callback. Filtering and smart cleanup do not increase mass. On a warm hit, the actual record comes from the initial causal store. On a miss, the fresh candidate is bounded before publication. If a smaller callback installs an earlier winner, the proof reads the bound from that callback's actual returned store. It does not transfer the losing candidate's bound to the winner. Pending paths retain their actual store without a successful result premise.

The final source has 15 public declarations. The imported probe checks every full explicit signature and its axioms. The final imported kernels have three pairs:

- `constructed_nested` constructs a nested raw Mu with a captured outer variable and a union. It derives the result bound and the full returned causal store from the literal empty heap.
- `actual_warm_replay` uses that first completed construction to derive an exact full-state replay. The second result and store bounds come from the first actual returned store.
- `pending_store` starts with a literal reserved key and empty payload maps. It derives the exact pending outcome and its retained bound.

The first kernel draft had a dependent pattern proposition that did not synthesize `Decidable`. The final draft uses a Boolean constructor test. The failed source and log remain unchanged. Production direct attempt 1 and pure attempts 1 and 2 also remain unchanged.

The final direct source log is empty. The public and integration logs have no errors, warnings, or `sorryAx`. The canonical combined build completed 1183 jobs. Its only warning is a replay from the older `InternedFreshOrdinaryClosedCompletion.lean:24` unused `inputs` binder. The new production module has no warning.

This component proves causal structural mass bounds. It does not prove a complete generated-query resource bound or general constrained reduction termination. The separate uniform numeric layer can use the public transformer equations without a future result premise. No Haskell change was required.
