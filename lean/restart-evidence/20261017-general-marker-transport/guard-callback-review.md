# Independent callback-certificate review

Reviewed on 2026-10-17 at 03:49 CEST. No material defect found.

The reviewed `SourceCurrentConstrainedCapCallbackCertificates.lean` has 132 lines. Its SHA-256 is `8f502251477358dbd7ad47235b3503bac3be182c7b74ba5dd47aa7e0fb7c1d15`. The four public declarations are `verified`, `semantic`, `checked`, and `candidate_of_actual`.

`verified` proves physical facts, growth, history retention, and availability of each actual returned value. `semantic` retains the semantic heap at the exact stopping state. Both apply to the literal callback, including a pending outcome. Neither assumes complete-cache readiness.

`checked` has no successful-execution premise. It derives causal `MuStored` at the exact stopping state. Each actual successful return satisfies the input cap at the same depth, the marked free/deep classifier, and local self-reference normality. Its pending branch proves store retention and has no successful result obligation. Its successful branch derives the raw cap and classifier, then applies the actual root filter at the same intermediate heap. The proof does not assume the desired output cap, classifier, or callback completion.

`candidate_of_actual` consumes the real normalized callback equation. It returns cap and classifier laws for `finish true (.mu entry value probe ordinary)`, plus the causal store, semantic heap, physical facts, available normalized body, growth, and issued-history extension at the exact callback return. The positive maximal marker and local normality remove the candidate wrapper or reduce the bare self-cycle to empty. Arbitrary probe arguments are safe here because cleanup removes the wrapper. This theorem does not certify the probes or install a cache payload.

The `Covered pending` input permits missing node payloads only at the listed keys. All edge payloads must exist. The returned `Covered pending after` keeps that same permission list on successful callback return. It does not assert that a listed key remains missing, that a particular owner cell is unchanged, or that all keys are complete. In particular, it does not imply `Ready after`, which also requires `Covered []` and open-depth readback. The theorem makes no coverage claim for an unfinished callback; the unconditional physical, semantic, and causal-store results remain available at that stopping state.

The candidate is not the actual first-writer winner. The literal `InternedNestedConstruction.request` rereads the current table and payload. A hit returns its existing payload. A miss runs the callback and then applies `keepFirst` to the actual returned records. An earlier completed payload can therefore win over this candidate. The reviewed module has no key-readback or winner-equality premise and does not claim a law for that winner. Actual winner cap readback or a causal winner certificate remains a separate obligation. The existing warm occurrence result does not by itself provide the missing guard-cap law.

The strict source log is empty. The canonical build passed 1094 jobs and replayed only the historical `InternedFreshOrdinaryClosedCompletion.lean:24:5` warning. `guard-callback-public-1.log` passed four imported full-signature and axiom pairs. It contains no warning, error, truncation, or `sorryAx`. Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms occur. This review added no integration tests because the actual substitution and normalized callback kernels already cover those operations.

This is local actual preservation during an outer reservation. It is not general native completion, whole-cache readiness, or a proof that every stored winner has the candidate's cap.
