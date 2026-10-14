# Deep references and source cleanup depth

Current update: 2026-10-14 11:12 CEST. The full literal-input source driver is proved in
`InternedFreshOrdinarySourceDepth`. Actual repaired ordinary-level agreement
under projected captures is proved in `InternedFreshOrdinaryLevelReplay`.
See [the current source depth note](notes-fresh-ordinary-depth.md).
General closed and literal-input source completion is now proved in
`InternedFreshOrdinaryClosedCompletion`. The remaining extension is arbitrary
fixed captured records and actual native prefix preservation.
The following design and validation record is historical.

Updated: 2026-10-13 17:25 CEST.

`InternedDepthSemantics` interprets full constructor syntax with four
observations: root reference alternatives, deep references, an opaque
alternative flag, and cached Mu depth. An ordinary edge moves all child
references below an ordinary boundary. A raw binder always adds one to
depth. A smart binder adds one when its distinct symbolic local occurs
below an ordinary or Mu boundary. Root-only self alternatives do not add
depth.

`evaluate_map` proves that arbitrary external-name maps commute with this
interpreter. The map need not be injective. `arguments_depth` proves equal
predicted body depth for any two literal callback arguments in the same
environment. This is a pure semantic theorem. It does not yet state that
all actual source executions have the predicted depth.

`InternedDeepFreeDepth` defines `deepNames` on actual complete records.
`union_filter_free` and `filter_free` identify the local references that
survive actual root self filtering. `finish_filter_depth` proves the exact
source depth equation after filtering and cleanup. A raw binder adds one.
A smart binder adds one exactly when its local occurs in `deepNames` of
the original raw body. The theorem derives the direct-self case and uses
the existing source normalization invariants. It does not assume callback
depth equality.

`InternedDeepFreeNormalization` proves `makeUnion_deep` through every
source union branch. `filter_deep` preserves every deep occurrence through
root self filtering. `deep_free` relates deep membership to the existing
free-name metadata. `InternedDeepLocalNormal.callback_local` derives the
normalized local condition for every completed repaired callback. Its
`finish_deep` and `finish_depth` give cleanup equations for that condition.

`InternedFreshOrdinaryDepthHeap` defines a recursive record invariant for
both raw and smart readback. The fresh ordinary argument detects whether
the body uses its local deeply. The ordered probe pair recovers its fixed
deep captures. `candidate` proves this invariant from all three actual
observations, equal body/Depth depths, fresh captured names, and the
independently proved free-name invariant. `hit_observation` recovers the
observations for the exact pair supplied by the current request.

`InternedFreshOrdinaryDepthRequest.request_checked` proves the hit, miss,
and pending cases. It derives ordinary-name and fresh-body capture
freshness from the actual Depth observation. The miss proof uses the
original reserved identity and actual no-overwrite readback. It takes the
separate complete free-name heap for that request and recursive callback
observation premises. Those premises remain to be discharged by source
syntax induction. No full source depth heap or general no-pending theorem
is claimed.

All six new modules in this note are frozen and compile. The remaining
source driver should quantify lexical reference names and evaluate
`names.map Value.reference`. Every closed source run has this environment
form. The driver can carry exact depth and deep-name membership, then use
the existing free/profile source proofs and the pure shape projections for
the other observations. The ordered child and edge cases need maximum
depth and live-child composition. The binder case should use the new
request theorem and `arguments_depth`. This avoids an unnecessary
arbitrary-record environment congruence layer.

The separate parent-owned `InternedDepthSemanticProjections` work links
the richer pure shape to the existing profile and free-name interpreters.
Its coherent-shape preservation and exact profile projection now compile
and are imported by the aggregate audit. Free-name membership projection
is not yet written. No full source depth correspondence is claimed.

The temporary mirror compared all completed subexpressions against this
interpretation in 25,921 repaired closed executions, including discarded
children and both existing controls. It found no discrepancy, pending
request, or resource skip. A 45-second budget ended the finite search.
This is diagnostic evidence only. The script and log are
`/tmp/mcfta-fresh-depth-semantics-search.py` and
`/tmp/mcfta-fresh-depth-semantics-search.log`.

The pure interpreter and cleanup bridge build with Lean 4.34.1 in 192 jobs.
Their focused audit checks 8,183 theorem dependencies. The request module
and its dependencies build in 256 jobs. Their focused audit checks 8,840
theorem dependencies. Both audits permit only `propext`, `Classical.choice`,
and `Quot.sound`. Logs are `/tmp/mcfta-deep-free-depth-audit.log` and
`/tmp/mcfta-fresh-depth-request-audit.log`. No checks remain running.
