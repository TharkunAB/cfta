# Whole binder profile comparison design

Read-only design review on 2026-10-18. No additional Lean job belongs to this report. The unused branch was subsequently proved in SourceCurrentStoredMuUnusedProfile under the approved scope. The unified finish wrapper below remains a proposed composition until its owner checks it.

Let M = mu entry body depth ordinary. Let own = interned entry.identity and ord = uninterned(ordinaryLevel depth). Let rho assign arbitrary reference profiles.

The pure open-Mu identity in SourceCurrentStoredMuProfileReduction.open_denote uses Coherent, Available M, and M.free.isEmpty = false. It requires marker absence only from the finite profiles assigned to ORIGINAL body leaves. It proves exactly:

```text
denote M rho = erase marker (denote body (shadow own (some [marker]) rho))
```

The new general StoredProfilePlan.rebind supplies the symbolic-local recapture equality for arbitrary Abstract profiles. A concrete replacement environment cannot realize arbitrary rho without extra construction. No such realization is needed. symbolic_fresh derives marker absence from profile origins in the finite original leaves. symbolic_mapped and erase_mapped then convert the symbolic local to root erasure. Root fresh_marker chooses an uninterned name at freeBound of the finite profile names. This choice needs no physical marker availability and no freshness of a hypothetical output.

ProfileContract.Correct transfers this exact identity to the ordinary probe. open_correct needs freshness only for BODY leaf images. It does not require ordinary-leaf freshness. Correct provides Equivalent at the same arbitrary rho and local singleton; erase preserves that equivalence. The current open_denote and open_correct sources have no material issue on inspection.

All finish branches reduce as follows. Set keep = !smart OR usesLocal depth ordinary.

```text
if keep then
  if M.free.isEmpty then none
  else erase marker (denote ordinary (shadow ord (some [marker]) rho))
else
  denote ordinary (shadow ord (some []) rho)
```

The denotation of finish smart M is Equivalent to this expression under Coherent, Available M, the new parametric Correct, the existing DepthHeap.Correct, and the finite body-leaf freshness condition. Raw finish always retains Mu. Smart used finish retains Mu by NativeNormalizedComparison.retained_of_used. A retained closed Mu denotes opaque by StoredProfileFunction.closed. A retained open Mu uses open_correct. Smart unused finish uses the new smart_unused theorem and needs no marker. Bare-own cleanup belongs to the unused branch but returns Empty, not the stored body.

For two actual completed builds of the SAME binder source, use NativeBinderExecution.decompose and NativeRequestProbes.request_probes to recover exact current probes and selected stored payloads. The selected payload may come from an earlier different source body. Obtain its parametric Correct from the causal heap invariant; do not infer writer syntax identity. NativeNormalizedComparison.probes_same aligns the used flag. NativeNormalizationInputs.actual_free for the common symbolic source inputs, together with cleanup_free, aligns original closedness. The common symbolic list must preserve fixed captures and varying reference labels; denotation equivalence of arbitrary unrelated lexical values alone does not preserve these original branches.

If both returns use the unused branch, the strict source BODY comparison is needed at local profile Empty. If both retain open Mu, choose ONE marker outside the union of both finite original body-leaf image sets. The strict body comparison then relates the current ordinary-probe callbacks with their respective ordinary names mapped to that marker. Erase the common marker. If both retain closed Mu, both denotations are opaque and this subcomparison is unnecessary. This route uses strict source syntax and causal selected payload Correct; it requires no decreasing raw returned depth.

Keep the root-filter branch in that strict source comparison. Equivalent raw denotations alone do not identify the bare-own exception before filtering. Existing scoped alias tests and exact bare-source tags supply that decision. Root filtering acts on the ORIGINAL raw records, not on the final assigned profile names.

Two invalid simplifications remain explicit. A closed raw Mu with bare-self body denotes opaque, whereas erasing a marker from its body gives Empty. Thus open_denote cannot drop its open premise. Also smart unused does not always return body: bare-own cleanup returns Empty. The new theorem covers this branch. Neither warning is a newly checked counterexample to parametric Correct. General source publication correctness remains unproved.
