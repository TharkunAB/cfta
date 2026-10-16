# Independent review of the current Merge profile producer

Reviewed: 2026-10-16 20:06 CEST. Verdict: no material logical defect found in the reviewed component. This review is static. This agent ran no production checks, canonical builds, or Haskell tests for this review.

## Universal candidate before the actual winner

`MergeProfileProducer.run_profile` follows the supplied mutually recursive current `Run`/`Call`. Its Call induction hypothesis has no domain premise. It takes only the initial physical and profile storage laws, semantic readiness, costs, and request availability. The local request continuation receives the physical contract and the universal profile Certificate.

The miss proof first applies the smaller actual body Run IH to the lifted physical body certificate. This derives physical effects and the body's current storage invariants. It then proves the candidate Certificate by introducing every original row, arity, and height bound. For each such profile, it applies the same smaller body Run IH to the proved fixed-profile body certificate. Height monotonicity changes the envelope from the exact input height to the supplied larger height limit. These are multiple logical applications to the same indexed graph, candidate, heap, and current memo. They do not run a second body or choose another return.

Only after that universal Certificate is established does the proof update storage and invoke `winner_certificate` with the body's current memo. The winner can be an entry inserted during the body. Physical storage identifies its complete original. The profile law comes from its own stored Certificate or the new candidate Certificate. The proof does not apply a losing candidate's profile to an earlier winner. The final physical and profile invariants refer to the same actual `remember current input candidate` table.

The hit case skips the body and retains the exact heap and memo. `hit_original` and `hit_certificate` use resident request readback and literal tagged identity coherence. An arbitrary unrelated entry cannot supply the requested Certificate.

## Fixed-profile body derivation

`MergeProfileBody` discharges the local algorithmic obligations. Its public body endpoint has no actual body completion, returned profile, recursive-result supplier, or parent-result law premise. Recursive request laws occur only inside the instruction certificate. The mutual graph induction discharges those laws from smaller actual Call graphs.

The proof retains position-aware `Language.All₂` maps. It derives child and column result lengths from the same lists, and it carries each returned physical record through later heap effects. Small rows rebuild the original full guard. Large rows process the actual columns before their Top-row constructor.

The retained-column proof handles empty, singleton, and multiple selected values. Ordinary profiles exclude the explicit recursive-boundary union branch. A retained union can have a squared row limit. The proof derives that limit from the selected count and original profiles before applying the request Certificate. `column_envelope` then embeds the squared-input envelope into the parent envelope. It does not assume the union has the original unsquared profile.

Group posts combine returned row profiles, maximum child height, and a bound by the original group length. The root uses the exact ordered group results. Its flattened row count follows those posts and the original grouping partition. Node constructor profile and height laws refer to the literal actual normalized output, including coherent cache hits.

## Conditional versus ordinary claims

`Certificate input output` is universal over profiles of the input. For Mu, explicit union, and reference inputs, that profile premise is false. The Certificate is then vacuous. The producer still returns a substantive physical contract for such available inputs, but it proves no ordinary output domain for them.

`MergeProfileFinite.finite`, `.cold`, and `.caller_finite` require an actual input `NodeShape`. This excludes those unsupported constructors throughout the input structure. Their output profiles and nonincreasing heights are therefore substantive. Full guards and nonempty equality classes remain permitted. The theorems do not require an ordinary-only whole initial heap. A warm table's initial universal profile `Stored` remains an explicit causal invariant. The cold endpoint derives both storage laws from the empty table.

## Same actual physical and caller return

`MergeProfileFinite.allocated` uses the supplied allocated call and its exact `Call.graph` erasure. The erasure retains the current constructor heap, result, and completed merge memo. The allocated call's physical receipt separately retains its actual equality-field allocation state. It does not erase to a historical uncached worker or change the actual return.

`.finite` constructs its own allocated call from initial physical facts. It then derives both stable literal worker bounds and profiles from that same call. `.cold` derives the empty storage premises and calls this constructor. Neither endpoint takes a successful worker return, completed call, returned state validity, or body certificate as an initial premise.

`.caller_finite` uses the existing constructive literal-caller finite endpoint. It reads one successful literal return from its stable bounds, derives the exact current call through `call_sound`, and applies the new producer to that call. Its physical output, saved merge table, full advanced caller, and global bundle are the same objects as the existing `Post`. There is no alignment with a different existential execution.

The initial full caller `Context` and warm profile storage remain explicit. `Post` retains the actual checked state, operation state, warm native state, fourth table, merge history, global validity, and probes. The inventory parameter is the existing fixed inventory; this result does not claim that a new output is admitted as a new root in it. The final semantic law is `Covers`: every input term is accepted by the result. It is not language equality. The logical global reads remain a constructed schedule from the existing caller receipt, not concrete host table execution.

## Source and remaining boundary

Current Haskell `Interned/Operations.hs:613` calls `memoTypeableWith`. Its body uses ordered within-bucket rows from `fromListWith (flip (<>))`, a four-row threshold, recursive child calls, and retained column unions (613–644). The profile body follows the existing canonical grouping and completed column-first model. It does not prove native HashMap iteration or GHC demand order.

`Interned/Memo.hs:93,116` delegates to `insertKeepingFirst`. `Interned/Cache.hs:149–155` reads the table, installs a candidate thunk without forcing it, and rereads the stored winner. The reviewed completed graph runs its body before recording completion. Its header explicitly excludes early lazy publication, pending ancestors, concurrent forcing, and the GHC runtime. The new profile proof does not close these adapters. No new Haskell behavior defect was found in this review.

The recursive completed Merge profile producer is now present and the finite wrappers construct returns within that model. Projection and Required profile/request components remain complete. Merge Work/selection request and reservation bounds, cumulative Target/Shared/class/outer resource bounds, later capacity, and whole-library/runtime correspondence remain open. A bounded profile is not a bound on total constructor requests or source allocations.
