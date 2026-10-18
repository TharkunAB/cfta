# Tracked slot extension and Ready-cache boundary review

The review found no material issue in `SourceCurrentTrackedSlotExtension` at source SHA `03a221a6a0ad645645c6cd3ab05df5dcdb091e6264518ac33b14c3c6c08ce8c9`.

`related` rewrites both masks with exact absence from both resolved root profiles. It proves an equivalence. It needs no heap, execution, availability, or future result premise. The new marker need not be absent from the old tracked list.

`paired` applies this equivalence only to paired reference slots. The premises quantify the actual resolved values `input environment value`. Nonreference slots retain the same capture and equal maps on its free names. The proof does not infer nested marker absence from an opaque root profile.

`bind_marker` uses the existing sparse binding extension theorem. It requires each new lexical name to be absent from the original slots' free names. This premise prevents the new binding from changing an old reference resolution or an old opaque capture's relevant map. The marker's exact resolved-profile freshness and the lexical binding-name freshness serve different purposes. The theorem keeps both premises explicit. It derives no output comparison or source binder law.

The root integration uses an actual closed source-built used Mu at a Ready reader. Its first resolved reference is this Mu; its second is an untracked ordinary reference. Both have an opaque tracked observation. The same actual closed Mu also occurs as a fixed capture. Fresh local names bind one shared marker. The witness retains literal executions of both new local references. This checks the supplied slot hypotheses and the actual binding equations. It does not compare two completed binders.

## Ready-cache boundary

The immutable `binder-contract-direct-3.source.lean` derives a real `Ready` proof for a manually assembled record. The Depth and ordinary probes come from source `node7[x,y]`. The installed body comes from another source, with rows `node7[x]` and `node7[y]`. The body does not use the reserved self name.

This construction satisfies every conjunct of `Ready`. `Normal` retains coherent resident payloads, live rows, flat unions, nonempty records, and nonempty members. The profile heap checks root opacity and pure root reference sets after cleanup. The free-name heap checks decoded membership. The depth heap checks decoded depth and deep-name membership. Coverage checks stored input support. The open-depth heap checks body/probe open depth. These observations admit the two different row groupings. Duplicate free names do not change membership.

None of these summary invariants supplies a common-expression publication witness for all three callbacks. The boundary installs the mismatched body with a direct `complete false` call. That operation is not the complete same-expression binder schedule. The review therefore treats this state as a countermodel to summary-only hypotheses. It does not establish a reachable-source cache counterexample or a Haskell defect.

The later boundary witness requests the same current smart-binder expression under two renamed capture lists. One request hits the manually installed record. The other constructs its own record. Equal substitutions erase one capture and retain another. The split body retains one row, while the joint row disappears. The proof retains initial Contexts, live Aliases and self tests, paired Empty flags, actual source equations, actual reconstruction equations, forward Keeps, and final warm replay. Its strict node body law holds; the lower-rank premise at rank zero is vacuous.

The depth route has a separate limit. Smart unused cleanup can return an ordinary raw result of depth zero. The selected Mu candidate still has depth one, and its stored writer body has depth zero. Thus a rank premise strictly below the returned raw depth zero does not cover the actual writer body. Adding a causal history premise alone does not prove that missing strict inequality. An original syntax or actual publication measure needs a separate justification.

A general binder fusion statement over arbitrary Ready caches cannot use the summary invariants as a replacement for causal writer provenance. The next contract needs an actual common-expression publication/source-history invariant or another proved body/probe reconstruction invariant. A causal invariant still needs its own preservation proof. This review does not assume that such an invariant already closes general binder fusion.

No Lean build or new proof declaration was added for this review. The selected owner signatures, full proof prints, and axiom reports are reused.
