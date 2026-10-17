FINAL 2026-10-17 19:28 CEST: source frozen at
6778d4e4e166512bc22749665b2e9c3b5c4a4cf4da1e3dea364f8b14334c4958.
Strict candidate-direct-3 EMPTY, canonical1 PASS554, public1 full head clean.
See candidate-review.md, candidate-manifest.json and candidate-verify.py.
No remaining owned proof task. Guard owns causal History discharge.

# Candidate-law continuation

Updated 2026-10-17 19:26 CEST. Owner: required_memos. New production only:
`lean/MicroCFTA/SourceCurrentNativeNormalizedComparisonCandidate.lean`.
The finite, erasure, and outer components remain frozen.

Goal: `candidate event compared unused` proves
`finish true (.mu event.entry event.body event.depth event.ordinary) =
eraseSelf (.uninterned (ordinaryLevel event.depth)) event.ordinary`.
The only comparison premise is Compared of the actual smaller expression,
with fixed environment lifted from Atom Unit into Sum Unit Unit, one varying
local `.inl ()`, ordinary and reserved assignments, common event.afterBody.
No private Heap or desired candidate law is an input.

Proof plan:
1. Extract both raw builds and exact filters with PublicationCallbacks.raw_callbacks.
2. Derive both starting Contexts, DepthHeap, raw Normal and Available from actual builds.
3. Derive both raw-return issued histories into afterBody from filter_verified,
   intern_issued_extends, and the actual body callback history.
4. Obtain actual ordinary and reserved freshness against fixed captures, then
   extend_fresh_on over the singleton local list. Turn usesLocal=false into
   ordinary raw noDeep through filter_deep. Use deep_transport_on for body raw.
5. Apply compared to the literal raw calls.
6. If the local is supported, derive both bare roots and local ValueNormal.
   Apply LocalRecordErasure.same to the exact filters.
7. Otherwise obtain raw equality via live-input replay. Actual free support
   and freshness exclude each own marker. Prove the actual filter is identity
   under free absence. Erasure is identity too.
8. Derive actual body's Local from callback_local and body noDeep from
   filter_deep. Apply NormalizedErasure.finish_true_eq_erase and the erased equality.

Validation: immutable candidate-direct-N snapshots, executed at their absolute
paths with pinned Lean 4.34.1 and linter.all. Actual 4 GiB max/high, swap zero;
unique candidate-peaks.txt. Canonical own single target after strict empty.
One full public signature/proof/axiom group, no extra scenarios. Package a
candidate-manifest.json and executable candidate-verify.py after final freeze.
No old source, Audit, docs, Haskell, Git, or other owned evidence changes.
