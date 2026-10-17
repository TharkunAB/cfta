# Exact guard-depth observer and remaining causal readback

The frozen source is `lean/MicroCFTA/SourceCurrentConstrainedCapGuardDepth.lean`.
SHA-256: `04442c331eedefe4329f0cd30192e7fd86f76901cb431ead92a4075c97ef2a6c`.

`profile` (line 40) reads actual stored guards, ordinary children, union members, and Mu bodies. It returns `Option Nat`. A present number is the least finite constraint-depth bound. `none` means no finite bound exists. Empty values and references have depth zero. A union takes the maximum of its members. An ordinary guard outside the predicate costs one layer. A positive child depth costs one more ordinary layer. A Mu has a finite profile exactly when its body is hereditary. Probe records and cached Mu depth do not define this observer.

The observer is pure and noncomputable for an arbitrary proposition-valued guard predicate. It does not choose a minimum from cap witnesses. Its recursion reads literal source fields. It adds no runtime checking claim.

`within_iff_cap` (line 231) proves exact equivalence with the frozen `Cap` predicate. `profile_zero_iff` (line 236) identifies the existing hereditary annotation predicate. `profile_none_iff` (line 242) excludes every finite cap. `profile_minimal` (line 254) proves the least-number claim. `children_iff_caps` and `rows_iff_caps` (lines 259 and 264) retain the actual ordered child and row families. The row laws distinguish zero from positive depth. No equality-free guard restriction is added.

The literal `makeNode`, `makeEdge`, and `makeUnion` producers (lines 288, 297, and 309) derive returned profile bounds from the original profiles and actual physical cache facts. They use the existing constructor readback laws. They do not assume a desired output cap or a future constructor return. They do not publish a new Mu invariant.

Validation is strict and imported:

- Absolute-path direct attempt 6 passed with a zero-byte log. Source attempt 6 matches the frozen source.
- `canonical-components-1.log` built this exact module and passed 1096 jobs. The only replayed warning is the old unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion`.
- All 28 public declarations have full explicit signatures and axiom reports.
- Two constructive kernel pairs pass. The first builds an actual initial ordinary source with an allowed outer guard and a false inner guard. Its least cap depth is exactly two. It has no cap at depth one.
- The second builds an actual earlier raw Mu from a root union of its bare local reference and a false-guard constant. Both actual probes and the stored body have profile one. They are nonhereditary. The local is not deep. An actual smart warm request returns that stored body with the entire same heap. The raw Mu itself has no finite profile. No source execution, warm result, body cap, or future cache law is supplied to the kernel.
- Both final standalone probe sources enable all linters, explicit terms, proofs, universes, deep terms, full names, and ten million print steps. Final logs contain no warnings or `sorryAx`.

All attempts are retained. Direct attempts 1 and 2 failed on unfolding and well-founded child proofs. Attempt 3 used a misspelled toolchain path and did not invoke Lean. Attempt 4 passed the initial equivalence core. Attempt 5 exposed a missing namespace in the added constructor helpers. Attempt 6 is final. Kernel attempts 1 through 5 are retained. The second kernel attempt has a large expanded failed goal. The final kernel attempt is 6. The debug value projections used to select literal integration witnesses are copied separately. Their final witness equations are proved by kernel evaluation in the final source.

## The causal theorem still needed

The exact earlier-winner target remains open. For each actual stored Mu cell, the desired produced invariant must derive

`Within d (profile valid depthProbe) -> Within d (profile valid ordinaryProbe) -> usesLocal depthProbe ordinaryProbe = false -> Within d (profile valid body)`.

This implication is a target to prove from actual writes. It is not a premise of any new producer. At depth zero, the existing causal `MuStored` law supplies hereditary body readback. Positive depth needs more information.

A new joint source interpretation must retain the guard-depth observation together with root emptiness, literal root-reference alternatives, and binder cleanup decisions. It must relate the actual depth callback, fresh ordinary callback, and reserved interned callback. It must derive the new candidate law before keep-first publication and retain the earlier winner law on a hit. The actual three-callback semantic origin is useful causal evidence. Its historical context does not contain a historical guard-profile heap or a source-to-current growth receipt. Those facts cannot be recovered from current `SemanticHeap` alone.

Existing guarded-language and budget-language heaps cannot replace this structural observation. Guards in nonproductive branches remain part of `Cap`. The independent `guard-probe-readback-review.md` contains a source-built empty-language raw Mu that has no finite cap. It does not refute an exact-key theorem with capped probes.

This component proves an observer, exact equivalence, and primitive constructor bounds. It does not prove the universal fresh-callback reflection, causal earlier Mu body-cap producer, general mixed optional-binder preservation, selected recursive termination, or whole-library Haskell correspondence. The concrete warm kernel is evidence for one actual family. It does not narrow the general target. No Haskell defect is claimed.
