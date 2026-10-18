# Stored profile function review

Date: 2026-10-18 18:46 CEST.

The production source is `lean/MicroCFTA/SourceCurrentStoredProfileFunction.lean`, SHA256 `7d6ebb0a59f62c42dda78a527dd339961f1c60d23bde5ddde7f6e411261b4e9c`.
The selected checks contain six public declaration/proof/axiom pairs and one constructed pair. There are no auxiliary pairs.

## Claims and dependencies

`denote` at line 23 interprets the actual complete `encode (leaves value) [] value`. It maps reference leaves to arbitrary monomorphic reference profiles. It retains the profile of each other captured leaf. `empty` and `reference` give the exact base equations. `closed` at line 103 gives exact equality with the original profile when the stored free-name list is empty. The closed equation follows from the actual closed-capture branch of the encoding. It does not require resident metadata correctness.

`congr` at line 113 requires one coherent state and availability of the original value there. Agreement of two profile assignments on the value's free names gives exact denotation equality. The private mutual evaluator congruence at lines 35–90 checks every syntactically used lexical slot. In the binder case it retains the fresh symbolic local and maps each external profile through `Sum.inr`. `InternedStoredPlanFreeSupport.encode_free` supplies actual free-name support for each used reference leaf. That theorem uses coherent resident metadata and exact canonical slot lookup. The proof does not assume correct metadata for an arbitrary malformed record.

`execute` at line 133 requires initial `SourceEqualityRequiredCache.Ready`, original availability, replacement availability, and the literal successful stored call. `InternedFreshOrdinaryProfiles.build_profile` compares the complete actual build with its pure encoded profile. A leaf-by-leaf equation identifies this profile with `denote` under the resolved environment. The conclusion uses existing `InternedRootProfile.Equivalent`; it preserves opacity and reference membership. It does not promise list order or multiplicity equality for the actual result.

The main supporting definitions are `InternedStoredSubstitution.leaves` at line 24, `encode` at line 58, `InternedStoredPlanFreeSupport.encode_free` at line 19, `InternedFreshOrdinaryProfiles.build_profile` at line 33, and `InternedProfileSemantics.evaluate` with its ordered operand/edge interpreters. The actual execution bridge follows the private `actual_profile` proof in `SourceCurrentStoredMuTrackedProfile`. These are source dependencies, not new assumptions.

## Constructed integration

`profile-function-kernels.lean` copies a private initial construction prefix from the frozen tracked-erasure fixture into a new namespace. It does not call an old existential witness. Both source builds start at the empty heap. Their actual returns derive readiness and recursive target availability. Replacement availability and actual stored returns are derived locally.

The first case is an open Mu whose original body contains a nested Mu. An outer replacement exposes marker 101 in the actual result. The fixture proves that `denote` is exactly `some [101]` and the actual output is that reference. Changing the bound Mu identity assignment to an opaque profile does not change the denotation; the public support theorem derives this fact. The second case returns an opaque ordinary node and has denotation `none`. Both cases also invoke `closed` on the enclosing closed source root.

The selected fixture source uses a private checked witness and a public theorem with the exact same statement. The complete private proof is unchanged from the successful strict attempt 2. The verifier compares both the private/public statements and the original/private proof text. The selected full public proof is the exact private theorem alias. All proof dependencies remain kernel checked.

## Scope

This component defines the function needed for a future causal parametric cache invariant. It does not prove that every resident Mu stored body agrees parametrically with its ordinary probe. It does not repair the previously refuted general binder Fusion contract. It has no BinderFree, finite Cap, closed-input, or unused-local restriction on `congr` or `execute`. Actual execution remains an explicit completed-call premise. There is no termination, reader transport, finite-language, or live Haskell correspondence claim.

## Validation and retained attempts

Selected production strict attempt 2 and fixture strict attempt 3 terminate with literal zero-byte logs. Canonical attempt 1 is warning-free and reports 564 jobs. `profile-function-public-1` prints all six full public declarations and their axioms. `profile-function-kernels-public-2` prints one full constructed declaration and its axioms. Both groups pass the hardened checker with all eight settings, no omissions or printer failures, and only the permitted standard axioms. Each selected execution records memory.max and memory.high as 4294967296 and memory.swap.max as 0 under the 4 GiB/5 minute wrapper and pinned Lean 4.34.1.

Production attempt 1 failed on private recursive proof unfolding. Fixture attempt 1 failed on two local proof details. Fixture strict attempt 2 succeeded and is retained as the exact pre-alias proof. Fixture full printer attempt 1 ended with SIGTERM (-15) and partial output. Its exact termination source is not claimed. It is unselected. No failed or superseded artifact is changed.

The manifest has an explicit file list. It excludes root mutable modules, root baseline files, global selections, and other components. No older source or evidence file is edited.
