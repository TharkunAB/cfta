# Scoped profile inputs

Date: 2026-10-18 19:02 CEST.

Production source: `lean/MicroCFTA/SourceCurrentScopedProfileInputs.lean`.
SHA256: `b3a65202196d541cd6d833faef290167f845a6e7674498d2fdb9c997a73cff30`.
Selected counts: eight public declaration/proof/axiom pairs, one constructed pair, no auxiliary pairs.

## Exact support contract

`Compatible` at line 27 uses `NativeNormalizationInputs.support expression inputs`. At a live fixed name it requires literal equality of the assigned profiles. At a live varying label it compares the profiles assigned to the two corresponding names. The symbolic input list contains the same fixed records and corresponding varying reference slots. There is no condition on every lexical input and no full lexical Paired premise. The profiles use the existing monomorphic `InternedRootProfile.Profile`.

`variable_input` at line 33 consumes an actual indexed lexical selection. It extracts free-name agreement for a selected fixed record or the selected varying-name profile equality. `union_member` at line 52 restricts compatibility to any original source member through exact free-name support inclusion. `node_child` at line 67 restricts it to an original child of an original live row. Its literal all-nonempty profile test is explicit. A dead source row supplies no such restriction, and the theorem makes no claim for that row.

`extend` at line 86 binds the SAME local profile at two possibly different local names. Its local alias premise ranges only over the original live support. `NativeNormalizedComparison.capture_support` identifies fixed and varying captures under the entered binder. The proof splits each live capture on whether it is the local name. It preserves the shared local profile and otherwise uses original compatibility.

`extend_depth` at line 120 derives the local-to-capture alias premise from the existing `UsedBinderAliasTransport.Aliases`. The existing Scope includes the fixed Depth anchor. This theorem permits actual Depth aliases and does not require Depth freshness.

## Actual publication endpoints

`publication_ordinary` at line 132 consumes two actual Publication receipts, one common symbolic input presentation, the same source body, and initial compatibility. Each literal completed Depth callback derives freshness of its own ordinary name on live support. The theorem then extends compatibility under the two ordinary shadows. It does not require freshness for unused captures.

`publication` at line 161 consumes one actual Publication receipt and any presentation of its captured environment. It extends any common outer assignment at the exact reserved and ordinary names. The actual Depth callback derives ordinary freshness. The actual missing-key reservation and Context at its cut derive reserved freshness. The proof uses `NativeMuPublicationCallbacks.contexts` and `NativeNormalizationFreshness.reserved`; it does not infer a new payload law from arbitrary cache contents.

The exact-value extension template is `StoredProbeCompatibility.extend`. This component does not copy its full Paired presentation. It uses profile functions directly. `StoredMuProfileContract.shadow` supplies the sparse override. `InternedFreeNameSemantics.evaluateMany_member` and `evaluateEdges_member` supply original source restrictions. All syntax forms remain arbitrary, including nested Mu. No unused/dead-row freshness, BinderFree, or finite Cap condition is added.

## Actual collision integration

The fixture copies only a private initial construction prefix from the frozen `20261018-union-source-induction/live-source-kernels.lean` into a new namespace. It derives an actual closed leaf build, Ready states, and two actual smart Mu publications. Their source body uses the local and first captured reference. The second captured reference is unused and equals the FIRST actual ordinary marker. The two profile assignments deliberately disagree at this unused name.

The checked witness invokes `publication_ordinary` across the two actual events, `extend_depth` with an independently checked live alias relation, and the actual reserved/ordinary `publication` specialization. The collision is explicit in the theorem. It is permitted because that capture is absent from live support.

The same witness constructs an actual ordinary node with two declared source rows. The second row contains Empty and the disputed capture; that row is discarded. The actual result has exactly one row. The witness invokes `union_member`, `node_child`, and `variable_input` for the surviving original child. It proves the selected corresponding profiles equal while the unused/dead-row capture profiles differ. The final public theorem has exactly the same full conjunction as its private checked proof. No opaque Claim definition hides its statement.

## Boundaries and verification

This component supplies input restrictions and binder extension. It does not prove the general binary source/profile comparison or `StoredMuProfileContract.Correct` at every publication. Profile equality does not preserve original reference alias classes by itself. Existing Aliases and scoped self tests remain separate structural premises for a later source comparison. The module does not state a language, observation, termination, or Haskell correspondence theorem.

Selected production strict attempt 3 and fixture strict attempt 2 have literal zero-byte logs. Canonical attempt 2 is warning-free and reports 598 jobs. Full public attempt 1 prints all eight declarations, proofs, and axioms. Full fixture attempt 1 prints one exact public statement/proof/axiom pair. Both groups pass the hardened checker with all eight printer settings, no omission or printer failure, and only the permitted standard axioms. Every selected execution records 4 GiB effective memory.max/high, zero swap, the 5 minute wrapper, and pinned Lean 4.34.1.

Production attempt 1 failed in one conditional rewrite. Attempt 2 proved the mathematics with two deprecated `if_pos` warnings. Canonical attempt 1 replayed those warnings. The selected source uses `ite_eq_left`. Fixture attempt 1 failed only in finite support simplification and explicit contradictions. All attempts remain unchanged.

The manifest uses an explicit allowlist. It excludes root mutable modules, baseline files, shared selections, global docs, and other live components. No older source or evidence is edited.
