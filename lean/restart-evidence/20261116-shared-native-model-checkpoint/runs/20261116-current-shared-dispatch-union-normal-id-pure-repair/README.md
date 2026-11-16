# Actual identity-monad result normalization

Frozen: 2026-11-16 05:36 CET. Status: UNCOMPILED. Root45352 rejected the preceding132-line module. afterQuery_unionNormal reported standard axioms. The dispatcher proof retained identity-monad pure wrappers at every returned tuple. This caused the seventeen errors, including wrong fallback names after the non-done branch tactic failed. The dispatcher has no proof credit.

This new132-line module changes exactly thirteen simplifier entries from Id.run to Id.run_pure in the dispatch proof. No other raw byte changes. The pinned project toolchain is Leanv4.34.1. Its Init/Control/Id.lean:44 defines the actual identity Monad. Init/Control/Lawful/Basic.lean:268 proves Id.run_pure by rfl. This existing law reduces the actual run(pure result) together. Unfolding only run had left pure wrappers beneath the caller projections. No shadow executor, new normalization framework, or future result is introduced.

The entire afterQuery proof, shared-check helper, both complete headers2a371188, probes, and preamble are byte-exact. The original EnumGuard, nativeFuel/p/h, source-target order, queries, and returned full caller remain unchanged. Every native done, yielded, failed, constraintError, and blocked branch remains present. The only invariant premises are past UnionNormal at the relevant original checked heap. No readiness, availability, word ranges, model, or sufficient-budget premise is added. No linter or heartbeat changes.

Root alone runs strict checks and promotes Source. Original132, headers, probes, and45352 log remain immutable. Whole-worker done-domain UnionNormal and the joint finite completion remain open. No Source, compiler, Git, board, root document, tmp, or Haskell change is made.
