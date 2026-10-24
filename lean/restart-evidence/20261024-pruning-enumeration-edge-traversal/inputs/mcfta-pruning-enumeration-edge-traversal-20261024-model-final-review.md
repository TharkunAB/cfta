# Final edge-traversal model and proof-delta review

Review cut: 2026-10-24 11:32:21 CEST. Verdict: FINAL_SOURCE_MODEL_CLEAR. Final source has256 lines/15377 bytes; its exact SHA is bound in the table below. The two retained patches reconstruct strict2→strict3→strict4 exactly. All14 accepted literal contracts remain single exact occurrences. There is no statement, definition, helper, instance, type or limit change. The earlier model review remains byte-exact and immutable.

I authored declarations, not Root's executable definitions or proof bodies. I previously read the complete246-line first body and the complete251-line strict2 delta. I now read both complete new patches and correlate their exact resulting source snapshots, current selected source and installed source. This is an independent body/model delta review, not a new independent review of my own declarations. Guard separately reviewed those declarations before the Root body gate.

The first new patch replaces the unconstrained existential action placeholder with its ACTUAL prefixAction-bind expression. It runs the SAME captured prefix once, passes its packet.2.1 to runStaged, and branches on the actual child result. None returns pure None. Some records packet.2.2 against the actual `.node packet.1 fragments`, then returns that same fragment. It is definitionally the existing prepare action, with its local fragment let expanded. It does not rerun prefix preparation, select a different action, add a getValue/native operation, introduce a proof let or supply a desired-success law. Existing packet/result/fragments/Unit continuation types are the same reviewed types. The final-state existential is still determined by the existing exact record-update equality; no final-state premise was added.

The second new patch removes only a redundant rfl after simp already closes prepared-action equality. It changes no operation or proof premise. Both patches are proof-body-only. There are still four heads, six local haves, one proof let inputs, one definition-local fragment let, one proper-tail induction, one structural worker and the single named local List Monad. No LawfulMonad/global instance, private helper, new predicate/carrier, classical command, admitted proof or proof-limit override appears. The final256 lines fit hard260.

The prior model verdict therefore remains valid at this final identity: actual left-to-right child effects precede later unsupported entries; full-run and take-stop observations share the SAME actual endpoint; counter grows only by completed children; ordinary-parent Ready/Available/closed/edge membership derives genuine child facts; no parent residual is recorded on None; Some records only the complete residual and same returned fragment. Final alignment and all-slot realization use actual values/counter retention, not a false full Frame claim. Raw reject/Except priority, outer projection absence and inner unsupported remain distinct.

Observed compiler evidence is read-only receipt correlation, not a run by this reviewer. strict1/strict2 remain actual failures as recorded in the earlier report. strict3 actually exited1 and its160-byte raw log says `No goals to be solved` at the removed redundant rfl. strict4 actually exited0 with a literal0-byte log under warningAsError/all linters and the same compiler/proof limits. Its source hash equals both current selected and installed source exactly. No public-readback completeness, focused-build/Audit result or future seal/push claim is made here.

Terminal merging/native intersection/changed native heap, Graph/ID/extraction/index correspondence, constructor-receipt arity transport, recursive truncation-language preservation, whole-driver correctness/termination and H6 remain separate. No source-fidelity boundary is enlarged by proof elaboration success. The full goal remains active.

I performed only bounded read/hash/JSON/diff correlation and wrote this separate immutable report. No compiler/parser/prepared or selected program/import/Git/network/board operation or repository/old-report mutation occurred.

| Exact input | Bytes | SHA-256 |
|---|---:|---|
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024-model-review.md` | 8896 | `73058a10fbb47fe5919d04c99fb239ba6d387cfc96fbb70bc305458f78794be3` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-2/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15072 | `7a37c5dc044ab3c6796b25f7d34478c7ba1eefc037402a0b95bb21410d39e2c7` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-3/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15387 | `76db666a323c22101440326fb75f381a7ba3a1bb3c9a32af2d2ba989c0285f8a` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-4/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15377 | `9a071434740188ae3b03c06b6ed0487d1d3856aaaac0a8b0d7ff4bca4c1271bc` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/explicit-action-witness.patch` | 925 | `1d6091a6c650c09ea721abf05791e4d5dc3044863b20395c3305c6ffb6c2f1d3` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/redundant-reflexivity-removal.patch` | 406 | `dfab8701eb6d38eb366a7297e6cb7e82a79ea317b56ef25d2beb234a48556c13` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-3/report.json` | 715 | `e23d3e0d960d5c05aa503170d4c0b39de3c16108141329d60481910863899542` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-3/raw.log` | 160 | `90374d018c9c6a02b48029182aab335fcdf3e0e4e6f5d34b1c5bbbb097f65f75` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-4/report.json` | 713 | `8d2cca7463aed8bac5e7ead8a2481f8b3374ea6341beaf9b3f31b39a15dfddf5` |
| `/tmp/mcfta-pruning-enumeration-edge-traversal-20261024/strict-source-4/raw.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationEdgeTraversal.lean` | 15377 | `9a071434740188ae3b03c06b6ed0487d1d3856aaaac0a8b0d7ff4bca4c1271bc` |
