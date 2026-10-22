# Singleton prepend, final reversal and finite iterator transport

Updated: 2026-10-22 23:33 CEST. Proof checkpoint: `44fcfd7d89241c0e22c13f37ac7d34ce0b272b13`. Start: `d0cf685f461430a7c608ceb3b76da0fe568e4d84`.

The selected reviewed declarations in SourceCurrentPrependGrouping provide
pure bucket and iterator laws for a generic key and item type.
Singleton insertion prepends new rows to the old optional bucket.
Reversing every final bucket gives the existing ordered append-fold table.
None and Some remain distinct. Every matching input occurrence remains.
Finite iterator transport preserves exact lookup and unique emitted keys.
The result permits an arbitrary outer order with exact within-bucket order.
No HashMap implementation or Haskell state/evaluation refinement is claimed.
No native request, group execution, new Room, reset or wider caller is added.

H20's checked one-symbol-group completion and physical union iff remain unchanged.
A later actual all-symbol traversal must retain its evolving packet and global history.
That traversal is not proved here. Generated parents, public Mu/full pass,
practical width, solver contracts, Haskell refinement and convergence remain open.
H6 constructed_node_calls remains the strongest combined theorem. The whole goal is incomplete.

Selected source: 89 lines, SHA `3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba`.
Selected clean strict: `prepend-grouping-strict-3`. Selected FULL: `prepend-grouping-public-1`.
Strict has a literal-empty log. Default declaration limits and all linters remain.
The source has a hard240-line limit. Diagnostics follow the complete module.
FULL retains 133490 raw bytes. Complete check/print TYPEs agree after ASCII whitespace normalization.
insertWith TYPE: 4 logical lines, 3 LF, 204 bytes, 196 characters.
insertWith raw checked SHA `48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be`; printed 204 bytes, SHA `48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be`.
insertWith raw byte identity: True; lexical identity: True; canonical SHA `2070c90b3a20e08bc6ee18540c8a6c382e22c8cac3dc784571aea6339a6e2029`.
insertWith actual axioms: none.
fromRows TYPE: 2 logical lines, 1 LF, 139 bytes, 129 characters.
fromRows raw checked SHA `094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28`; printed 139 bytes, SHA `094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28`.
fromRows raw byte identity: True; lexical identity: True; canonical SHA `2de1facfaf02162c1673ff85572a91a23c07ff45ee0bd2e852e5bb9749e0df0b`.
fromRows actual axioms: none.
reverseTable TYPE: 2 logical lines, 1 LF, 132 bytes, 128 characters.
reverseTable raw checked SHA `1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528`; printed 132 bytes, SHA `1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528`.
reverseTable raw byte identity: True; lexical identity: True; canonical SHA `3ca033ceb30ce55d6e40174e64c6cfa2b7a678145592b624c9a49b75b53b551a`.
reverseTable actual axioms: none.
pair_fold TYPE: 8 logical lines, 7 LF, 653 bytes, 649 characters.
pair_fold raw checked SHA `9dc4d1e79df4da3e0ead7a744b916ab00c8352344aa090cbfe469a9a4988d800`; printed 653 bytes, SHA `80591714a25308241133eda0250a552e996f6531f7cbfa031bdf5338640d1061`.
pair_fold raw byte identity: False; lexical identity: True; canonical SHA `c94234bcbd7ae0ee1d53048469a3f8ef616122f57b5cb21f7b80fb97698fe824`.
pair_fold actual axioms: propext.
reverse_insert_singleton TYPE: 9 logical lines, 8 LF, 698 bytes, 696 characters.
reverse_insert_singleton raw checked SHA `fd13a4e124d61c37b4c120aab3211187fbe18ab2f5c8a3a355340969daf69f05`; printed 700 bytes, SHA `2647b3b5bfd2290c719ba98df5e8537b7afeaf8756b68064ddd23336c092b2bb`.
reverse_insert_singleton raw byte identity: False; lexical identity: True; canonical SHA `a88381f5ad81acb49e545d34b770ee94b75b4433699d1511a87978265a58eff1`.
reverse_insert_singleton actual axioms: Quot.sound, propext.
reverse_fold TYPE: 14 logical lines, 13 LF, 984 bytes, 980 characters.
reverse_fold raw checked SHA `e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3`; printed 984 bytes, SHA `e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3`.
reverse_fold raw byte identity: True; lexical identity: True; canonical SHA `4026de9a15f3bdd86402abe720a0d58f3368e46c4ff381243690d5c53426669a`.
reverse_fold actual axioms: Quot.sound, propext.
reverse_fromRows TYPE: 6 logical lines, 5 LF, 386 bytes, 382 characters.
reverse_fromRows raw checked SHA `3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30`; printed 386 bytes, SHA `3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30`.
reverse_fromRows raw byte identity: True; lexical identity: True; canonical SHA `de6c752d1da376b684d75a2c5ba95eee50523520c493617dcc1f678335980209`.
reverse_fromRows actual axioms: Quot.sound, propext.
iteration_reverse TYPE: 10 logical lines, 9 LF, 661 bytes, 657 characters.
iteration_reverse raw checked SHA `15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6`; printed 661 bytes, SHA `15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6`.
iteration_reverse raw byte identity: True; lexical identity: True; canonical SHA `094b6bee174403be3e74712d95b8a924924446b2e6241f5efc54f52a2800116c`.
iteration_reverse actual axioms: Quot.sound, propext.
iteration_permutation TYPE: 9 logical lines, 8 LF, 617 bytes, 611 characters.
iteration_permutation raw checked SHA `8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9`; printed 617 bytes, SHA `8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9`.
iteration_permutation raw byte identity: True; lexical identity: True; canonical SHA `b6696c3f80179ca3c95ac10b10fdbdd6c2180d24b2f3cfdab4b99dde6bc7518b`.
iteration_permutation actual axioms: Classical.choice, Quot.sound, propext.
Root and an independent reviewer read each complete checked public TYPE.
Both raw TYPE views remain. Per-head byte identity is reported above. No second manual TYPE read is claimed.
All four private markers and recorded helper names are absent from TYPE.
Whole bodies remain retained and checked programmatically, not wholly read by hand.

The actual ledger has 5 Lean/Lake commands:
4 source and 1 Audit commands,
2 failures, 0
warned source exit-zero commands and 0
rejected PUBLIC TYPE commands. All inputs, raw logs and repair history remain.
The first reader stopped on TYPE wrapping. Its failed metadata artifacts remain.
The revised reader retains both raw views. No second FULL is run.
Metadata work creates no proof command. Audit has 3638
jobs and 75494 theorem dependencies.
This writer claims no seal or local publication success.

Preservation covers 93582 files/modes and 3636 older non-Audit Lean sources.
All 298 baseline Haskell files, 207 active package files, proofs, drafts,
counterexamples and optimized code remain. Extra H21 Haskell archives must
match baseline source bytes. Nine document inverses preserve all old text.
The original Audit has 3126 lines and SHA 69e0e42c6e36fbe4cf9868df0582642fe2bf2a6df7c1ad3af4fae169445f6dd3.
Its sole edit is the new module import. FINDINGS retains the repair index FIRST.
PR #65 and PR #97 remain fixed. No Haskell repair or runtime change is added.

The approved 12-commit payload was pushed and verified at 562120d456.
Eight newer local commits at this start are outside that approval.
A future exact payload needs fresh approval. Old pending-12 notes are historical.
The checkpoint stays LOCAL_ONLY/PENDING_USER_APPROVAL.
The local publisher retains seal, scoped staging and filesystem/index/HEAD checks.
It performs no network command.

Read the [next target](restart-evidence/20261022-prepend-grouping/NEXT-TARGET.md)
and its source-only inventory before the next declaration review.
