# Main-integration seal-script source review

Recorded: 2026-10-24T04:28:16.905927+02:00. Status: CLEAR_SOURCE_ONLY_FOR_ROOT_CAPPED_EXECUTION.
I read both complete final scripts, including the explicit seal-script-review
requirements, and inspected the actual area schema, native pins, document/index
metadata, resource cut, previous publication fields and Root review. Root authored
the scripts. I authored an earlier helper proposal, which this task does not change.
The separate source/document peer review remains the authority for those claims.
I did not execute either script, any compiler, verifier, test, Git command or
network operation. I wrote only this review file. No seal result is claimed.

The fixed baseline ed89dccbf8242231cde1abf87e52f909cb726470 and count127926 match
baseline.json. Merge metadata supplies ea9965949bdad994709318cf54162bea1c23cf40
with the exact baseline/main parents. The verifier checks those parents against
Git, ancestry, current main74250bd889685da436cdbfe32ac4b5a0878ffd09 and complete
baseline/merge tree equality. It checks exactly the five upstream delta paths,
bytes against both main and local repair07229ca7f3, and baseline/main blob modes.
These are adequate source-identity conditions to reuse the retained checks.
The script does not run a build or test. Its zero repeated-tests field records
this source-only checkpoint; it is not a new validation result.

The compressed baseline tree must equal the actual complete Git tree. Every old
blob and mode is checked. The nine document insertions have the expected schema
and are reversed before comparison. FINDINGS then reverses the separately
recorded first-header replacement. Its recorded hashes are full-file hashes,
while before/after strings are the bounded header prefixes; the implementation
uses these two roles correctly. The status insertion's FINDINGS before hash is
the index replacement's full-file after hash. The index remains first, all six
rows are retained, and the first five rows must be unchanged. There is no Audit
or Lean-source exception. Stashes, other worktrees, protected refs and the exact
backup remain checked. Both scripts reject tracked worktree/index differences.

The archive rejects an existing destination and requires source/docs, seal-script
and Root reviews before creation. It retains the complete work area, deterministic
compressed tree, actual note, saved verifier and previous callback checkpoint's
three post-seal six-artifact bundles plus publication records and source script.
Current previous-publication fields have the exact expected baselineed89 head.
The active archive-1 receipt family is excluded while incomplete. All other flat
checkpoint inputs are copied. A complete nested-file manifest is built, and the
verifier requires exact file-set equality with only SHA256SUMS excluded. It then
checks every manifest hash. The seal result is written outside the archive.

The actual preseal cut has one baseline job: its high/max limits are4GiB,
swap is zero, recorded allowance age is zero and remaining allowance is93%.
The verifier's exact one-limit/one-usage count is therefore consistent. The
archive's own active receipt is correctly outside that historical count. The
current destination is absent. Root has recorded document commit
46a67c5d7b4a0301c0ee3006755f178ce9fded7f and will execute the archive afterward.

I found no material current-schema contradiction, unsafe source bound or missing
preservation gate in these final scripts. Final baseline verification, archive
seal, local publication and push still require Root's actual capped execution.
The frozen helper proposal and earlier evidence are not modified by this review.

Exact reviewed input pins:

- `/tmp/mcfta-th-repair-main-20261024-verify.py`: 6079 bytes, SHA256 `100077fe21d25df230c958446650e1b833a4c67e36c95533270a2d9a00129e40`.
- `/tmp/mcfta-th-repair-main-20261024-archive.py`: 3779 bytes, SHA256 `26baefbba0b2a86a222df381bae1aa007708bfab9ce040c6829ea4ffa9322b2c`.
- `/tmp/mcfta-th-repair-main-20261024/baseline.json`: 420 bytes, SHA256 `c7b39ef61f4ebdd0caccecd62254f3539054a055b3e158c872c9d3b28394cf11`.
- `/tmp/mcfta-th-repair-main-20261024/merge.json`: 291 bytes, SHA256 `a44c0aa8def52613b6ea87901bf4289dca608928a97d92cadeae1f846581666a`.
- `/tmp/mcfta-th-repair-main-20261024/native-source-pins.json`: 679 bytes, SHA256 `376d5c76c52be1a38bf01c6b5fe81de886534941c271f989e08e7635f3690884`.
- `/tmp/mcfta-th-repair-main-20261024/document-changes.json`: 13133 bytes, SHA256 `a40cc123512be40a9a26ce76ed2660c9a4269773b7adbc8975af03b5ac87ce3a`.
- `/tmp/mcfta-th-repair-main-20261024/findings-index-change.json`: 8104 bytes, SHA256 `3ad757afaef8a289751cf722a50c347ae99a7072a912102cf5639ce618f148c9`.
- `/tmp/mcfta-th-repair-main-20261024/main-delta.patch`: 5318 bytes, SHA256 `ceb143eefb2208f3340548d1a89c664ad71fa43629b7fdd062f607aedaf33338`.
- `/tmp/mcfta-th-repair-main-20261024-root-review.md`: 2115 bytes, SHA256 `8a23f325d45116db9e19c44de5a34626324d090048193923725f1562b4d83933`.
- `/tmp/mcfta-pruning-record-types-20261024/remote-publication.json`: 367 bytes, SHA256 `a6a82e6d606cd183df6c52fed7a25fc7ef2da20d902963a0acff56c9735f1ed3`.
- `/tmp/mcfta-pruning-record-types-20261024/publication-spec.json`: 247 bytes, SHA256 `608423e0006d420e64e921b356b39e3fce8233c1ae04d7ac27cb8c9f28a8cbf9`.
