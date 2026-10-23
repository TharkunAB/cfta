# Enumeration-until final document review

Reviewed at 2026-10-24 01:16 CEST. **CLEAR for the current documents and their source/evidence claims.** No document correction is required. I read the complete 101-line focused note, the complete new 33-line update, and the complete first Haskell repair index. I checked all nine recorded document inverses. Historical text was checked by exact inverse, not manually reread in full. This review ran no compiler, prepared program, Git mutation, network operation, or repository write. The only reviewer output is this report.

## Exact inputs and inverses

The focused note is `lean/notes-current-enumeration-until.md`, SHA256 `6c8a3c88e8bbd6e3cd6248b921b060a603034ae3aa5767bc1ea8ca42c125e58a`.

The insertion record is `/tmp/mcfta-enumerate-until-20261024/document-changes.json`, SHA256 `e9434a1fa714e5291b81e20e393ae63523756e0be1ef94893a3e63f6dce6d4de`. Its nine paths are `NEXT-PROMPT.md`, `HANDOFF.md`, `FINDINGS.md`, `lean/README.md`, `lean/SYSTEM.md`, `lean/API-COVERAGE.md`, `lean/COVERAGE.md`, `lean/notes-proof-status-20261017.md`, and `lean/notes-current-system-claim.md`.

For every path, the recorded insertion position contains the exact inserted string. All nine strings are identical, contain 33 LF characters, and contain no CR. The actual full-file SHA256 equals the recorded after hash. Removing only that insertion produces the exact current HEAD bytes and the recorded before hash. Thus no earlier document bytes were replaced or lost. In FINDINGS, the entire prefix through the complete external Haskell repair index is also byte-identical to HEAD. It remains before the new enumeration update. The negative-depth fix and both open LPO defects remain explicit. This checkpoint does not claim to repair either LPO defect.

The actual proof commit is `ecabbf38e669d96275ce991fa8a843bcec3b51ed`, with parent `790c39ce21f0be612fafcb6a36eb972ac5bf03f9`. Its exact three-file payload is the two new enumeration modules and the one additive Audit import. No earlier implementation or proof body, and no Haskell source, is changed by that proof commit.

## Scope and validation

The note and current update agree with the reviewed installed sources: `EnumerationUntil.lean` SHA256 `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137`, and `EnumerationUntilBridge.lean` SHA256 `ac5eb73483f5d59bf52f1a251c55322050f289cc8a9dd052d032ab8e32638642`. The independent complete source/type review is `/tmp/mcfta-enumerate-until-20261024-installed-review.md`, SHA256 `ad30e7eb42bc1ebed690fe9965844e5726193a866eb3d4b3d320c09016723e37`.

The docs correctly restrict the ordered-success equality to no stop, identity narrowing, eager expansion, the same finite bound and modeled scan scheduler, and `ReadOnlyOracle`. They retain multiplicity and the full final state while mapping Unit to `none`. They do not add a Safe or completion premise to that equivalence. The outcome theorem adds Safe before and derives only safety, a nondecreasing counter, and Finished. The note explains that Finished is not residual-guard discharge or concrete acceptance.

The read-only definition is stated precisely: each successful callback branch preserves the complete machine state, while rejection, errors, and caller-state changes remain possible. The empty-node callback-order difference is disclosed. Error-list and callback-trace equality are not claimed. The shallow/eager observation counterexample is identified as a source derivation rather than a native test. The note does not claim a public native slot setter. Speculative holes need not have an accepted completion. Cached scheduling, path compression, graph realization of Mu/InternedUnion, and frontend/source correspondence remain separate obligations. Older H23 conditional results are preserved; the new H23 counter composition remains queued.

The validation wording matches retained Root-run evidence. Final combined strict check 5 records exit 0 with a literal-empty log, all linters and warnings-as-errors. The installed focused build records exit 0 and 13 jobs. Audit records exit 0, 3,659 jobs, and 75,635 checked theorem dependencies; its sole warning is the old unused `inputs` binder in `InternedFreshOrdinaryClosedCompletion.lean:24:5`. The new modules have no warning. Public readback 2 records exit 0 and contains the 21 complete checked signatures and 12 axiom reports already read independently. Its raw SHA256 is `c5bce7e3d368101c34e6b78440a78d4ea187c95bafbd6d635df48da9a1e44ba2`. Actual dependencies are standard subsets; the three main bridge theorems use the stated standard three axioms.

All 12 retained attempt reports have raw byte counts and hashes that match their logs. Earlier temporary-package path failures, proof/type errors, and the unsupported `pp.width` display option remain failures. The docs do not report those attempts as passed or claim first-try success. No new Lean or native test was run by this review.

## Checkpoint boundary

The bootstrap report confirms the stated start, imported main `6b62b4afefca80bb05f5a37546212a99980aa3df`, baseline count 126,320, and backup `codex/backup-enumerate-until-20261024-0055`. Root's full file/mode preservation check and evidence archive are separate closing operations in progress at this review cut. I did not rerun or pre-claim them. The documented evidence directory is the intended archive destination.

The current update explicitly precedes the evidence commit and its authorized push. It makes no future publication claim. H6 `constructed_node_calls` remains the strongest combined result. The full goal remains active and incomplete. Resource, practical-width, full-pipeline, Haskell/solver, and convergence obligations remain open. No additional Haskell repair is claimed.
