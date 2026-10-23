# Installed enumeration-until source review

Reviewed at 2026-10-24 01:13 CEST. **SOURCE CLEAR.** I read all 180 lines of `lean/MicroCFTA/EnumerationUntil.lean` and all 265 lines of `lean/MicroCFTA/EnumerationUntilBridge.lean`. I checked the one-line additive Audit import and the live helper statements used by the bridge. I found no remaining type, proof, or statement-scope defect by source inspection. This review ran no Lean/compiler command, prepared program, network operation, or repository mutation.

## Exact cut

| File | SHA256 |
| --- | --- |
| `lean/MicroCFTA/EnumerationUntil.lean` | `3d54b3a6ca3db0c668f6b8910c62adcae099f3eae79cfb6d82ee9176710fd137` |
| `lean/MicroCFTA/EnumerationUntilBridge.lean` | `ac5eb73483f5d59bf52f1a251c55322050f289cc8a9dd052d032ab8e32638642` |
| `lean/MicroCFTA/Audit.lean` | `6a380998c9c8dad36734023907fdb192ad9a01d04bb193e3a0f08ccc0d49044f` |

Repository HEAD remained `790c39ce21f0be612fafcb6a36eb972ac5bf03f9`. The worktree change at this cut consists of the two new modules and `import MicroCFTA.EnumerationUntilBridge` prepended to Audit. Existing implementation and proof bodies are unchanged. Root authored the final proof body. Guard authored the operational definitions. I reviewed both and authored neither.

## Public statements and proof dependencies

`no_stop_eager_successes` specializes to no stop rule, identity narrowing, and the existing eager expander indexed by the same bound. Its conclusion is equality of ordered successful result lists after mapping old Unit results to `none`. It retains the complete returned `State`, branch order, and multiplicity. It does not assert equality of error rows, callback traces, or returned caller-oracle state.

`no_stop_eager_success_iff` states both necessary facts for the same supplied run: the new result is `none`, and the old driver succeeds with Unit and the identical `after` state. The proof converts membership through the exact success-list equality. It does not select a second unrelated execution or change fuel.

`no_stop_eager_outcome` adds `Safe before` and an actual successful new run. It derives `Safe after`, `before.counter ≤ after.counter`, and `Finished graph after` by applying the existing `EnumerationDriver.enumerateFully_outcome` to that same run. It adds no validity, completion, resource, or acceptance oracle. The counter statement is nondecreasing growth. `Finished` excludes eligible pending slots; it does not assert a concrete term language, resolved residual guards, or absence of unconstrained recursive markers.

The auxiliary proofs use the actual `run_bind`, successful membership, and UnionFind lookup interfaces. `getValue_repeat_value` retains values across two successful representative reads. It derives the common representative from preserved old paths and path uniqueness. It needs no unlisted global forest-validity assumption. `empty_out_after_read` then excludes a successful eager expansion of the just-read empty node, including fuel zero. The private empty-observation lemma applies `ReadOnlyOracle` to the successful pre-callback and excludes the resulting successful tail. Nonempty cases retain actual callback state threading and the eager worker. The fuel induction recurses on the same supplied continuation and actual intermediate machine state.

The earlier projection defects are addressed in the installed body: the bind proof normalizes its induction hypothesis with `simp only [successes]`; the congruence proof clears `rowsEq` before induction. The local List instances follow the existing enumeration modules. There is no added axiom, admission, unsafe declaration, or local proof-limit override in either new file.

## Operational definition check

The definitions retain the positive-bound stop test before scheduling, all candidates including blocked ones, and the nonempty test. Repeated recursion precedes narrowing and callbacks. A narrowed empty view rejects before the pre-callback. Identity narrowing adds no slot write. Changed narrowing keeps the original suspended constraints. The worker rereads the slot after the pre-callback and later writes to its captured representative. The shallow root and child helpers have distinct behavior. Positive edge bounds pass predecessor fuel to child preparation. Zero bounds remain explicit errors. The literal eager worker and edge equations retain their original complete state actions. Partial rendering keeps pending holes and residual state; it is not an acceptance certificate.

## Required precision

`ReadOnlyOracle` constrains successful callback branches only. This is sufficient for this success projection. A callback can still emit errors or have no successful branch. The new early empty rejection can therefore change the full error list. An arbitrary state-changing callback can revive an empty slot in the old driver, so the observer premise cannot be dropped.

The equal-state theorem compares the new eager specialization with the existing modeled eager loop. Both use the old modeled slot scan. Haskell now uses cached selection, whose representative-compression effects can differ. The module introduction explicitly keeps that source-refinement obligation open. It also does not equate the public shallow path with eager execution, or claim realization of both Mu and InternedUnion from the abstract recursive graph view. Existing H23 conditional results and the strongest H6 result are unaffected. No Haskell repair or end-to-end whole-pass refinement follows from these statements.

I inspected Root's retained `combined-check-5/report.json`: its recorded Lean 4.34.1 command enables warnings-as-errors and all linters, records exit 0, and records a literal-empty log. This is retained Root-owned evidence, not a new reviewer-run check. Focused build, Audit, and complete checked public TYPE readback are separate evidence cuts. This report makes no claim about their future results.

## Independent complete checked-type addendum

At 2026-10-24 01:14 CEST, I read the complete 165-line, 12,193-byte `public-2/raw.log`, including all 21 checked declaration types and all 12 printed theorem axiom sets. The log SHA256 is `c5bce7e3d368101c34e6b78440a78d4ea187c95bafbd6d635df48da9a1e44ba2`. The diagnostic source SHA256 is `4e9fbfb6fcf637321849b9f4bab5ec7138b621e18b371eaf4a17c88ce9c7941e`. Its retained report SHA256 is `4b52e9071623a66313705e93d2d1b52df20398bbc9e12af118a2d72c82350574`, with exit 0 and the matching raw byte count/hash. I read the complete diagnostic source and correlated each requested declaration with its output. This is a manual review of complete checked types and axiom output. No printed proof BODY was requested or manually reviewed.

The checked types confirm the exact scopes above. The main three declarations retain the explicit `ReadOnlyOracle` premise, the same fuel and initial caller state, and the same full `after` state. The success-list equality has the expected map to `none`. The equivalence has exactly the result equation and old successful execution. The outcome adds only `Safe before` and the actual new successful run before deriving safety, nondecreasing counter, and `Finished`. There is no added empty-graph assumption, success oracle, final certificate, hidden semantic premise, or private helper in these public types. The operational types retain the optional stop, arbitrary narrowing, indexed expander, scheduler preference, and caller oracle.

Each main bridge theorem's actual axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`, ignoring the displayed universe parameters. The other nine theorem axiom sets are subsets of these standard axioms; `successes_pure` has none. This is the observed output, not an assumption that every declaration uses three axioms.

`public-1` is retained with exit 1. Its single diagnostic is the unsupported display option `pp.width`; its declaration output is not selected as the successful readback. `public-2` removes that option and records exit 0. This diagnostic repair does not change either production module. Their hashes remain those in the exact-cut table.

I also read the actual focused-build and Audit logs/reports. The focused build records exit 0 and 13 completed jobs. Audit records exit 0, 3,659 jobs, and checked axiom dependencies for 75,635 MicroCFTA theorems. Audit raw SHA256 is `ea0519b26f87fce5faf029a800d3e01af49e0d5970975a20a326b462b3ea053e`; report SHA256 is `65322faaf083d8b6cdd4787321ebb13792e04bf6af47922f375636421ce40d5d`. It replays the single old unused-`inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean:24:5`; neither new module reports a warning. These are actual Root-run results inspected after the earlier source-review cut. I did not rerun them.

Final status: **SOURCE AND COMPLETE ACTUAL CHECKED PUBLIC TYPES CLEAR** for the pinned module bytes and this readback. The cached-source, arbitrary-error-list, shallow/eager, and end-to-end semantic limits above remain in force. No Haskell repair, whole-pass correctness, new strongest combined result, commit, or publication is claimed by this review.
