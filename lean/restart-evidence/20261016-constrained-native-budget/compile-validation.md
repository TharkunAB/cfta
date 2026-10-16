# Static native Work budget validation

Date: 2026-10-16 19:03 CEST.

## Frozen sources

- `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetNumbers.lean`: 53 lines. SHA256 `770fff2198f565ba1d8de6cc124ea17694b48cbfbbc911b2620da3e8481175e5`.
- `SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCompile.lean`: 208 lines. SHA256 `4d2645438178f8a284dbe57fba361d803854d4e4cdb6dbd0fc1bfca7d3152391`.

The evidence source copies are byte-identical. No older source was edited.
No Lake or Git command was run by this owner. Parent ran canonical builds.

## Checks

- Numbers direct check 1: terminal exit 0, no diagnostics.
- Compile direct check 2: terminal exit 0, no diagnostics.
- Numbers canonical build: terminal exit 0 in the Code/Numbers batch, 1056 jobs. Parent observed process 91789 terminal.
- Compile canonical target: built at job 1110/1111 in `native-budget-build-1.log`. That aggregate failed only in the separate root NativeBudget module. The repaired aggregate passed 1111 jobs in `native-budget-build-2.log`.
- Imported public check: terminal exit 0. All 20 declarations have an axiom probe and a full signature probe. This covers 8 Numbers and 12 Compile declarations.
- Imported kernel check 2: terminal exit 0. All 6 kernels have an axiom probe and a full signature probe.
- Final public and kernel logs contain no warnings, errors, or `sorryAx`. The reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Compile direct draft 1 and kernel draft 1 retain failed elaborations. Final checks use the frozen source and imported canonical oleans.

## Proven budget

`nodeBudget rows arity 0 = 1`.

`nodeBudget rows arity (height + 1) = 1 + rows * rows * (1 + arity * nodeBudget rows arity height)`.

`edgeBudget rows arity height = 1 + arity * nodeBudget rows arity height`.

The Numbers module proves positivity and monotonicity in height. Compile fixes a scheme with the literal empty domain and uniform original operand profiles. Node cost uses the maximum operand height. Edge cost uses the maximum child height.

The row proof reserves every occurrence in the literal source hash join. Its length is at most the product of the original row lengths. Each edge request reserves its complete child expansion. The final raw node constructor reserves one request. The child proof uses the literal ordered zip and its arity bound. It reserves one final raw edge constructor. The sentinel reserves one raw edge constructor.

The node dispatcher follows the actual guard order. Empty and self are pure. Empty-domain reset is false. Swapping preserves the maximum height and the same fixed profiles. Empty seen excludes the repeated-pair branch. The finite ordinary profiles exclude Mu, explicit union, and reference branches.

`body_bound` checks the literal yielded current checked body. Error and blocked branches cannot supply that yield. Accepted children and sentinel code retain the uniform continuation budget. Arbitrary returned constructor values do not introduce a new recursive request.

## Integration probes

1. The concrete recurrence gives node budget 209 and edge budget 628 at rows 2, arity 3, height 2.
2. Duplicate matching full-guard rows reserve four edge calls and one final node constructor.
3. A node with a nonempty equality class and Boolean guard has the claimed budget.
4. Accepted nullary child code uses one constructor for any actual combined constraint.
5. Sentinel construction needs no child profile and uses one constructor.
6. Actual arity mismatch emits the sentinel with the exact driver finish continuation and no field-load premise.

## Scope

These are static code expansion certificates. They count raw constructor Work requests, including repeated subproblems. Warm memo hits can skip those requests. No uniqueness or pair-production assumption is used.

The budget does not count equality-cache operations, interpreter instructions, GHC demand events, or runtime allocations. No execution completion, future result law, physical final state, WordRanges, or successful recursive callback is a premise. The separate execution module must relate this static potential to actual finite prefixes. This task does not remove higher caller numeric plans or prove a finite instruction bound.
