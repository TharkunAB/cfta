# Root initialization validation

Validated at 2026-10-16 15:04 CEST with pinned Lean `leanprover/lean4:v4.34.1`.

## Source and checks

Owned module: `lean/MicroCFTA/SourceCurrentAllocatedPartialInitialization.lean`, 144 lines.

SHA256: `83bae4390352d9a40cc16c3258d63d0443c161e85177f026ed480c2443652eff`.

- Direct module check: `init-direct-2.log`, exit 0, no warnings.
- Root-managed canonical check: `init-build-1.log`, 1329 jobs, success. The only warning is the older unused `inputs` binding in `InternedFreshOrdinaryClosedCompletion`.
- External imported-module checks: `init-probes-2.log`, exit 0, no warnings or errors.
- The external file checks six public theorem axiom reports and full signatures, six public definition signatures, and six integration kernel axiom reports and full signatures.
- All twelve final axiom reports are clean. They contain no `sorryAx`. Their union is the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. `emptyValue_live` uses no axioms. The generic warm-hit kernel uses only `propext`.

The first direct module log records two elaboration errors in the new source. These were corrected before the source freeze. The first external probe log records two probe errors and an unused section variable. Failed elaboration produced `sorryAx` placeholders in that failed log. These are not proof evidence. The final external log has no placeholders. Both failed logs remain available.

## Integration kernels

`init-checks.lean` derives these facts without supplied future result laws:

1. Covered original history and actual construction derive successful existing physical field loads in the final empty-allocated equality cache. The kernel also derives allocated readiness and exact raw readback.
2. Constructed initialization publishes the exact root request, starts cell zero in the caller's empty node table, and derives the running cell's full memo `Sound` invariant. It assumes no root body law or result.
3. The complete original history followed by actual empty allocation retains all earlier canonical table entries and issued identities. Both completed equality-operation tables stay empty.
4. A concrete valid warm equality cache stores the empty key at identity 37. Empty initialization returns identity 37 and retains the whole interner unchanged.
5. Any existing empty-key entry determines the returned empty value and retains the whole interner. This kernel does not assume identity zero.
6. The singleton inventory computes root membership in its finite input model from the actual original build. It takes no model-validity callback.

The public `constructed` theorem derives every `Context` field: current checked readiness, computed input admission, both caller result-table laws, merge residency and all-ambient coverage, fourth-table correctness, three-table global validity, and the physical probe invariant. It also derives the exact allocated empty inherited identity and root availability, closedness, and original syntax scope.

## Scope

The initial native tables, completed equality-operation tables, caller result tables, merge table, fourth table, and three global tables are deliberately cold modeled tables. The physical equality interner retains the exact covered history and the exact empty-allocation result. No source-global cache reset is asserted.

This theorem packages initialization. It does not prove general outer progress, unrestricted termination, concrete CAF forcing, GHC demand order, runtime publication, or process-global cache correspondence. A wrapper can use the derived context with existing literal root exactness. Such a supplied-success wrapper still needs actual reached checks and the actual successful worker return.

No Haskell source changed. No Haskell test, network request, Git mutation, Audit edit, or older proof edit was performed by this task. Root owns canonical builds and checkpoint publication.
