# Actual completed native node memo observation

Frozen and validated 2026-10-16, Europe/Stockholm.
Source: `lean/MicroCFTA/SourceCurrentAllocatedNativeCompletedMemo.lean`.
SHA256: `f9d1753fe923b3c0c17902d2d34c3f8e723544e454dda4570008a20bd03c2412`. Lines: 162.

Focused canonical build: terminal 0, 1088 jobs. Only the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion` occurs. Public probe: terminal 0; seven public axiom reports, seven fully explicit signatures, and eighteen kernel examples pass. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

## Exact commands and evidence

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeCompletedMemo
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-warm-history/memo-probe.lean
```

Raw terminal outputs: `memo-build.log`, `memo-probe.log`. The exact probe and source snapshot remain beside this note.
The examples include an actual empty-input cold request allocating one returned native node cell, exact key/handle metadata, derived final-cell observation, exact two-step repeat with unchanged full State, and an actual unresolved-placeholder request taking the direct path without root publication. The last example uses a constructed actual physical Trace and derives the first key checks internally.

## Public contracts

- `done_retained` derives retention of both returned-cell families and both publication tables from initial Shape and the actual completed execution.
- `completed_node` takes initial PhysicalCache.Valid, original request NodeReady, explicit KeySafe, a literal cacheable request key, and actual completed requestNode execution. It derives a final published handle and a returned cell containing the EXACT complete original request and returned value. It does not take a supplied final cell, final Valid, result language law, or final residency premise.
- `warm_node` is the low-level literal-cell replay law. It returns in exactly two checked interpreter steps with the entire checked State unchanged. It skips the source body and equality operations.
- `completed_repeat` derives that cell from actual completion, then applies the low-level warm law. Its public premises contain no desired warm answer or final cache oracle.
- `uncacheable_call` retains the exact direct lookup and actual direct-body trace. It does not assert that the body is silent or that a repeated unresolved request is a memo hit.
- `completed_cases` gives the literal optional-key split: direct trace for none, or derived final cell and unchanged warm return for some. Machine bounds are conditional on an actual cacheable key.
- `repeat_of_trace` consumes initial PhysicalCache.Valid, the literal key, and an actual completed physical Trace. It extracts current NodeReady/conditional KeySafe from the FIRST actual instruction. The remaining observation proof uses raw actual body Steps and protected finish retention, not future validity or semantic completion.

The proof uses existing key/returned-cell retention and actual running-cell preservation. No independent new invariant is assumed or introduced. In the started branch, physical key injectivity identifies captured=request, actual body completion retains that evaluating handle, and the literal finish stores the actual returned result. Body allocations and all equality-operation changes remain in the actual returned State.

## Source correspondence and limits

Live `cfta/src/Data/CFTA/Interned/Operations.hs:480-485` looks up `nodeMemoKey` on both original operands. Cacheable calls use `memoFlatTypeableWith` with domain identity and ORDERED operand keys. A placeholder takes `onNode` directly. Source key lookup precedes the empty/reset/self/swap/body dispatch (lines486-520). This module preserves that ordered key, exact original captured request, and completed-hit skip. The edge wrapper remains at lines564-578 and is not extended here.

These theorems concern actual executions of the checked Lean machine and its resident completed-cell model. They do not establish the GHC publication-before-forcing schedule, pending-thunk behavior, runtime flat-table implementation, concurrency, or global unsafe IO. Physical KeySafe remains the machine-range/no-alias boundary. The main observation theorem assumes actual completion, as an observation theorem must; it does not prove native termination by assuming a future body result. Independent completion receipts can supply that execution.

Only this new proof and owned evidence were written. No old proof, Haskell, Audit, documentation, or Git mutation was performed by this task. No active process remains.
