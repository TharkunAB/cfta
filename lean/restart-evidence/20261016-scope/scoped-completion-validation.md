# Actual checked scope completion

Validated 2026-10-16 06:12 CEST. Both owned proof sources are frozen. Exact hashes are in
`scoped-sha256.txt`. The frozen copies retain the validated source bytes.

## Result

`SourceCurrentAllocatedNativeScopedCode.Certified` records local syntactic
scope certificates for actual source code. Primitive continuations use the
literal returned machine and actual completion equation. Node callbacks
receive `Available` and `Scope request.domain.key.seen`. Edge callbacks
receive `EdgeResident` and `ResultScope.EdgeScope` for the same incoming
seen pairs. There is no symbol-matching, semantic model, rank model, or
local language premise in this certificate.

`SourceCurrentAllocatedNativeScopeCompletion` proves finite actual checked
completion with returned scope and the returned-cell `ScopeCache.Scoped`
invariant. The proof follows the same protected physical traces. It keeps
all physical heap and equality-operation effects.

The private strong induction uses independent `requiredFuel`. It derives
local child scopes, then the actual request result scope before each
finish. The actual body trace retains the exact evaluating request and
handle. Native ready hits use initial physical validity and the explicit
warm scope cache. Every private recursive body and source-certificate
interface is discharged internally. No public endpoint assumes a finish
scope, a completed callback, or a future invariant.

Public endpoints are `node_complete`, `edge_complete`, `request_complete`,
`edge_request_complete`, `initial_complete`, and `cold_complete`.
`Receipt.done` erases the receipt to the literal checked execution.

`Receipt` extends the existing physical receipt. Its fields include the
same actual trace, final `Good`, machine `Extension`, heap `Keeps`,
operation-cache growth, and residency postcondition. It also stores
`scopedCache`, `semantic`, and `law` for that exact final state and value.

`initial_complete` derives the pure schedule and active bound from original
available closed inputs and initial idle native cells. It returns the
actual receipt, final idle state, and `value.free = []`. The free-list law
comes from result scope at the actual empty root domain. The warm
`ScopeCache.Scoped` premise remains explicit.

`cold_complete` uses literal empty native memo tables. It derives scope
validity and idle state directly. It returns the same actual result with
an empty free list, without assuming initial or final result scope.

## Premises and limits

- `Good` contains physical native validity, required heap readiness,
  equality operation-cache validity, and successful same-cache equality
  field loads for resident edge keys.
- Initial `SemanticReady` supplies the actual guarded and budget heap
  invariants used by optional binding. Final semantic readiness is derived
  along the actual physical trace.
- General recursive endpoints retain original source scope, independent
  pure-schedule completeness, actual current operands, source heap growth,
  issued history, active-frame bounds, and reached `WordRanges`.
- Initial closed endpoints derive schedule completeness and active bounds.
  Actual reached `WordRanges` remain explicit. This module does not prove a
  fixed-width global capacity bound.
- Warm returned-cell scopes are explicit initial invariants. Cold native
  tables derive these scopes without a supplied result law.
- Scope is syntactic. Edge scope needs no matching-symbol premise. Language
  exactness remains in the separate contextual completion module. Root
  integration can join both completed runs by actual done uniqueness.
- Checked rejection and arity mismatch keep their actual sentinel allocation
  and child skip. Actual accepted code propagates ordered child scopes.
- No old eager execution or old semantic `Produced` invariant is used.
- These are actual checked Lean-machine results. GHC lazy evaluation,
  pending thunk publication, machine containers, and full source/runtime
  correspondence remain separate boundaries.

## Validation

Focused pinned commands:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeScopedCode
    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeScopeCompletion

Both completed with exit 0. The final completion target passed 1099 jobs.
No new warning was emitted. The pre-existing unused `inputs` warning was
replayed from a dependency.

Public probes:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-scope/scoped-completion-probe.lean

The direct probe completed with exit 0. Eight public axiom checks and eight
signatures pass. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Three kernel examples check actual receipt erasure and physical plans;
cold completion, arbitrary extra fuel, and closed result metadata; and
actual edge lookup/demand/finish without a matching-symbol premise.

Only the two new owned Lean modules and new evidence files were written.
No old proof source, Haskell source, Audit, documentation, or Git state was
edited by this task.
