# Conditional finite ordinary native memo certificates

Timestamp: 2026-10-16 16:09 CEST.

The new source is `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryStored.lean`.
Its SHA-256 is `344f8d121d1edfba172986cad36ce5f06ed2f53148380043e80d7af2e5681b0e`.
The source has 209 lines. The frozen copy has the same bytes.

## Schema and invariant

The current checked state retains a `SourceRecursiveIntersectionThunks.State` plus the literal equality-operation state. The native state contains separate node and edge `FlatMemoThunk` tables. Each cell retains its complete original request: domain, ordered left operand, and ordered right operand. Suspended, evaluating, and returned statuses remain distinct. `PhysicalCache.Valid` supplies physical residency and exact checked keys. It does not supply a structural or historical producer law.

`NodeCertificate request result` is conditional on all three facts: the request's incoming seen list is empty; the left operand belongs to `FiniteOrdinaryDomain.Node`; and the right operand belongs to that domain. Its result is domain membership and a height no greater than either actual stored operand. `EdgeCertificate` uses the analogous edge domain and edge height. There is no guard or equality-class restriction. Neither certificate asserts result availability, free-metadata closure, or language equivalence.

`Stored native` quantifies over the actual returned node and edge cells. Its certificate is indexed by the request stored in that same cell. No result condition is imposed on a suspended or evaluating cell. No result condition is imposed when the incoming seen list is nonempty or an operand lies outside the domain. The independent physical invariant remains separate.

The empty-seen condition is necessary for the intended producer theorem. A repeated pair in a nonempty incoming seen list can select a recursive reference even when the operands are finite ordinary values. The new module does not assert a finite ordinary result for that branch. The final integration checks explicitly show that the conditional certificate imposes no constraint when this antecedent is false.

## Public results

The module provides twelve lifecycle and observation theorems:

- `initial_stored` derives the invariant for empty native tables over any source machine.
- `advance_stored` retains it through the literal machine advance. This theorem needs no heap-growth premise because the invariant is syntactic and the two cell tables do not change.
- `lookupNode_stored`, `lookupEdge_stored`, `demandNode_stored`, and `demandEdge_stored` preserve existing certificates without a candidate-domain or result premise. Publication and demand create no returned result. The unresolved node-key bypass remains unchanged.
- `finishNode_stored` and `finishEdge_stored` accept a certificate for the exact evaluating owner at the selected handle. They store it only through the literal finish operation. The other native result family remains exact.
- `node_observed_ready` and `edge_observed_ready` use current physical validity, ready original inputs, checked key bounds, and the actual lookup and demand equations. They recover the conditional certificate for the exact requested operands, the unchanged post-demand native state, and physical result availability or edge residency.
- `node_started` and `edge_started` use the same physical checks to identify the exact evaluating owner, recover its actual cell, and preserve the structural invariant. They do not assume a completed body.

The finish premise is a local producer obligation. It is not a completion theorem or a public callback that supplies a future trace. This module does not derive that producer obligation. A completed checked producer proof must establish it independently before a whole-query structural claim is made.

## Validation

The root canonical build passed with 1065 jobs. `stored-build-1.log` contains the raw output. Its only warning is the older `InternedFreshOrdinaryClosedCompletion` unused-variable warning. The source itself reports no warning.

The direct source check passed in `stored-direct-2.log` with exit code 0 and no output. It used the independently compiled Domain dependency in an isolated temporary module directory. No canonical artifact was changed. The first attempt records a missing isolated dependency file before that directory was populated.

The final external check is `stored-checks-4.log`. It passed with exit code 0 and no errors, warnings, or `sorryAx`. It uses the final canonical module. It reports full signatures and axioms for all twelve public theorems and all three public definitions. The reported axioms are `propext` and, for physical exact-request bridges, `Quot.sound`. No additional axiom is introduced.

Five integration theorems also pass with full axiom and signature reports:

1. Cold initialization followed by node publication, node demand, edge publication, edge demand, and a machine change derives the invariant without any initial result certificate.
2. Literal node-Empty and edge-singleton-Empty certificates are derived directly, then installed at exact evaluating cells in both families. Equal numeric handles in different families need no exclusion premise. No future producer law is supplied for these structural constants. This check does not assert that an arbitrary body actually returns them.
3. A physical warm node hit with empty incoming seen list and both operand domains yields the requested minimum height bound and an available domain result at the actual reached state.
4. The analogous warm edge hit gives domain membership and the minimum original edge-height bound for every actual returned child, with exact returned-edge residency and retained `Stored`.
5. Nonempty incoming seen lists make the conditional certificates vacuous. This records the scope restriction directly.

The first integration log preserves two invalid field-projection elaboration errors. The second passed against the isolated source output. The third passed against canonical output; its enclosing shell command returned status 1 only because a following search found no errors. The fourth repeats the exact canonical check as a standalone command and records exit code 0 unambiguously. No source module changed during these checks.

## Remaining scope

Actual checked body preservation, full trace preservation, and finite execution from legitimate initial invariants remain producer and completion obligations outside this lifecycle module. General recursive domains, Mu results, explicit unions, references, pending publication, host demand order, and concrete machine identity remain separate. No older eager execution or historical `Produced` relation is transferred. This increment changes no Haskell source.
