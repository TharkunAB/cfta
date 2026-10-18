# Finite root reconstruction review

The module lifts an existing raw `RootMatch` to finite observations of two actual warm stored calls. The observation `view` and the ready execution `common` are separate parameters. The source SHA is `0b23fb52cd2aecc3e5905694fb2bc092b7b695f9041d7e1bf9a864a66a83aa81`.

`Executions depth view common first second a b` quantifies actual successful stored calls at `common`. It relates their complete outputs by `RelatedAt depth view`. It does not assert completion. `reconstruct` takes initial `Ready common`, raw availability, replacement availability, and `RootMatch`. It resolves matched references at depth `n+1`. Matched literal Mu atoms require actual execution alignment at depth `n+1`. Ordered row children require execution alignment at depth `n`.

The proof obtains every needed atom call and ordinary row call from `SourceCurrentStoredLiteralExecutionParts.atom` and `.row`. It obtains returned literal parts from `.parts`. Thus the conclusion does not take a whole-parent result relation or a future child completion premise. Row calls retain complete symbols and guards. Their child lists retain order. Child physical Empty equivalence proves the same survival test. Available normal result parts prove physical Empty agreement separately from epsilon observations.

The proof copies private reference, row, and nonempty-part lemmas from the frozen `SourceCurrentLiteralPartsObservations` into the new module. This keeps the old source byte-identical. The copies split root unions and keep Mu atoms opaque. The proof uses actual stored completion from initial Ready only to derive output availability at literal successful calls.

## Boundary

This is a conditional finite reconstruction step. It does not produce raw `RootMatch` for arbitrary source programs. It does not prove the Mu-atom induction obligation. When a raw root is a Mu, that obligation can be the whole root case and remains explicit. A source producer must justify that its atom hypotheses come from strict source induction. The theorem has no BinderFree, finite Cap, closed-root, or unused-local premise. It makes no reader transport, all-depth, general binder, or termination claim.

## Verification

Selected strict attempt: `finite-root-direct-2`, exit 0, literal zero-byte log. Selected canonical build: `finite-root-canonical-1`, exit 0, 602 jobs, no warning. Selected public group: `finite-root-public-1`, two complete declaration/proof/axiom triplets, all eight options, no printer omission, only the three permitted axioms. The hardened probe checker passes. There is no independently counted constructed group in this component; publication and source-node integrations belong to other components.

The first strict attempt failed only because `by_contra` is not in this project's tactic set. Its source, error log, metadata, and effective memory limits remain in the allowlist. The final proof uses `Classical.byContradiction`. All four jobs used 4 GiB maximum, 4 GiB high, zero swap, and the five-minute wrapper limit. The component does not pin shared mutable root artifacts.
