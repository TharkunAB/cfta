# Controlled source rewrites for the zero-depth audit

Prepared: 2026-11-14 21:20 CET.
Status: UNCOMPILED CANDIDATE.

This packet repairs the remaining errors in the strict check of `b4592853`.
The original audit packet and both earlier candidates remain unchanged.
All five explicit public theorem headers are byte-identical to those candidates.
The concrete source and initializer are unchanged. No premise is added.

The source acceptance proof rewrites only the outer `relevantRows` call.
It resolves the actual empty selection and changes the remaining goal to the
explicit `Except.ok (termsRows ... 0)` equation. The zero terms equation closes
that local fact. The final frontend goal reduces to a map over `Except.ok []`.
`rfl` closes that remaining goal. The proof does not put the recursive
`relevantRows` equation in the simplifier.

The empty-language proof now simplifies the hypothetical empty-root member
in its hypothesis. This follows the strict linter's requested form.

## Implicit instance assumptions

The explicit headers are unchanged. The following unused section instances
are omitted from the elaborated theorem types:

- `zero_source_accepted`: Symbol, EdgeKey, and Node equality instances;
- `zero_source_native_empty`: Symbol and Node equality instances;
- `zero_source_no_native_member`: Symbol and Node equality instances.

The latter two still require the EdgeKey equality instance for the actual build.
The pure source acceptance equation does not need native equality instances.
Omitting these unused instances strengthens the auxiliary statements. It does
not weaken the source or initializer claims. The worker theorems retain their
original instances. The private root-shape omission from the previous repair
is unchanged. No linter is disabled and no fake use of an instance is added.

Root's failing log is:

`../20261114-prefix-zero-and-filter-repair-check/SourceSynthesisCurrentZeroDepthProductivity.txt`.

The full target and audit boundaries remain in:

`../20261114-current-zero-depth-productivity-audit-draft/NOTES.md`.

The original full positive-depth finite joint-assignment target remains open.
This packet adds no counterexample and no model or nonemission provider.
No compiler, live module, Git action, board action, or Haskell change was made.
No Haskell fix was established.
