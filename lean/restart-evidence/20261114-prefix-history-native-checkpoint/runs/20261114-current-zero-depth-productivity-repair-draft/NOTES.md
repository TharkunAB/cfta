# Proof repairs for the accepted-source zero-depth audit

Prepared: 2026-11-14 21:08 CET.
Status: UNCOMPILED CANDIDATE.

This packet repairs the four errors in Root's strict check of the original
`09e528017738dfab12639fd96d184bcf52d8e825eddc5d00f7e52965041fec28` module.
The original module and original audit packet remain unchanged.

The five public theorem headers are byte-identical. The concrete library,
query, expression, source build, startup, identity narrowing, no-stop policy,
metadata, order, work fuel, recursive depth, and emitted-list scope are unchanged.
No premise is added and no nonemission provider is supplied.

The proof changes are:

- Omit the two unused section instances on the private root-shape lemma.
  Its EdgeKey instance remains in scope. Public instance headers are unchanged.
- Rewrite the actual source construction through its empty argument list,
  the checked empty-selection resolution law, and the zero terms equation.
  The source acceptance proof no longer relies on definitional reduction of
  the recursive source algorithms.
- Rewrite the pure depth evaluator and its shape operations. The empty
  candidate child erases the filter edge, independently of the goal's shape.
  The native empty-root proof still uses the existing actual-build theorem.
- Introduce a hypothetical empty-root member and unfold the guarded meaning
  equation to obtain False.

Root's original log is:

`../20261114-entry-origin-publication-and-context-check/SourceSynthesisCurrentZeroDepthProductivity.txt`.

The original target and interpretation boundaries are recorded in:

`../20261114-current-zero-depth-productivity-audit-draft/NOTES.md`.

This is still a candidate for a filtered accepted-source path. It does not
establish the full positive-depth joint-completion theorem. It does not produce
an emitted accepted-source counterexample. The original complete finite-witness
target remains unchanged and open.

No compiler, live module, Git, board, or Haskell change was made.
No Haskell fix was established.
