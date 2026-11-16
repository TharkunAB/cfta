# Quantified branch repair

Status: UNCOMPILED. The failed candidate and full diagnostic remain unchanged.

The expand and full-depth headers and probes are byte-identical. The proof
ceiling and original opacity context are unchanged.

The remaining diagnostic has two subgoals at one tactic site. After splitting
the actual preparation result into `none` and `some folded`, the existing
`branch` premise has the required history for every actual emitted output.
`simp_all only` uses that premise and rewrites the desired history to `True`.
It leaves `forall output, membership -> True` in both cases because its empty
simp set does not reduce those quantifiers.

The only edit finishes those remaining quantified tautologies with
`fun _ _ => True.intro`. The original history premise and all actual membership
conditions remain in the checked derivation. No target, premise, emitted list,
cap, linter, or runtime budget changes.
