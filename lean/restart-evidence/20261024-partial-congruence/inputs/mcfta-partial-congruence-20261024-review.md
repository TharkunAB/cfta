# Partial-observation congruence candidate review

Author self-review, 2026-10-24 02:28 CEST. No compiler or candidate program was run. No repository file was changed. This is not an independent proof review.

Candidate: `/tmp/mcfta-partial-congruence-20261024-candidate.lean`, 124 ordinary lines, SHA `a80cab1534295394ebdd70773139a0bacfa378b973082f8c24aba1b0816abd70`.

The module imports the installed `EnumerationPartialObservation`. It uses the distinct local instance name `partialCongruenceMonadList`. It introduces one private helper, `partialChildren_agree`, and one public theorem, `expandPartial_agrees`.

The public theorem uses one graph and one supplied fragment on both sides. It takes independent left and right fuel bounds, a complete input `Frame`, totality of the left forest, and the two actual successful renders. It returns equality of the partial terms and the complete frame between the actual final states. There is no safety, finished-state, semantic acceptance, readable-slot, completion, or desired-observer premise. The right success is the observation compared by this paired theorem; no additional right execution is assumed or constructed.

The main induction generalizes the second bound, fragment, all four states, and both observed terms. Its lower-fuel IH therefore covers the enumerated stored fragment and every child, with arbitrary related intermediate states. Either zero-bound success contradicts `success_failure`.

The private helper fixes the two lower bounds and consumes that paired IH. Its list induction generalizes both initial states, both final states, and both term lists. It compares each actual child read before it compares the actual tail. `expandPartial_frame` derives left intermediate totality. It preserves list order and multiplicity. Pure list reconstruction preserves the paired final frame.

The node branch compares the actual child traversals and then reconstructs the same concrete symbol. The hole branch uses `getValue_agrees` on the two actual reads, so both continuations inspect the same complete stored value. Only the enumerated-value branch invokes the lower-fuel IH. The other branches return the same literal partial term. Truncation occurs only for a recursive graph view with empty suspended constraints. Other pending and eliminated values retain the original queried hole ID, without renaming it to its representative.

Every final-state relation remains the full installed `Frame`. The proof does not replace it with class equivalence, root equality, or a field projection. The public statement makes no literal forest equality, same-bound transport, error equality, or unconditional termination claim. One-sided transport remains a separate task.

The 123-line initial draft is preserved as `/tmp/mcfta-partial-congruence-20261024-draft-v1.lean`. During source review, the helper induction was corrected to generalize both final states, and the tail IH call was given its two actual tail-final states. This was an uncompiled draft correction, not a failed proof job. No theorem statement changed.

Exact installed dependencies read in full:

- `lean/MicroCFTA/EnumerationPartialObservation.lean`, SHA `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc`: actual frame preservation and successful fuel extension.
- `lean/MicroCFTA/EnumerationObservations.lean`, SHA `ebc891e8461c7b545d55f6823322789f19635e2d1c58a5551307b621079ba0ab`: exact paired value-read interface and primitive transports.

Additional exact source cuts checked: `EnumerationState.lean:335–354` for all partial-render branches; `EnumerationSchedule.lean:1062–1081` for the ordered `mapM` shape; `EnumerationCompressionFrame.lean:69–87` for read-frame totality; and `EnumerationCorrectness` bind/pure success decomposition. The candidate was read in full after the draft correction. Kernel elaboration and an independent review remain pending.
