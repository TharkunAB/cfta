# Independent reached-entry validation

Validated at 2026-10-16 17:40 CEST.

The new source is `SourceCurrentAllocatedFiniteOrdinaryOuterEntries.lean`.
It has 107 lines. Its SHA256 is `7ee682c86fa6594cc20b3b8eea9457281cb7a3b6cdf987c0314b21a55450b7a7`.

The direct pinned Lean check passed with exit status 0 and no warnings.
The parent canonical log `entries-build-1.log` reports 1519 successful jobs.
Its only warning is the existing unused `inputs` warning in `InternedFreshOrdinaryClosedCompletion.lean`.
The imported public probe passed with exit status 0. It prints all 28 public type, definition, theorem, and constructor axiom/signature pairs.
The imported kernel probe passed with exit status 0. Its four independent examples check these properties:

- An actual node demand enters the first parent checks before that parent completes. No completed current body or child graph is a premise.
- A second row receives the exact complete caller returned by the first actual edge call and its descendants.
- A second indexed node receives the exact earlier node return and the next literal descent operation state.
- Contradictory children have no entered child step.

The final imported probes have no warnings, errors, or `sorryAx` dependency. Their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`Entry` stores inputs and the complete current caller. It has no result or completion field.
`Step` contains completed graphs only for earlier prefixes. `Reach` closes those steps.
`Plan` supplies `ParentWorkerActual.ResidentRanges` at reached edge-body entries. It contains no semantic result, final invariant, or capacity theorem.
`Plan.restrict` transports that same initial plan to a reached control.
`Plan.edge_call_ranges` obtains checks for the actual captured owner after the actual evaluating observation.

The plan remains an explicit machine-check assumption. This component does not prove that an arbitrary fixed word width can accommodate all generated identities. It does not construct recursive completion by itself.

No earlier source or evidence file was changed. No Haskell, Git, or Lake command ran in this validation. The canonical build ran under the parent agent.
