# Raw guard envelope validation

Date: 2026-10-16 22:39 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.lean`.
The frozen source has 350 lines and SHA256 `945c0e2635f6f465958ee121a8e77c9953d13e6a3b8f36b16fc39af96f068b26`.

## Initial metrics and closed producer

`Limits` separates stored path occurrences S, stored depth D, raw guard stages G, and exposed Same depth P.
`Bounds limits constraint` refers only to those initial raw constraint fields.
No bound on a future normalized result is an input.

`stages Top` is zero.
A non-And atom has one stage, including a residual atom that positive extraction rejects.
An And list has the sum of its child stages plus one stage for every list element.
`SamePaths P guard` bounds only Same atoms exposed by outer conjunction flattening.
It does not inspect paths hidden under a residual constructor.
The actual positive accessor does not extract those paths either.

Let C(S,D) be the frozen ConstraintEnvelope normalized occurrence bound, and L(S,D) its expanded depth bound.
The staged positive budget starts at (2,P).
At each next stage it maps (S,D) to (C(S+S,D), L(S+S,D)).
`positive_bounds` follows the SAME actual `positiveNormalized` and `positiveNormalizedList` branches.
Each distinct Same uses the literal normalizer.
Each successful list fold combines the actual earlier normalized operands.
A failed syntax branch retains its None result.
The proof does not replace the staged accessor with one flattened normalization.

For two initial vectors, `conjoinLimits` derives:

- Stored occurrences: C(S1+S2, max D1 D2).
- Stored depth: L(S1+S2, max D1 D2).
- Guard stages: 2*(G1+G2).
- Exposed Same depth: max P1 P2.

`merge_stages` proves its factor directly from the retained original outer atoms.
Top contributes no atom because the literal merge removes it.
Every retained atom has one stage.
Sorting and duplicate removal cannot increase its occurrence count.
No transitivity or totality assumption on the supplied comparator is needed for this quantitative statement.
`merge_paths` derives path bounds from the same retained atom membership.

`effectiveBudget` combines the derived stored bound with the derived staged positive bound.
`effective` follows the actual `sourceEqualities` branches, including residual syntax, positive contradiction, and the exact empty-positive fast path.
Its inflated bound also covers branches that retain the original stored field.

`conjoin_complete` constructs the actual allocated conjunction from initial operation Valid, both stored Ready facts, and both initial vectors.
It returns the literal result and operation state, Valid, Ready, Grows, cached original readback, the next raw vector, and the effective-own bound.
It calls existing `ConjoinAllocation.conjoin_correct` and identifies that SAME returned stored field.
It does not assume an actual conjoin result, normalization success, desired result bound, future capacity, or completed enclosing graph.

## Exact source anchors

- Haskell `Constraint.hs:129–136`: effective equalities use the actual positive guard accessor and its empty shortcut.
- Haskell `Constraint.hs:171–176`: positive Same normalizes, and And uses the literal right fold with intermediate normalization.
- Haskell `Constraint.hs:215–222`: raw constraint conjunction combines stored equality fields and raw guards separately.
- Haskell `Constraint.hs:310–316`: guard conjunction flattens only outer And, removes Top and duplicates, and orders the retained atom set.
- `SourceCompactGuards.lean:430–443`: actual staged positive accessor and list fold.
- `SourceCompactGuards.lean:488–492`: actual effective-field branches.
- `GuardConjunction.lean:257–258,293–316`: literal merge, atom-count bound, and exact retained membership.
- `SourceEqualityConjoinAllocation.lean:60–64,75–98`: raw allocated operation and constructive exact readback.
- The new source exports the pure vector closure at line283, effective bound at line292, and allocated producer at line320.

These source statements use the preserved natural-index model.
Haskell `Index.hs:41` and `Path.hs:37–39` use signed Int child indices.
This module does not establish that conversion, negative-index behavior, or whole-library Haskell correspondence.
It adds no arity or index-magnitude assumption and reports no Haskell defect.

## Validation results

- Direct source checks 1 and 2 failed. All source snapshots and raw logs remain available. The first check exposed namespace alias, reduction, and induction elaboration issues. The second check left three local proof elaboration issues.
- Direct source check 3 reached terminal exit 0 with no diagnostics.
- Direct source check 4 reached terminal exit 0 with `linter.all=true`, but reported seven missing-doc warnings on new structure fields.
- The final source adds only those seven field docstrings. Strict direct check 5 reached terminal exit 0 with no diagnostics. Its source snapshot is byte-identical to the production source.
- Root canonical `guard-envelope-build-1.log` completed successfully with 1076 jobs. Only the historical unused-input dependency warning remains. This owner ran no Lake process.
- Final canonical imported public check 2 reached terminal exit 0: 16 public axiom probes and 16 complete signature probes.
- Final canonical imported integration check 3 reached terminal exit 0: 6 kernel axiom probes and 6 complete signature probes.
- Both standalone sources set `linter.all true`, `pp.explicit true`, `pp.proofs true`, `pp.universes true`, `pp.deepTerms true`, `pp.maxSteps 1000000`, and `pp.fullNames true`.
- Final source/imported logs contain no warning, error, `sorryAx`, or omitted-term marker. Reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## Integration checks

1. Actual Top/Top guard merge has zero stages.
2. A zero-stage Top beside Same satisfies the proved raw-merge stage bound.
3. A residual Not guard may contain arbitrarily long hidden Same paths without extracting positive equalities.
4. Nested And syntax with large natural indices constructs its actual staged normalized output and derives the six-stage bound. No normalization-success premise is supplied.
5. Two literal raw conjunctions run in sequence. The second uses the first returned operation state, stored value, Ready, and derived vector. The third original operand's Ready is transported through the actual first growth receipt.
6. The actual conjunction return derives the allocated precheck path obligation. The inherited Ready fact grows to the literal returned operation state. The frozen ConstraintEnvelope precheck theorem then uses the derived effective-own envelope. There is no future path-bound or completed-precheck premise.

Kernel draft 1 failed in concrete reduction, ambiguous Path names, and reflexive-inequality elaboration. Draft 2 passed against the final direct-built temporary olean. Public draft 1 also passed there. The final public and kernel checks repeat those same proofs against the canonical olean. Failed checks are not counted as passes.

## Remaining scope

The vector transformer is conservative and may grow quickly.
It bounds class/path data, not equality-interner allocations, normalization instructions, or wall-clock work.
The component closes one actual raw conjunction and composes repeated raw conjunctions.
It does not yet propagate these vectors through every native producer, Merge result, warm outer memo, raw rebuild, and whole recursive caller history.
The remaining whole-root capacity reservation, general recursive progress, signed-path conversion, and host forcing obligations remain separate.

No older source, Haskell, Audit, root document, or previous evidence changed. This owner ran no Git or Lake command. Final owned text has one final newline and no blank line at EOF. No compiled artifact is stored in the evidence directory.
