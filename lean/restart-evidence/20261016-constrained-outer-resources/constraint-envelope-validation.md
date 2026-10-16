# Constraint envelope validation

Date: 2026-10-16 22:23 CEST.

Production source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope.lean`.
It has 344 lines and frozen SHA256 `95a99ea4f3aeb99442fb1641b5cffb0311c5c2d99769d0da2afc52fe2a261581`.

## Checks

- Direct checks 1, 3, 5 failed. Their exact source snapshots and raw diagnostics remain in this directory. Check 1 exposed proof elaboration issues. Check 3 required a generic list flatten-count helper. Check 5 required the empty descent branch to identify its exact output before it reused the decreased-depth bound.
- Direct checks 2, 4, 6 each reached terminal exit 0. The final source check 6 has no diagnostics. Its source snapshot is byte-identical to the production source.
- Root canonical `constraint-envelope-build-1.log` completed successfully with 1075 jobs. Only the historical unused-input dependency warning remains. This owner ran no Lake process.
- Final canonical imported public check 3 reached terminal exit 0: 17 public axiom probes and 17 full signature probes.
- Final canonical imported integration check 6 reached terminal exit 0: 7 kernel axiom probes and 7 full signature probes.
- Both final standalone sources set `linter.all true`, `pp.explicit true`, `pp.proofs true`, `pp.universes true`, `pp.deepTerms true`, `pp.maxSteps 1000000`, and `pp.fullNames true`.
- Final imported logs have no errors, warnings, `sorryAx`, or omitted-term markers. Reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.
- Root reported full Audit terminal exit 0 with 2624 jobs and 60653 dependency checks. That aggregate is separate from the focused checks.

The first public import and kernel check 4 used the final direct-built temporary olean. Public check 2 and kernel check 5 used the canonical olean. Final public check 3 and kernel check 6 repeat those exact final proofs with the strict standalone options above.

## Integration scope

1. The actual congruence step derives a length-three path from inputs whose maximum length is two.
2. The actual bounded fixed-point normalizer retains that generated path.
3. An input with natural indices above one million receives a normalization envelope without any index range or arity premise.
4. Actual inherited-first physical combination constructs its result, then actual indexed descent derives the decreased-depth envelope.
5. Every live precheck retains the original own occurrence and depth bounds, with no inherited-size bound.
6. Initial operation validity, physical readiness, and initial effective guard bounds derive the allocated precheck path obligation at every actual classes branch.
7. Empty and contradictory payloads retain the literal indexed-descent cases.

Kernel checks 1–3 failed only in the two concrete normalization equations because kernel reduction stopped at the source sort's well-founded implementation. Check 4 proves those equations with `cbv` and introduces no reflection axiom. All failed drafts and logs remain available. No failed check is counted as a passed probe.

## Preserved scope

The module follows the existing natural-index path model. It does not prove signed Haskell path conversion or infer an index range from finite ordinary structure.
The allocated precheck input bounds the initial effective own field. No future parent result, future path envelope, completed enclosing graph, or global fixed key carrier is an input.

No older source, Haskell, Audit, root document, or previous evidence changed. No Git or Lake command was run by this owner. Owned source and text have one final newline and no blank line at EOF. No compiled artifact is stored in this evidence directory.
