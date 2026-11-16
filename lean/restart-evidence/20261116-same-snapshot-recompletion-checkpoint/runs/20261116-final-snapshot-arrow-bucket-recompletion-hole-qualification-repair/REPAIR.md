# HasHole owner qualification repair

Status: UNCOMPILED. The original failed raw, header, and diagnostic remain intact.

The only code change qualifies the intended header constant as
`EnumerationDependencies.HasHole`. Its authoritative declaration is
`lean/MicroCFTA/EnumerationDependencies.lean:18`, inside namespace
`MicroCFTA.EnumerationDependencies`. EnumerationReferences imports and opens that
namespace. It does not own this inductive predicate.

This is the same predicate used by the existing recomplete_with_base_on header,
whose preamble opens EnumerationDependencies. All semantic binders, budgets,
conclusions, and proof text remain unchanged. The repaired header is frozen with
its explicit namespace resolution. The old unresolved header had no proof credit.
Probes are byte-identical. No cap, linter, runtime, or Source file changed.
