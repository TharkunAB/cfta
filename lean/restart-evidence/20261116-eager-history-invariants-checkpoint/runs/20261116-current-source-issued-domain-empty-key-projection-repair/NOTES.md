# Empty-domain projection repair

Status: UNCOMPILED. Root owns validation.

The first candidate failed strict checking at three final return sites. Its raw source and diagnostic log remain unchanged. The failed module has no proof credit.

This repair adds `IntersectionEmptyDomain.emptyDomain` to the three existing final `simpa only` calls for the handle equality, actual entry step and actual suffix. This reduces the literal empty-domain key projection to the original literal emptyKey. All other source bytes are unchanged.

The complete public header and appendable probes are byte-identical. No premise, trace count, continuation, endpoint or supplied budget changed. No compiler was run for this repair.

Original candidate: 20261116-current-source-issued-domain-enter-origin-draft.
Diagnostic: 20261116-full-none-domain-origin-eager-parked-check/issued-domain-origin.txt.
