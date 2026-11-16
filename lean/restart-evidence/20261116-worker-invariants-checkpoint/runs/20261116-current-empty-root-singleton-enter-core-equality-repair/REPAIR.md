# Final core equality repair

UNCOMPILED. The preceding owner-qualified candidate failed strict Root check 39549 only at its final use of congrArg₂, which is unavailable in this environment. Preserve that raw source and the exact log at 20261116-cps-rendering-ancestry-none-candidates-check/domain-ancestry.txt.

Replace only that final expression. First use core congrArg to replace the free field in the two-field DomainKey constructor. Then rewrite its seen field. The resulting constructor is definitionally emptyKey. All actual source-control, physical-cache, trace and singleton-key reasoning is byte-identical to the preceding candidate.

The complete public header and appendable probes are unchanged. No assumption, import, auxiliary theorem, proof ceiling or algorithm budget changes. No proof credit before Root's strict check.
