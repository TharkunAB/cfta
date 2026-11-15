# Child span count rewrite repair

Status: UNCOMPILED. This repair has no proof credit.

The original candidate failed the private strict check.
The log is retained at:
20261115-native-node-child-span-before-finish-check/SourceCurrentAllocatedNativeNodeChildBeforeFinish.txt
The failed original packet stays unchanged.

The only source change replaces the unsupported convert tactic.
The proof derives remaining + 1 - 1 = remaining with omega.
It rewrites the goal with that equality and applies the actual tail.
No input, conclusion, supplied budget or observed state changes.
The complete public header and appendable probes are byte-identical.
No imports occur in PROBES.lean.txt.

The proof still has no global C/M or full finite-witness claim.
The parent owns compilation and publication.
