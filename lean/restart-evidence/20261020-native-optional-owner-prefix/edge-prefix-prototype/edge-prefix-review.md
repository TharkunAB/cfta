# Checked edge-body optional prefix review

Reviewed on 2026-10-20 at 19:15 CEST.

The sole public theorem `edge_body` starts from the actual unbound checked edge-body Trace. It derives equal original arities, both exact field loads, the actual ready allocation result, and the exact first yielded state. It retains the selected original zipped child index and the completed Walk over the earlier children. The returned prefix Trace starts at the original edge-body control. The unbound selected child Trace ends at the same optional instruction and checked state. The continuation equation retains the remaining children and the actual allocated makeEdge continuation.

The proof excludes failed loads, blocked steps, rejected allocations, sentinel completion, and completed makeEdge work by their literal step behavior. It uses no Good, Fields, conjunction law, completed owner return, or desired cut premise. It does not identify the checked edge body with the older compileEdge code. It does not establish compiler-owner or original source ancestry.

The final source SHA256 is `a84874824f40f740695c05f77f69a1581b5b1213421a879c7a0f82526c6a768b`. The selected strict check has an empty raw log. The selected full printer checks one statement, its complete proof, and its axioms with all eight output settings. Four capped Lean attempts are retained. The first two attempts failed during elaboration. No canonical build or constructed case is counted in this package. The parent owns the official build.
