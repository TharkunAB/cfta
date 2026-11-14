[2026-11-14 16:14 CET] UNCOMPILED strict-lint repair of native-step check1. No new proof credit is claimed.

Root's exact instrumented input and complete log are preserved under inputs. The input is original7a743 followed only by the two public axiom reports. The candidate omits instrumentation and preserves original7a743 in its earlier frozen packet and as a local input copy.

The only change moves variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] below lookup_resources, node_reference_branch, and union_reference_branch. Those three pure lookup/control helpers need neither instance. Both execution helpers still have the same instances in scope. No proof body changed.

All seven written declaration headers are byte-for-byte unchanged. Both public headers are exact. From private node_reference_steps through the end of the module, the entire source is byte-for-byte unchanged. No premise, conclusion, fuel offset, callback, result provider, source initialization, or operational definition changed. The whole module had failed strict check1 solely on these three unusedSectionVars diagnostics; its two standard axiom reports did not give it proof credit.

The ordinary and union branch distinction remains exact. Ordinary Q/refU uses lookup/reset; refU/Q adds sorting. Union Q/refU walks before reference lookup; refU/Q adds sorting. Full type/descendant closure and original-root finite-witness closure remain OPEN.

Only header/source/SHA comparisons ran. No Lean compiler, Lake, Nix, heavy job, live write, Git operation, board action, or child agent ran. Root owns all checks and publication.
