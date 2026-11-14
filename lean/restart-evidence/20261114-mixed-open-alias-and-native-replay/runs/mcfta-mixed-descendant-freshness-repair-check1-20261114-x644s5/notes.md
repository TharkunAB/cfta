[2026-11-14 15:47 CET] UNCOMPILED one-line proof repair of mixed-descendant freshness check1. No proof credit is claimed.

The full exact terminal log and instrumented input are preserved under inputs, together with original df217. The instrumented source is exactly df217 followed by Root's four axiom reports. The candidate has no instrumentation.

The eleven diagnostics all stem from introduction of the three target let binders as later/laterValid/continuation. In the actual context, later was the target universeValue (a Value), laterValid was the entered allocation pair, and continuation was the target initial Machine. The subsequent arguments therefore shifted by three places. Declaring local let expressions with the same spelling does not consume the target's let binders.

The repair inserts dsimp only immediately before the existing introductions. This reduces the goal's let binders before intro names the actual later machine, validity, Extension, operand, availability, closedness, numeric identity, identity equation and strict height. No target or premise changes.

All four public theorem headers and three private headers are byte-for-byte unchanged. All declarations before mixed_entry_strict_descendant_fresh are byte-for-byte unchanged, including the first two public helpers that printed standard axioms. The full same-source wrapper declaration and proof are byte-for-byte unchanged. The original generated-type closure and remaining descendant headers remain preserved and OPEN.

Only source/header/SHA comparisons ran. No Lean compiler, Lake, Nix, heavy job, live write, Git operation, board action, or child agent ran. Full descendant closure and reset remain unclaimed. Root owns all validation and publication.
