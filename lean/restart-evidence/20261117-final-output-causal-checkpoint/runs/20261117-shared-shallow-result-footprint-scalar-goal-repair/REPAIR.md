# Scalar goal reduction repair

Status: **UNCOMPILED**. The two earlier failed packets and their logs remain unchanged.

The previous repair left five failures at the scalar rewrites. Each concrete goal still contained a generated match with proof arguments that depended on the core being rewritten. This repair adds an explicit `change` before those rewrites. The node branch states its stored bucket as the original `scs`. Each other branch states its stored bucket as `[]`. The resulting scalar goal has no proof-dependent match application.

Only these two scalar-goal changes are new. The remaining proof, full public header, all private helpers, preamble, and probes are byte-exact to the previous repair. No premise, fuel, cap, or linter setting changed. No compiler was run.

Previous raw: c2471dfd6e91ef5093ae160d93003eae556bb67733a617b7c65013ac653d2d51.
Previous log: ../20261117-shared-shallow-result-footprint-value-cases-check/normal-module.txt.
