# Successful Mu request readback

`SourceCurrentNativeRequestWinner.winner` handles the actual generic
`InternedNestedConstruction.request`. A successful request returns cleanup
of a record stored at the request key in the exact final heap. The hit reads
its existing payload. The miss uses `keepFirst_present` after the actual body
callback. It can select an earlier winner instead of its candidate.

The theorem requires only the literal successful request equation. It has no
callback result law, context, cache correctness, cap, or availability premise.
It is an actual-graph verifier. It does not construct initial completion.
It does not compare the winner's body with its ordinary probe.

Final source SHA256: `2e6d9e5e5bb68ed86501e9f995c97befb878eef12f1dc04ec740bd6d3debdac6`.
Strict attempt 3 has an empty log. Canonical attempt 1 passes 145 jobs.
Public attempt 1 checks the one public theorem with all eight explicit
printer/linter options and full proof/axiom output. The only axioms are the
three standard axioms. Effective limits are 4 GiB / 4 GiB / zero swap.
Failed strict attempts 1 and 2 remain preserved with their executed snapshots.
No additional constructed scenario is selected for this small helper.
