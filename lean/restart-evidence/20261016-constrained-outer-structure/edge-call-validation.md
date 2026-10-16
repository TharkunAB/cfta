# Constrained outer edge-call validation

Date: 2026-10-16 17:37 CEST.

The frozen source is `SourceCurrentAllocatedFiniteOrdinaryOuterEdgeCall.lean`.
Its SHA-256 is `75a4d8ce88e3cced1570ebb4841dc99e9de94aa801622be2e9da9e091876e80e`.
The module has 169 lines. The final direct check is `edge-call-direct-3.log`.
The root canonical build passed 1518 jobs. The source did not change after that build.

`edge-call-checks-1.log` checks both public declarations: the `Ranges` definition and the `finite` theorem. Each has a full signature and an axiom report.
`edge-call-kernels-6.log` checks two integration theorems. Each has a full signature and an axiom report. These final logs contain no error, warning, or `sorryAx`. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the axiom reports. Earlier failed attempts remain as evidence.

The first integration constructs an actual finite call from the initial Context, inherited readiness, edge residency, domain, three causal certificates, active-owner bound, and reached live checks. It then derives an immediate repeat at all ten zero bounds. The repeat returns the exact same edge and complete caller state. The theorem also restores the ancestor active bound and derives a strict child rank against the original requested edge. It has no second range or completion premise.

The second integration derives the entire reached range plan from raw contradiction and the actual captured-owner value equality. It constructs the call and its zero-bound repeat without any machine range premise. Initial domain and caller invariants remain explicit; this is an outer-call theorem, not the more general raw parent rejection theorem.

The implementation constructs `Parent.finite` on live evaluation and `Parent.rejected_finite` on raw rejection. Strict reads derive the full body Post. The exact evaluating cell survives the parent advancement. Its derived bound is installed at the same handle. A warm hit uses the first stored owner's certificate. No callback supplies parent success, semantic laws, or a result domain.

The range plan quantifies only the actual begin-evaluate owner and running state. Its result is the existing live-only `ResidentRanges`, whose final obligations are machine range checks. It does not quantify a future Context, body graph, result law, or completed query.

The theorem does not construct outer node, row, or descendant recursion. It does not remove the reached machine-range plan. It does not establish GHC thunk demand, CAF identity, concurrent publication, or the complete library runtime transfer. No older source, Haskell, Audit, Git state, or restart authority was edited for this component.
