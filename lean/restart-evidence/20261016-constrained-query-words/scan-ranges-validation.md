# Finite ordinary Scan-only range validation

Date: 2026-10-16 17:55 CEST.

The source has 108 lines and SHA-256 `0904a85b1bcdcbcf2b88abb1e7cd7aacb430918100f3c8f42f0db4d82ff1f5e5`. Direct attempt 2 passed without warnings. Root canonical validation passed 1499 jobs with only the historical dependency warning.

All five public theorem signatures and axiom reports pass in `scan-ranges-checks-1.log`. Both substantive integration signatures and axiom reports pass in `scan-ranges-kernels-1.log`. Final direct and probe logs have no error, warning, or `sorryAx`. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the axiom reports.

`scan_ranges` derives the EXISTING ClassScanCompletion.Ranges. Its only physical inputs are initial heap coherence and Values. Its structural input is finite ordinary Children. It has arbitrary class lists and gate predicates. It requires no global memo validity, proper path, closedness, positive machine width, completed Scan, or supplied range plan. Every actual primary false trace has the same heap. Each primary true antecedent contradicts the metadata theorem. Secondary, seeded, and conjunction obligations are therefore unreachable.

`local_ranges` derives exactly LocalReductionActual.Ranges across the literal operation-only precheck, without an operation-validity or successful precheck premise. `resident_ranges` uses SemanticReady and a resident domain edge to derive its child availability and the exact PartialEdgeActual.Ranges. `edge_body_checks` derives the existing Checks on an actual body. `edge_call_checks` derives Checks for an actual completed call from initial Context, inherited readiness, edge residency, and domain. It transfers the full captured owner through the actual begin protocol. It adds no desired body law or result domain.

The first integration invokes existing ClassScanCompletion.finite with internally derived ranges and then derives exact selected-all, no rejection, unchanged checked state and fourth memo. The preexisting finite API's proper-path and initial fourth Correct inputs remain explicit in that integration. The second integration consumes supplied strict parent-body reads, derives Checks internally, and derives full Post, result residency, all three causal certificates, EdgeNarrow, and EdgeLaw at the same actual return. It has no range premise.

This component removes Scan-only checks. It does not prove LocalReduction.Ranges or ParentWorkerActual.ResidentRanges, since those also contain class-target and leaf query checks. It does not assert new finite graph existence from the supplied-read adapters. The source module and its comments keep this distinction explicit. No older source, Haskell, Audit, Git state, or restart authority was changed.
