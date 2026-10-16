# Current Scan worker completion validation

Final source: `SourceCurrentAllocatedScanWorkerCompletion.lean`, 202 lines.
SHA-256: `9ca08269e8fcbac48db0b83f4f50d3e43eb141bf3551d5a1d4f812403360c3f5`.

The root-managed canonical batch passed with 1297 jobs and exit 0.
`scan-actual-build-1.log` records Completion and WorkerActual. Only the
preexisting unused-input dependency warning remains. This agent ran no Lake
process. The final direct source check passed with exit 0 and no warnings
in `scan-completion-direct-3.log`. Earlier direct logs retain the local
elaboration failures. They are not final validation results.

The final external probes all returned exit 0 with no errors, warnings,
or `sorryAx`:

| Probe | Axiom reports | Full signature checks |
| --- | ---: | ---: |
| Completion public endpoints | 9 | 10, including StableRun |
| Completion integration kernels | 6 | 6 |
| Root Caller and WorkerActual endpoints | 6 | 6 |
| Root semantic integration kernels | 2 | 2 |
| Total | 23 | 24 |

The axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`,
or no axioms. The source and probes retain all raw logs and a frozen source
copy. The manifest records their hashes.

The completion kernels check exact selected occurrence retention, stopped
execution with an arbitrary unproved suffix, duplicate selected classes in
source order, a warm fourth-memo hit with zero lower work, empty Scan with
identical checked state and fourth memo, and nested selected failure tags
with the exact underlying observation.

The root kernels derive two semantic integrations from supplied literal
success and legitimate initial facts. A stopped result names an original
class and refutes it for every accepted original forest. A completed Scan
can feed a next generated native query. That query derives its own next
inventory, admission, closed result, and exact physical intersection law.
Only reached next-query WordRanges and the closed resident operands are
additional query inputs. No next model or cache-law oracle is supplied.

`scan_complete` requires only the finite actual current Scan graph. It uses
actual lower gate completion, actual checked Seeded completion, and the
current conjunction Call completion. The graph supplies the reached calls;
there is no supplied future callback, final readiness, or semantic result
law. The conjunction budget stays fixed. Five independent stage bounds are
combined by maxima, including the projection/read bounds shared between
seeded queries and conjunction calls. The result equality retains selected
classes, all checked fields, and the entire fourth memo.

This direction does not establish graph existence for arbitrary input.
Root WorkerActual constructs the graph under its explicit initial domain
and reached ranges. Concrete host global tables, lazy demand/publication,
and general outer caller termination remain separate. No Haskell source,
older Lean proof, Audit, or restart authority was edited by this agent.
