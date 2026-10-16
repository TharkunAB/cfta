# Independent admission and generated-query validation

Date: 2026-10-16 07:47 CEST.

The pinned direct Lean check passed with exit status 0. The final log has no warnings, errors, or `sorryAx`. No canonical Lake build ran. The root reported canonical CoveredQuery build 1139 and full Audit 2320/56321 separately.

Command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-admission-history/covered-query-independent-probes.lean
```

| Module | Public theorem axiom reports | Full public signatures | Integration kernels |
| --- | ---: | ---: | ---: |
| AdmissionExecution | 4 | 6 | 2 |
| AdmissionCode | 4 | 5 | 2 |
| AdmissionTrace | 3 | 5 | 1 |
| CoveredQuery | 3 | 4 | 3 |
| Total | 14 | 20 | 8 |

All eight named kernels also have axiom reports and complete signatures. Thus the final log contains 22 axiom reports and 28 signatures. Every reported axiom set is a subset of `propext`, `Classical.choice`, and `Quot.sound`.

## Kernel checks

1. `execution_all_outcomes` derives both weaker cache invariants for the actual finite interpreter outcome. Generic execution retains its explicit current-publication checks.
2. `execution_done_full_state` identifies coverage at the exact complete returned checked state.
3. `node_admission_before_publication` derives the current publication check from the source request certificate. It requires no completed request.
4. `ordered_node_requests` composes ordered request certificates from local scope and input coverage. It requires no completed calls or result language law.
5. `concrete_trace_admission` instantiates the generic trace theorem with the actual node and edge branch certificates. It derives final Covered, Admitted, and SeenAdmitted from the actual physical trace.
6. `fixed_query_exact_and_covered` invokes `query_complete`. It derives actual checked done, available closed output, exact physical intersection language, and all three final admission properties. It supplies no future request coverage, desired output law, or completed child callback.
7. `generated_inventory_retained` invokes `generated_complete`. It retains the exact current-heap availability and closedness witnesses for `roots ++ [left, right]`, the literal computed finite input model, the actual receipt, and final all-cell coverage.
8. `two_generated_queries` invokes `generated_complete` twice. The second request uses the first actual output and the original right operand at the exact first returned checked state. The first receipt supplies Good, Contextual, Covered, Scoped, SemanticReady, Idle, heap growth, allocation history, output availability and closedness. It also retains the earlier right operand. The second model is the literal finite inventory at that first returned heap with roots extended by the first output. The only additional call premise is the second request's reached WordRanges. The second actual return has a closed resident result, all-cell coverage and both weaker invariants, and language exactly equal to the initial left/right intersection. The semantic composition uses idempotence of intersection, proved directly from the two receipt equivalences.

## Explicit scope

The initial source Facts, original finite inventory, warm Contextual and Covered caches, syntactic Scoped cache, Good checked state, SemanticReady, Idle, source growth/history, closed resident operands, and reached WordRanges remain explicit. Generated inventory validity and contextual transport are derived. No second contextual or admission oracle is supplied. The check does not claim GHC execution, machine overflow beyond WordRanges, solver IO correctness, or a completed current class Scan semantic composition.

Only new evidence files were written. All four proof sources remained unchanged. Source copies and hashes are retained with the probes. Early probe logs retain local elaboration failures and automatic recovery placeholders. Those came from evidence-local variable-capturing notation. The final probes replace that notation with explicit terms and print axioms for every named integration kernel. The final evidence does not rely on exit status alone.
