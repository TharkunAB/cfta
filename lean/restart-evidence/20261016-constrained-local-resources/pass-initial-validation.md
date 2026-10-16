# Initial pass capacity validation

Date: 2026-10-16 21:47 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.lean`.
The frozen source has 155 lines and SHA256 `ca616760d852cfc8c2b2b8021abc0af2395576c024bea9702b3ad045237f94c1`.
The frozen and direct-source evidence copies are byte-identical.

## Checks

- Direct source check 1: terminal exit 0, owned process 85457. No diagnostics. No production correction was needed.
- Root canonical `local-pass-initial-build-1.log` built this module successfully at job 1578 of 1579. The aggregate failed only in the separately owned LocalResources target. The log retains that failure. Root confirmed this module's canonical success. Only the historical dependency warning applies to this module.
- Final canonical imported public check 3: terminal exit 0, 4 public axiom probes and 4 full explicit signature probes.
- Final canonical imported integration check 3: terminal exit 0, 3 kernel axiom probes and 3 kernel signature probes.
- Final logs contain no error, warning, or `sorryAx`. Reported axioms are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

Public check 1 used an unsupported formatting option, `pp.width`. Kernel check 1 began before the temporary import file was copied and failed at import. Public check 2 removed that formatting option. Kernel check 2 ran after the temporary import was ready. Both passed. Check 3 imported the final canonical object. No production source changed during these checks. All raw logs and the first public probe source remain in the manifest.

## Initial-only capacity construction

`complete` uses the same initial arguments as PassResources.fold_complete. Initial hypotheses include physical and semantic readiness, the current inventory, global validity, all three native and Merge certificates, the uniform original forest profile, original record/path facts, and cumulative node and edge headroom. No completed current pass, future result profile, or numeric capacity plan is an initial hypothesis.

The proof first derives the shorter tail's universal capacity predicate by induction. For each actual earlier tail admitted by the existing PassCapacity head condition, PassResources.fold_complete independently constructs that shorter tail from initial facts. `fold_unique` compares literal stable worker returns and identifies the exact forest, full checked state, and Merge memo. The derived tail receipt supplies its computed inventory, physical and semantic facts, and global bundle. Its returned profile and supply bounds derive the current head class's remaining headroom. ClassInitialCapacity.complete then supplies that head's existing capacity plan.

The list retains order and multiplicity. No distinct-record or distinct-path assumption is used. The proof does not select a result from a completed enclosing pass.

`ranges` derives the existing class-pass range predicate from that universal capacity plan. `finite` constructs the existing actual Pass, strict PassReads, and full receipt with its computed inventory. It retains native and Merge structural certificates and ordered NodeNarrow. The stronger output-profile and constructor-request conclusions remain available from the separate PassResources producer.

## Integration kernels

1. Any raw empty tail returns the same forest, entire checked state, and Merge memo. This uses no physical premise or chosen bound.
2. Any raw earlier tail under initial cumulative headroom receives the head ClassCapacity at its exact returned forest and state. The kernel does not assume a current head or full-pass completion.
3. Initial headroom derives the old ranges and a constructed full pass receipt. The same output carries its computed inventory, global validity, native certificate, Merge certificate, and ordered narrowing.

This module discharges the pass capacity predicate from initial cumulative pass headroom. It does not derive whole outer headroom, equality-operation instruction costs, general recursive progress, host forcing, or whole-library Haskell correspondence.

No older source, Haskell, Audit, root document, or previous evidence changed. This owner ran no Git or Lake command. Owned source and text have one final newline and no blank line at EOF. No compiled artifact is stored in this evidence directory.
