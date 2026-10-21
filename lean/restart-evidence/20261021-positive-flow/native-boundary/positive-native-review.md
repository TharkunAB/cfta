# Positive positions through actual Merge and native calls

Written 2026-10-21 02:17 CEST. Source review and one checked counterexample.

## Checked result

`PositiveNativeSupportKernels.actual_opaque_mu_counterexample` has no premises.
It constructs the actual source family below. Top is the literal constraint
`⟨some [], .top⟩`. A is `⟨some [[[0],[1]]], .top⟩`.

```
leaf = node leaf_Top[]
left = binder false (node pair_Top[leaf,leaf])
right = binder false (node pair_A[leaf,leaf])
program = node roots_Top[left,right]
```

The theorem retains the actual closed build, the exact initial native machine
with empty node and edge result tables, allocated initial `Good`, and available
distinct inputs. Both actual inputs are full Mu values whose stored bodies are
closed. The raw false binders do retain those unused Mu values. Neither input
has `PositiveAt` at any child-index path. Actual `execute 64` returns an ordinary
result. The result's row zero has a nonplain full constraint and gives
`PositiveAt result []`. `NativeKeyAdmission.node_done` derives a physical Trace
for that same call and same returned result. There is no supplied execution,
cache winner, or desired origin premise.

This is a counterexample to unrestricted native same-position positive support.
The query exposes the two stored bodies. Its ordinary body result has no free
pair placeholder, so optional construction returns the ordinary result. This is
not an implementation defect. The theorem does not concern class selection,
Parent copying, an outer return, or the Haskell implementation. The source is a
new raw-binder variant of the earlier ordinary pair/Top versus pair/A fixture.
It is not a rerun of that earlier theorem.

The final source is `positive-native-kernels.lean`. The sole public constructed
head has the same complete type as its private checked witness. Selected strict
and full-printer receipts are named in `positive-native-selection.json`.
Every failed source and log remains unchanged. The three earlier strict runs
failed elaboration; they did not refute the source calculation.

## Validation and limits

The selected strict log is empty. The selected full public readback prints the
complete statement and alias proof. Its axiom report has only propext,
Classical.choice, and Quot.sound. Five owned Lean commands are retained: three
failed elaboration attempts, one selected strict check, and one full public
check. There are no owned canonical jobs and no runtime/Haskell jobs. Every
command has fresh usage and verified 4 GiB max/high, zero swap, five-minute
limits. Each command retains its exact source, log, receipt and limits.

`positive-native-support-plan.md` records the source-only Merge/native contracts
and the warm unused-body positional boundary. Those proposed producers are not
proved here. Source snapshots and live hashes pin every named foundation. This
component changes no official module or frozen evidence.
