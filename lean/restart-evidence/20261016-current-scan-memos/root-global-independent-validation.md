# Independent current global-memo caller validation

Date: 2026-10-16 08:19 CEST.

The root reported canonical GREEN1330 for the three caller modules. This independent check used the completed canonical dependencies and direct pinned Lean. It passed on the first attempt with exit status 0. The log has no warnings, errors, or `sorryAx`. No source edit or canonical Lake build ran.

Command:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean lean/restart-evidence/20261016-current-scan-memos/root-global-independent-probes.lean
```

| Module | Public theorem axiom reports | Full public signatures |
| --- | ---: | ---: |
| SourceCurrentConjunctionQueryGlobalMemos | 1 | 2 |
| SourceCurrentConjunctionClassScanGlobalMemos | 2 | 3 |
| SourceCurrentConjunctionAllocatedGlobalMemos | 1 | 1 |
| Total | 4 | 6 |

The signatures also cover QueryReads and ScanReads. Three named integration kernels have their own axiom reports and full signatures. Thus the log contains seven axiom reports and nine signatures. All reported axiom sets are subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## Integration kernels

`stop_before_suffix` derives the actual primary gate's global tables, then invokes the current secondary/checked seeded/current conjunction Call endpoint. It records a stopped Scan for any arbitrary unvisited suffix. It requires only the current class's proper paths and seeded ranges. It has no suffix range plan, suffix completion, or suffix read receipt premise. The final global Valid and physical Ready refer to the same returned physical heap and checked state.

`verified_stop` consumes one actual warm current Scan and its legitimate initial At, physical Ready, values, proper/nontrivial original classes, fourth Correct, reached ranges, and global Valid. It derives global ScanReads and final At for that same actual output and full checked state. A stop contradicts any accepted original forest that satisfies all original classes. The proof derives rejected class membership from the actual Scan and uses the independently derived stopped-class law.

`constructed_empty_fourth` invokes the complete allocated entry endpoint. Actual allocation History, initial cache validity, literal source build, source guard coverage, and resident edge derive the loaded same-cache constraint and entry state. A ready inherited constraint, actual live precheck result, and reached range plan construct the current finite Scan. Native tables are cold at the literal prefixState. The equality operation state is the actual precheck return. The three global tables may be warm, subject to their initial Valid proof. The fourth memo is literal empty, and its initial Correct is derived inside the kernel. The result retains the same actual Scan, exact global receipts, final Valid, final concrete inventory At, final fourth correctness, and sound rejection of actual original output classes.

## Explicit boundary

The kernels do not supply a future Scan, future query law, final global Valid, completed native request callback, or final inventory oracle to the constructed endpoint. The generic verified kernel takes an actual completed Scan because it validates that graph's receipts; the constructed kernel derives the Scan itself.

History/build completion, resident edge, initial global table Valid, inherited field Ready, actual live precheck output, and reached range plans remain explicit entry assumptions. This evidence does not establish later required-path edits, the complete outer equality caller, lazy GHC evaluation order, pending memo publication, runtime hash maps, or solver IO semantics. The guard agent reviews source semantics independently.

## Frozen sources

- `SourceCurrentConjunctionQueryGlobalMemos` (101 lines): `e124565938300a8ea80d61f97180e0cf9096902325b912563b7604336b67e277`.
- `SourceCurrentConjunctionClassScanGlobalMemos` (174 lines): `071a30ed39f19fad0b14cbfd2770893349012137600696272f49e735b0210b32`.
- `SourceCurrentConjunctionAllocatedGlobalMemos` (101 lines): `922087479fd30279a7244e97ecacb5896e4fa32331500df48dac74973e6781e3`.
