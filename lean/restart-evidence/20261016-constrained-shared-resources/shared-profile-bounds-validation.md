# Shared target profile bounds validation

Date: 2026-10-16 20:58 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinarySharedProfileBounds.lean`.
The frozen source has 108 lines. Its SHA256 is `1fb04f7c2813171e1d0bc7eaabf3d153cfa7d5f4bc1b2a0846693a5e691ea9c8`.
The source snapshot is byte-identical.

## Results

- Direct source check 2: terminal exit 0, no diagnostics.
- Root-owned canonical log `shared-profile-bounds-build-1.log`: 1344 successful jobs. The log includes only the historical unused-input dependency warning. No canonical process was run by this owner.
- Final canonical imported public check 3: terminal exit 0, 8 axiom probes and 8 full signature probes.
- Final canonical imported integration check 2: terminal exit 0, 3 kernels with an axiom probe and a signature probe each.
- Final direct and imported logs contain no errors, warnings, or `sorryAx`. The public axioms use only `propext` and `Quot.sound`. The constructive Target integration also uses `Classical.choice` from its existing execution dependencies.

Direct check 1 found a Boolean filter-conversion proof that needed an explicit equality split. Direct check 2 corrected only that local proof. Public check 1 failed because an isolated temporary namespace lacked its dependency links. Check 2 used the corrected temporary import directory. Final public check 3 and integration check 2 import the canonical module. All draft logs remain in the manifest. No compiled object is stored in the evidence directory.

## API and scope

`target_rows_mono`, `target_nodes_mono`, and `target_edges_mono` compare the whole Target wrappers by full operand-path count. Count zero uses the actual empty-target zero row and zero request bounds. Positive counts translate to the existing additional-operand recurrence by subtracting the seed.

`operand_paths_length` derives exact length `paths.length - 1` from distinct paths and selected membership. `record_operand_paths_length` derives distinctness from the coherent record's canonical class field. `operand_paths_depth` proves that filtering and signed path conversion preserve each original path-length bound. It does not assume a runtime index conversion or input execution.

`record_target_bounds` uses an original class length bound `m` to bound all selected targets at the common whole-Target operand count `m - 1`. It also returns signed operand-path depth bounds. `record_profile` widens a separately derived actual target profile to the same common bound. It is a profile consequence, not a target producer or result-law assumption in the numeric bounds.

## Integration

1. Three distinct original paths with the middle path selected produce the first and last signed paths in original order. The exact operand count is two and both depths are one.
2. A singleton class produces no operand paths. Its whole Target row, node-request, and edge-request bounds are zero. No active-class assumption is added to this pure boundary check.
3. A coherent original record, resident captured forest, legitimate warm cache certificates, original profile/height/depth limits, and initial headroom at `m - 1` construct the selected Target. The kernel returns the same actual graph, stable literal execution, strict reads, full receipt, all three structural stores, uniform profile, and final supplies. It supplies no intermediate profile, count, future readiness, or completed Target.

The module does not prove whole class cumulative capacity, host forcing order, signed machine overflow, or complete constrained recursion. No older source, Haskell, Audit, root document, or earlier evidence was edited. This owner ran no Git or Lake command. New text has one final newline and no blank line at EOF.
