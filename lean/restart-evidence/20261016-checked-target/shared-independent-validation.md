# Independent Leaf validation

Validated 2026-10-16 09:05 CEST, pinned Lean v4.34.1.

Direct commands against existing canonical dependencies:

```
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/leaf-independent-public.lean
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env lean /home/tritlo/Code/mcfta/lean/restart-evidence/20261016-checked-target/leaf-independent-kernels.lean
```

Both terminal exit0, no warnings or errors. Three public theorem axiom reports and three signature checks passed. Only propext, Classical.choice, and Quot.sound occur. Seven kernel compositions passed: literal hit integration; literal miss integration; finite leaf derived from initial invariants without a supplied Force/Step; actual-leaf verification with narrowing and conditional preservation at the same output/state; unchanged fourth-table correctness; old slots and historical receipts after inventory advance; final global validity/unfolding extension/unchanged query tables.

The review makes no independent claim about parent canonical job counts. Reviewed frozen source copies and exact hashes are included. No compiled proof artifacts are included. Raw log files are retained unchanged.
