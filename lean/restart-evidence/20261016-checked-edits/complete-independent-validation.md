# Independent finite edit probes

Date: 2026-10-16 09:30 CEST.

The direct pinned Lean command in `complete-independent-checks.json` passed
with exit code 0. It ran no canonical Lake build. The final raw output is
`complete-independent-probes-final.log`.

The probe checks all three public completion theorem signatures and all
three public axiom dependencies. It adds five named kernel compositions:

1. `selected_leaf` derives finite selected execution from the actual leaf
   range plan and initial invariants.
2. `ordinary_child_open_sibling` constructs ordered child reads for a
   selected ordinary child beside an unchanged open sibling. It requires
   closedness only of the selected input.
3. `recursive_head_globals` constructs head completion and its global reads,
   then invokes public node completion at the literal returned heap. Its
   output retains the exact intermediate global bundle.
4. `list_root_no_native_ranges` invokes the public finite list endpoint for
   an ignored root callback. It supplies no native request range plan.
5. `two_selected_inventories` invokes completion twice. The second invocation
   uses the inventory, state, memo bundle, and resident-input transport
   computed by the first invocation. It constructs the complete ordered
   child read receipt.

All five named kernel theorems also passed axiom inspection. All eight
inspected declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. The final log contains no warning, error, or `sorryAx`.

The frozen Complete, Graph, and Ranges source hashes match the parent
checkpoint. The existing parent `graph-public-3.log` already checks the
public arity theorem and three graph integration kernels. Those checks
were not repeated here. No production source changed during these probes.
