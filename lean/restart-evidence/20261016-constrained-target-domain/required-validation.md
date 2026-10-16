# Finite ordinary required-path validation

Validated at 2026-10-16 16:42 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryRequired.lean`.
Source SHA-256: `68e1fc31db1a0a2bb7874162078182d9b58b92f67a79b75569036db595a55a31`. The module has 298 lines.

## Result

The canonical focused build passed with 765 jobs and terminal exit 0.
`required-build-1.log` contains only the historical unused `inputs` dependency warning.
The final direct check passed with terminal exit 0 and no diagnostics in `required-direct-3.log`.

All seven public declarations have an axiom report and a full signature check.
They comprise two relation definitions and five theorems: `head`, `node`, `children`, `rows`, and `requireAll_done`.
`required-public-1.log` passed with no errors, warnings, or `sorryAx`.

All five integration theorems have axiom reports and signature checks.
`required-kernels-3.log` passed with no errors, warnings, or `sorryAx`.
The earlier failed attempts remain in this evidence directory.

## Integration checks

1. `rejected_zero_arity` constructs the actual rejected-row graph for a required missing child. It has no child call or constructor allocation.
2. `retained_negative_key` constructs a retained zero-arity row with the literal negative-key rule. It runs actual edge and node constructors. The guard type and guard value remain unrestricted.
3. `rejected_parent_empty` constructs rejection of the only row and actual node reconstruction. The returned value is Empty at the original heap, with a strictly smaller constructor height.
4. `selected_then_unselected` constructs the selected first position and unselected second position. The ordered relation keeps both positions.
5. `serial_requireAll` uses two literal successful requireAll calls. It threads only derived intermediate SemanticReady, availability, and domain facts. It composes positional height bounds and proves the final length equals the original length.

## Contract review

The mutual induction follows the actual RequireNode, RequireChildren, and RequireRows graphs.
A domain input cannot enter their recursive-head case.
Physical effects use current constructor readback and current resident records.
The Head theorem inverts the actual bounded exposure result on Empty or an ordinary node.
The requireAll wrapper uses the actual graph/execution equivalence at the supplied literal successful return.
It does not use the old closed-input completion endpoint.

`NodeNarrow` and `EdgeNarrow` express structural domain and height bounds.
They do not express semantic language containment.
Children return a positional `Language.All₂ NodeNarrow` relation.
Rows can disappear, so their relation pairs outputs with an ordered sublist of original rows.
Node reconstruction can filter or canonicalize rows; no literal row-order equality is asserted for its output.

Every public effect theorem takes an actual completed graph or literal successful execution and initial SemanticReady plus resident available domain inputs.
No closedness, CostHeap, future invariants, child-result law, completion callback, or whole-forest language premise is supplied.
Guards and equality classes have no restriction.
This module proves structural preservation for completed graphs. It does not prove general completion, native lazy scheduling, Haskell runtime correspondence, or outer reduction termination.

## Commands

Direct checks use the pinned executable `/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean`.
`LEAN_PATH` is `/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean`.
The public and integration checks import the canonical final olean.
No Lake, Git, Haskell, Audit, older proof, or older evidence file was changed by this task.
The parent ran the canonical build.
