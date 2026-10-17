# Independent joint inventory query review

Reviewed on 2026-10-17 at 05:28 CEST. No material defect was found. This review covers the final `SourceCurrentConstrainedCapCheckedJointInventoryQuery` and `SourceCurrentConstrainedCapCheckedJointInventoryCold` sources. The manifest records their exact hashes.

`InventoryQuery.Receipt` (lines 31–52) extends the same actual covered query receipt. It retains the physical trace, full returned checked state, equality operation growth, contextual meaning, closedness, scoped cache, and idle tables. Its added fields refer to that same value and state. They retain the joint context, both conditional memo laws, origins of every allocated cell, cap, occurrence bound, original syntax, and probe exclusion. `Receipt.inventoryAt` (lines 55–60) derives the returned inventory from these fields.

`of_receipt` (lines 63–116) is a verification adapter. Its supplied physical receipt is explicit. It applies joint trace induction and origin trace induction to the same trace. It derives input support from original closed resident operands. It derives `Original` from the actual closed available output. It does not assume an output cap, output classifier, or new cell law.

`generated_complete` (lines 119–161) constructs its own return. It expands the inventory at the exact current heap. The new roots are the old roots followed by the literal left and right operands. Semantic admission and joint laws both rebase before execution. Joint rebasing uses captured request origins and successful old payload reads. It does not infer old facts from a vacuous conditional law. `nextContext` changes the source history to reflexive history at this same heap. It retains the existing semantic and causal guard heaps. The native tables and equality operations remain in the input checked state. Closed available operands derive their own `Original` witnesses. Entry counters derive reached word checks before the finite query is constructed.

`InventoryCold.cold_complete` (lines 25–63) constructs the initial covered receipt and then applies `of_receipt`. Empty native tables derive the initial joint stores and origins. Its caller supplies no receipt, completed trace, word-range plan, final context, or result law.

## Imported checks

Five public declaration pairs passed with explicit full signatures and axiom reports. Two integration pairs passed under `-Dlinter.all=true`. The final logs contain no errors, warnings, or `sorryAx`. All reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

`cold_result_fed` constructs the first cold receipt from initial inputs. It then passes the actual first result as the next left operand and the original right root as the next right operand. The first receipt derives the next availability, closedness, cap, semantic readiness, physical validity, context, joint stores, origins, scoped cache, idle tables, and `At`. Only node, edge, and domain counters remain as a causal condition after the first return. The second receipt retains the exact full checked state, literal interpreter return, cap, stores, origins, inventory, and language. Its roots are exactly `[left, right, first, right]`. The kernel derives that its language equals the original left/right intersection.

`mixed_mu_bad_cap_result_fed` specializes the same construction to a literal Mu and a nullary ordinary cap with a nonplain guard. It derives both initial caps and both `Original` witnesses. It proves that the ordinary operand is not hereditary. It supplies no completed query or returned-value law. This fixture assumes initial physical residency and an annotated Mu body. It is not a separate build-from-empty syntax test.

Kernel attempt 1 passed for the general result-fed theorem. Attempts 2 and 3 preserve namespace errors in the added mixed fixture. Attempt 4 passed for both final kernels. The failed snapshots and logs remain in this directory.

## Scope

The cap family permits finite constrained ordinary/union prefixes over hereditary Mu bodies. It does not admit arbitrary constrained Mu bodies. Each next query still requires its own explicit entry counters. The kernels do not derive those next counters from the first entry reservation. These theorems concern the actual checked native query. They do not prove whole outer selected-reduction completion or whole-library Haskell correspondence.
