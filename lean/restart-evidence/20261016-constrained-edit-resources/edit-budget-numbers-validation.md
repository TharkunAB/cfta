# Fixed edit budget numbers validation

Date: 2026-10-16 21:19 CEST.

Source: `lean/MicroCFTA/SourceCurrentAllocatedFiniteOrdinaryEditBudgetNumbers.lean`.
The frozen source has 212 lines and SHA256 `57793744017181baa9c4b5ca927d166b3cc98d7cd7c28fd0c83085f33409c9bd`.
The source snapshot is byte-identical.

## Checks

- Direct source check 1 passed with no diagnostics.
- Direct source check 2 passed after adding the two actual-slot cost comparison helpers. No proof correction was needed in production.
- Root-owned canonical log `edit-numbers-build-1.log` records 1356 successful jobs. Only the historical unused-input dependency warning remains. This owner ran no canonical process.
- Final canonical imported public check 2: terminal exit 0, 26 public axiom probes and 26 full signature probes.
- Final canonical imported integration check 3: terminal exit 0, 3 kernels with an axiom and signature probe each.
- Final direct and imported logs contain no errors, warnings, or `sorryAx`. The reported axioms are subsets of `propext` and `Quot.sound`.

Public check 1 and integration check 2 used the exact direct source through a temporary import directory. Integration check 1 needed a definitional equality proof for a concrete literal count; check 2 passed after replacing the unnecessary arithmetic tactic with reflexivity. The production source did not change. Final checks import the canonical module. Earlier raw logs remain intact.

## Fixed captured and current envelopes

The captured data are the original record and uniform limits Rc, Ac, Cc, D, Hc. Let T be SharedForceResources.targetRows for that fixed record and captured forest. Current input limits are Ri, Ai, Hi.

`outputRows` is `max T Ri * max T Ri`. The proof includes Ri = 0 and derives Ri at most this output row limit. `outputArity` is `max (max (max Ac 1) Ai) 1`, so every original current arity fits. These envelopes remain fixed for the complete edit.

`leafNodes` and `leafEdges` charge the complete whole-Target budget at original class size minus one, plus SharedLeafResources.queryBudget at the captured and current limits. Every position permits a first miss, even if the slot will actually be reused. The two slot comparison lemmas prove that any actual hit or miss budget fits these fixed coefficients. The three monotonicity lemmas permit smaller current row, arity, and height limits under the same fixed captured limits. No returned output profile feeds a later coefficient.

## Literal input sums

The six sums `nodeNodes`, `nodeEdges`, `childrenNodes`, `childrenEdges`, `rowsNodes`, and `rowsEdges` multiply original literal value positions by the corresponding leaf coefficient, then add original ordinary constructor occurrences. They count repeated source positions rather than distinct identities.

Empty pays one leaf and no ordinary reconstruction. An ordinary node pays a root leaf, its rows, and one node reconstruction. A child cons adds its head and suffix costs. A row cons adds its child forest and suffix; its edge sum also adds one edge reconstruction. The nil forest and row costs are zero.

`node_profile`, `children_profile`, and `forest_profile` combine ValuePositions and OccurrenceBounds. They derive input-only sum bounds from original row, arity, height, and forest-length limits. They require no execution, current result, child callback, future profile, or capacity plan.

## Integration

1. An ordinary node with two repeated rows, each containing two Empty children, has five leaf positions, one node occurrence, and two edge occurrences. Its exact sums are `5 * leafN + 1` and `5 * leafE + 2`. Shared record identities do not remove occurrences.
2. An actual slot-sensitive leaf cost at smaller current descendant limits fits the fixed whole-edit leaf coefficients. This comparison holds for any slot state and path and uses no runtime or completion assumption.
3. Two copies of the same ordinary node have original profile R = 2, A = 2 and height at most 1. The original profile and length alone give forest bounds `10 * leafN + 2` and `10 * leafE + 4` before any edit executes.

These are pure cost and profile-envelope laws. The separately owned direct edit construction must connect them to its actual Work traces and derive word checks from cumulative initial headroom. Host demand, equality allocation counts, whole outer completion, and machine overflow are outside this component.

No older source, Haskell, Audit, root document, or earlier evidence was edited. This owner ran no Git or Lake command. New owned source and text have one final newline and no blank line at EOF. No compiled object is stored in this evidence directory.
