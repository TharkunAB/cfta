# Indexed first ordinary cut: independent mathematical review

Reviewed 2026-10-20 16:25 CEST. Result: no material issue found in candidate SHA256 `98e3f0059871cf60a9fa68b976c1975a7cf4a791e612d351740de020d7aa1deb`.

This review covers all three public heads: Cut, Cut.facts, and split. It reads the complete proof and the actual leaves, Value.free, and RowAt definitions. It runs no Lean or runtime check and changes no candidate, repository, or existing evidence file. The candidate remains a next-checkpoint prototype.

## Exact statement and cases

`split` at candidate lines 84–88 consumes the exact lookup `(leaves value)[index]? = some leaf` and a structural `RowAt leaf row`. It returns `RowAt value row` or a Cut with the same value, initial index, and leaf. It does not assume the desired source ancestry or a cut witness.

The closed case at lines 92–99 respects the observer's first test. `leaves value` is exactly `[value]`. A successful lookup forces index zero and leaf equal to value. The given RowAt then supplies the direct arm. A closed ordinary value, union, or Mu is not traversed to manufacture a child cut. This matches `InternedStoredSubstitution.leaves` at lines 24–30.

The open reference case at lines 102–110 has only its literal reference leaf at index zero. RowAt has no reference constructor. That case is impossible; an out-of-range lookup is also impossible. Empty is already excluded by its empty free list.

The open ordinary case at lines 111–125 uses two exact indexed flatten decompositions. It retains a complete selected parentRow, the actual row index, an ordered child index and value, and the remaining leaf index. The offset sums the leaves of earlier rows, the leaves of earlier children, and the inner index. Cut.node at lines 53–60 retains the open-root premise and both exact lookups. Empty prefixes and repeated equal values cause no problem. No findIdx, encoder slot, canonicalization, equality-based choice, or uniqueness premise occurs.

The open union case at lines 126–142 selects an actual member of the stored value's member list. It retains that member's exact index and prefix leaf count. If the recursive result is direct RowAt, the union constructor lifts it. Otherwise Cut.union retains the member lookup, the exact offset, and the nested cut. The recursion decreases structural size of the selected stored member. It does not assume that a leaf of a normalized union belongs to an original source expression's member leaves.

The open Mu case at lines 143–154 uses the exact definition `leaves Mu = leaves body` under the nonempty Mu free-name premise. It passes the same leaf index to its actual stored body. Direct RowAt and a nested Cut lift through the Mu constructor. The recursive measure is the structural size of the body; it does not use cached depth or an execution result. A Mu whose own-name removal makes it closed takes the earlier closed shortcut instead. No unfold execution, heap change, or binder substitution is claimed.

## Facts and index discipline

Cut.facts at lines 75–81 derives `RowAt value parentRow`, the exact lookup `parentRow.children[childIndex]? = some child`, and the exact inner leaf lookup. The same complete EdgeValue is retained, including all symbol, guard, and ordered child fields. Union and Mu prefixes lift RowAt without changing that row or the child data.

The parentRow selected by a Cut need not equal the row inside the selected leaf from the split premise. They describe different structural positions. The theorem keeps that distinction. Facts does not claim observational Origin, execution lineage, a current physical row, a unique first-cut witness, or a unique repeated-leaf occurrence. The constructor witnesses retain each row/member occurrence index even though Facts exposes only the resulting RowAt and child lookups.

The private flat_lookup proof preserves exact occurrence offsets. In its right-append case the index subtraction is justified by the first segment's length bound. The induction retains the exact selected list position. The many_flat and edges_flat lemmas match the mutually defined ordered concatenations.

## Remaining source handoff

This is correct pure geometry of the actual stored value. It needs no heap or Context because it uses the same free-name fields and traversal as leaves. It does not prove those fields correct for an independently specified semantic model.

A union Cut follows actual stored members, not the original outputs of a historical source build. The checked closed-inner-union counterexample therefore remains relevant: outer normalization can expose a whole Mu leaf that occurs in neither original member's leaf list. This candidate neither assumes nor proves that false law. Actual source calls still need their separate producer and selected historical writer receipts at Mu boundaries. Closed-root stopping remains a separate source-handoff case.

The inspected owner selection records strict cut-direct-3 and full cut-public-1 for the three public heads. It records four wrapper invocations, three actual Lean jobs, one pre-Lean bus failure, one elaboration failure, zero canonical jobs, and zero constructed pairs. This independent review adds zero jobs and zero proof pairs. It does not repeat the owner's builds or modify their 30-pin component.
