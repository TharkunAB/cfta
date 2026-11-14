# Cases of the preserved simultaneous A/M header

Status: SOURCE AUDIT, not a proof of exhaustive coverage. This ledger refers to
the exact copied `ORIGINAL-COUPLED-FUEL-HEADER.lean.txt`. A is its closed,
empty-domain conjunct. M is its original mixed-domain conjunct, in both operand
orders and after actual extensions of that original entered machine.

## Existing checked components

| Case or input fact | Existing source component | What it does not supply by itself |
| --- | --- | --- |
| Any call at fuel zero | `Kernel.execute`, `checked_failed` | It proves a checked exhaustion result, not a successful result. |
| Empty operand | `Control.empty_first`; kernel empty branch | The full induction must connect the branch to each exact A/M call. |
| Closed physical self | `Control.self_first`, `self_record` | The full induction must retain closedness and atoms of the selected operand. |
| Actual swap | `Control.swap_first`; kernel swap branch | The caller still applies A or M at the strictly smaller fuel in the reversed order. |
| Closed only-U Mu operand | `SourceSynthesisCurrentUniverseClosedMuClassification`, reported STRICT PASS by Root | Classification is full-record equality. It is not the A/M call proof. |
| Actual ordered union child inputs | `SourceSynthesisCurrentUniverseAtomInductionSteps.union_member_closed_atoms` | This does not supply the recursive M or A result for each child. |
| Actual ordinary child inputs | `SourceSynthesisCurrentUniverseAtomInductionSteps.node_child_closed_atoms` | The open original body needs its separate physical child classification. |
| Ordered union reconstruction | `SourceSynthesisCurrentUniverseAtomInductionSteps.ordered_union_atoms_of_fuel_induction` | Needs the exact lower-fuel child conclusions. Its atom conclusion does not include closedness. |
| Selected closed ordinary A node step | `SourceSynthesisCurrentUniverseNodeAtomInductionSteps.ordinary_closed_nodes_atoms_of_fuel_induction` | This checked declaration is PRIVATE in the inspected source. It needs the exact lower-fuel child conclusions. Its atom conclusion does not include closedness. The public `ordered_node_atoms_of_fuel_induction` remains available for traversal composition. |
| Closing an available only-U returned record after growth | `SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_boundary_atoms_closed_after_growth` | Needs the actual returned availability, only-U atoms, and source-to-returned growth. It supplies no atom induction. |
| M operand is the full original U, with either original open alias | `SourceSynthesisCurrentUniverseAliasAtoms` and `SourceSynthesisUniverseMixedEntryReplay` | Retain the original entry. The full header must assemble both operand orders and closedness from the exact returned U. |
| M ref(U) against a strictly smaller ordinary node | `SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_node_reference_descendant_after_mixed_entry` | Gives the exact reference-read/reset equation to smaller-fuel empty-domain A. The full induction must apply A and handle the low fuel prefixes. |
| M ref(U) against a strictly smaller union | `SourceSynthesisCurrentUniverseReferenceDescendantSteps.current_stored_universe_union_reference_descendant_after_mixed_entry` | Gives the exact ordered union walk in the original domain. It does not reset the whole union call to A. Child M results still need induction and reconstruction. |
| Both operands closed in the original nonempty domain | `SourceSynthesisUniverseClosedResetSteps.execute_closed_nonempty_domain_step` and `closed_reset_atoms_of_fuel_induction` | Empty has priority. Otherwise the actual reset consumes fuel before A. The nonempty-domain fact must be instantiated for the same original entry. |
| M body(U) against an ordinary node: physical inputs | `SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_ordinary_child_requests_after_mixed_extension` | Identifies each body child as original ref(U) or an available closed atomless marker, with actual child freshness. It does not compose the child executions into the whole ordinary-node M result. |

The table omits only the common namespace prefix `MicroCFTA` on the synthesis
declarations. `Kernel` and `Control` mean `SourceRecursiveIntersectionKernel`
and `SourceRecursiveIntersectionControl`. It assigns no credit to a
private draft merely because a similarly named component is public.

## New candidate in this packet

The selected original U/node-or-union A step calls the SAME original entered
M body/operand call at exactly one less fuel. Both direct Mu orientations share
that same domain and cache. The actual optional binder has no effect because
the M result is closed. This candidate remains UNCOMPILED.

## Concrete remaining assembly

1. Validate the new selected Mu step, then derive and use its actual decisions.
   Compose the opposite original operand order through its real swap step.
2. Complete the A constructor/control split. Use the closed-Mu classification,
   selected union/node steps and lower-fuel hypotheses without assuming A on an
   arbitrary nonempty domain. Close every returned only-U value using the same
   source and actual growth.
3. Complete the M open-alias/operand split. Keep every call in the SAME original
   entered domain. Use exact full-U alias results, strict-height freshness, the
   reference equations, and the ordered union walk as appropriate.
   Derive each actual control decision. In particular, exclude an inadmissible
   repeated-pair result using the actual source identities and original seen
   set. A literal RecIntersect placeholder does not have the required only-U
   boundary atom. Empty-domain A has an empty seen set by definition.
4. Compose the M body/ordinary node row and child traversals with the physical
   ref(U)/marker alternatives. Ref(U) children use M or its exact reset equations.
   Closed marker children need the actual nonempty-domain reset before A.
   The separate frozen mixed-body node draft is not credited as checked here.
5. Combine both conjuncts in one fuel induction with the exact endpoints and
   extensions required by the preserved coupled header. Account for failed and
   exhausted calls. Derive the original full atom theorem from that unchanged
   coupled result.

No step in this ledger constructs the final finite joint assignment for emitted
enumeration outputs or establishes compatibility of historical cleared buckets.
Those remain additional parts of the original full formalization objective.
