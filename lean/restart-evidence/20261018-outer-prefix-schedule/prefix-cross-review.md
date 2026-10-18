# Independent outer prefix and lower-fuel review

No material issue was found in the final frozen Prefix and Fuel modules. This review adds no Lean declaration, build, or public pair. It reuses 22 existing public signature/proof/axiom pairs. The review reads the actual `ExecutionAncestry.Step` and `Reached` definitions, the completed-call adapter, and the physical and semantic entry invariants.

## Initial inputs and exact prefix scope

`OuterInitialPrefix.reached` takes the initial Context, Frame, numeric Fits, flat carrier, phase Inputs, one Room at the initial phase forecast, and the actual literal Reached witness. It produces the current seed and a SeedTrace for that same witness. It also produces the composed caller Post, current Frame/Fits/carrier/Inputs, remaining forecast inclusion in the initial forecast, current Room, global initial-envelope bounds, and a lower-fuel inequality. No future semantic invariant, result law, capacity callback, compiled Reads graph, or completed whole call is an input.

The operational Reached witness contains exact successful earlier-call equations. It is an observation of a finite prefix, not an oracle for an unfinished call. The separate existing busy-execution producer can construct that witness from an actual busy failure. The new theorem does not construct arbitrary desired prefixes.

Reached describes outer phase entries. It does not describe intermediate native instructions within a failed Parent call or arbitrary `Outcome.state` values. All-outcome physical growth does not imply the semantic Post used here. Completed earlier summaries obtain their missing semantic graphs and receipts from the frozen `OuterInitialActual` adapters.

## Eight actual step cases

| Step | Actual entry transport | Exact next seed |
| --- | --- | --- |
| node_evaluate | `CallSteps.node_start` derives the captured owner's ready input, inherited value, and semantic Context; checked state, Merge, and fourth stay exact | same seed |
| body_rows | Available ordinary node and linked resident records derive its literal original rows | same seed |
| rows_edge | `OuterEdgeGuardAlphabet.edge_call` aligns the observed Parent edge return, including the complete caller and returned inventory | Parent(seed) |
| rows_tail | The edge adapter and `InitialActual.descendants` supply two actual Posts before the untouched original suffix | descendants(fuel,Parent(seed)) |
| descendants_children | Initial resident field and inherited readiness construct the actual inherited receipt; exact run equality identifies its combined payload | same seed |
| children_walk | Live combined value selects its literal indexed walk | same seed |
| walk_head | `InheritedNumeric.descent` derives the actual current indexed request and unchanged physical profile | same seed |
| walk_tail | Actual descent followed by `InitialActual.node_call` supplies the exact completed first child before the suffix | node(fuel,seed) |

The original row suffix retains the original inherited value. The child suffix retains the original combined value, next index, and original remaining values. Both use the composed Post's constraint growth and physical Keeps. Neither substitutes the just-descended child payload or returned child list for the original suffix.

The evaluating node branch uses the captured original request. Unchanged checked-state projections alone do not provide semantic Sound for the new node status. The proof correctly obtains that Sound from `node_start` and constructs `Post.rebase` with it.

## Initial Room and exact schedule

The prefix invariant retains a current seed and bounds its remaining forecast by the source remaining forecast. A single initial final Room therefore supplies current Room by `Room.mono`. In the row cases, `rows_ge` first exposes the descendant forecast and `descendants_ge` exposes Parent's forecast. `parent_reserved` then supplies every exact finite own-record/count/ambient-word reservation. Suffix steps use the exact predicted previous output seed. No guard-alphabet or numeric-profile monotonicity of the schedule is assumed.

Merely retaining Fits at the initial global output profile would be insufficient: reforecasting another Parent from that already padded profile would require a larger Room. The implemented current-seed and remaining-forecast invariant avoids this mistake. `reached` derives the global output Fits/carrier only after it has derived the current facts.

## Pure lower-fuel ceiling

`OuterInitialFuel` has seven recurrences plus the six-tag phase projection. At a row successor, the maximum covers Parent at the original seed, descendants at the predicted Parent return, and the original suffix at the predicted descendant return. At a walk successor, the maximum covers the node at the current seed and the suffix at its predicted node return. An ordinary body uses predecessor-fuel rows. Descendants and children reserve their same-fuel child walk. Raw constructors, inherited operations, and terminal zero-fuel bodies add no lower-worker fuel.

The five component inequalities and two split equivalences use these exact seeds. The Prefix module's private `step_need` follows each actual Step. Its SeedTrace induction gives the remaining phase ceiling below the original ceiling. It does not infer scalar monotonicity from resource growth. The pure arithmetic theorems do not assert worker success or absence of lower faults.

## Remaining proof map and limits

A concrete next consumer can use the reached row seed, its Room and semantic Frame, and the reached fuel inequality. `rows_parent_le` places the current Parent common fuel below the original phase ceiling. `parent_reserved` supplies its initial uniform reservations. `ParentUniformGuardAlphabet.complete` then constructs that Parent and all nine independently larger lower-fuel runs. This is a local producer path; it does not by itself classify every failed outer outcome.

Semantic Context permits evaluating NodeGood cells. Its returned-result law is conditional on a returned status. Thus this new transport can coexist with an active same-key ancestor. The existing `ExecutionAncestry.initial` producer identifies such an ancestor from a busy observation; it does not exclude the collision. The new modules prove no all-owner key exclusion, bound on fresh recursive requests, general outer completion, convergence, or Haskell runtime correspondence. These remain separate obligations.

## Selected evidence

Prefix source SHA 79a2f220f9e3525c581a001b12b14887f8e0139be4af3b48905ce4645a34b399. Selected `outer-prefix-direct-6` is terminal zero with a zero-byte log. `outer-prefix-canonical-1` completes 1863 jobs. `outer-prefix-public-1` prints all seven public declarations in full.

Fuel source SHA c247db14852765ff82d939de6ba6dfa3d00e6722dd33e4cc5383e1a9de199bf8. Selected `outer-fuel-direct-3` is terminal zero with a zero-byte log. `outer-fuel-canonical-1` and `outer-fuel-public-1` terminate successfully. The latter prints all 15 public declarations in full.

Both public groups have all eight explicit options and only permitted standard axioms. The review reuses these receipts and does not run Lean. Canonical dependency replay warnings are separate from the selected zero-byte own-source strict logs. Failed earlier attempts remain immutable in the component owners' packages.
