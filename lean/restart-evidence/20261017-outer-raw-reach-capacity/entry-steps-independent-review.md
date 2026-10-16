# Independent review of full raw entry admission

No material defect was found in the final OuterResourceEntryDefs, OuterResourceEntrySteps, or OuterResourceEntryReach sources.
The reviewed Steps SHA-256 is `aa081197a351dcc26ba6f8854d893086c78b415b35ae9315a7cfe2742f44188c`.
The reviewed Reach SHA-256 is `f398a03c6042dc87ae90b16269ba8e1aab2dee6d9edafd341ee3c64d3b1f35d6`.
The exact reviewed-source manifest is adjacent to this note.

## Quantifier domain

The proof uses the preserved `OuterEntries.Step` at lines 36–74 and the preserved `Reach` at lines 77–81.
It does not define a new restricted reach relation or select one successful execution trace.
The raw Step constructors still quantify over arbitrary supplied completed earlier EdgeCall, Descendants, or NodeCall graphs.
No earlier strict Reads, semantic output law, or completed enclosing call is an input to the new step theorem.

PrefixResources independently constructs an admissible prefix from current initial facts and headroom.
PrefixUnique then identifies the supplied raw graph's output and complete returned caller state.
Proof irrelevance transfers the constructed strict Reads to that exact supplied graph.
This transfer includes the checked native state, equality operations, fourth memo, merge memo, and both outer tables.
It does not equate independently chosen logical memo schedules without an equality proof.
The produced Reads carry their own exact logical memo endpoints.

## All ten literal Step cases

| Case and final Steps line | Checked obligation |
| --- | --- |
| node_evaluate, 39 | The actual captured owner has the same resident value as the candidate. Publication keeps the checked state and headroom. The active bound changes from nodeRank to nodeRank minus one through node_push. |
| node_ordinary, 57 | Current linked residency gives actual input rows. Height decreases by one. The original row count reserves all row budgets while leaving the final raw node request outside the entered row control. Every row rank lies below the retained active cap. |
| edge_evaluate, 78 | The exact captured owner receives the same profile, guards, inherited readiness, and supply. EdgeBody needs no outer active exclusion because Parent does not call the outer recursion. |
| rows_edge, 92 | The head original row uses only its parent budget. It inherits the current original row profile and a safe active bound. The suffix is not executed or assumed complete. |
| rows_descendants, 104 | The arbitrary earlier parent graph receives exact strict Reads and Work through PrefixResources. Its produced universal certificate supplies parentRows, max arity 1, and parentGuards for the actual returned edge. Its height narrows. The entry reserves child traversal and retains the active cap. |
| rows_tail, 135 | Parent Work is charged first, then actual returned-edge descendant Work. Remaining headroom pays for the original suffix. The suffix keeps its original profiles and guards; it does not use the earlier output envelope as its input envelope. Both completed-prefix reverse frames retain the active cap. |
| descendants_children, 181 | The actual inherited-first prefix supplies payload readiness and Context. Its equality allocation keeps the constructor heap. The entered children are the supplied returned edge's literal children. Child headroom is bounded by that edge's arity, with the final raw edge request omitted from the entered child control. |
| children_live, 205 | The literal live case starts index zero with unchanged inputs, profiles, state, supply, and active cap. |
| walk_node, 206 | The actual indexed descent supplies the head request's inherited value and current Context. It keeps the heap and all causal stores. The head uses its original profile, guards, height, and reserved node budget. |
| walk_tail, 222 | The arbitrary earlier head graph starts after the actual indexed descent. PrefixResources derives its same-state Reads, Post, stores, and Work. The remaining original child suffix retains its original combined payload, profiles, and guards. Reverse frames restore the active cap at the exact returned state. |

Rows descendant rank bounds use the actual EdgeNarrow height inequality.
The explicit projection simplification at lines 132 and 159 makes that existing inequality available to arithmetic automation.
It adds no new hypothesis or structural restriction.
Equality payload size does not enter the outer structural rank. Changed inherited payloads remain legitimate because rank depends on the resident input value.

The Admitted predicate contains only current Context, causal stores, current input facts, current profiles, remaining headroom, and active-owner exclusion.
It contains no completed graph, future result, future Reads, or entry Plan.
Existential current profile parameters remain coupled to that entry's actual input and remaining supply.

## Reach and returned original Plan

EntryReach.reach at line 22 follows the original reflexive transitive closure, including every raw completed-prefix choice.
The induction generalizes the initial admission before it handles transitivity.
EntryReach.numeric_plan at line 32 derives ParentCapacity for each original reached EdgeBody entry.
EntryReach.ranges at line 40 derives the older universal machine-range Plan for the same original Reach domain.
Its endpoint uses the admitted current Context and resident edge at that exact reached state.

The new EntryRoot finite adapter calls the preserved conditional quantitative root with the derived original NumericPlan.
The prefix resources used to derive that Plan come from the earlier direct resource recursion, not from this Plan-dependent adapter.
The source dependency and proof dependency therefore do not assume their own desired Plan.
The constructed and prepared adapters retain the same original finite-ordinary syntax domain and compute their initial envelopes from the actual original constructor result.
They return the original universal NumericPlan as a conclusion.
They do not claim general Mu completion, Haskell cache initialization, host allocation order, instruction complexity, or whole-library correspondence.

## Independent integration

`entry-steps-independent-review-kernels.lean` imports canonical EntryReach and the preserved older OuterRoot.
The final strict run is `entry-steps-independent-review-kernels-2.log`, terminal exit 0.
It has four axiom/full-signature pairs: one result definition and three integration theorems.
All linters and explicit proof/universe/deep-term settings are enabled with one million print steps.
The final log contains no warnings, errors, sorryAx, omitted terms, or truncation.
Only the existing standard propext, Classical.choice, and Quot.sound dependencies appear.

1. constructed_source_full_raw_plans starts from source syntax, actual field history, initial cache validity, and computed initial headroom. It derives initial admission, the original universal NumericPlan, the older universal machine-range Plan, and admission for every original raw reached entry.
2. prepared_source_full_raw_plans constructs the actual field preparation receipt before it derives those same universal conclusions. It takes no loaded-field result or caller Plan.
3. old_root_from_initial_resources invokes the preserved older Plan-based root theorem with only the newly derived Plan. Constructor outcome uniqueness covers every value and heap in the older root's constructor-indexed range premise. The same returned graph retains strict Reads, full Post, quantitative stores, universal certificate, full language equality, exact Work, and final fitting supplies.

The first integration draft failed only to unfold initialNodes/initialEdges in the final supply arithmetic. Its exact source and log remain preserved.
No production source was edited during this review.
