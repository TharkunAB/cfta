# Memo-aware shared targets and class passes

Source main is `0696b48d`. The source merge is `f780009a`.
This checkpoint retains every earlier proof and the optimized interned core.
The new modules follow the completed merge requests from the previous checkpoint.
They do not identify the new executions with the older uncached edit graphs.

## Captured targets

`SourceCurrentMemoSharedTargetState.State` contains the full native state,
the returned target slots, and the actual completed merge table.
Each class starts fresh target slots over its captured forest.
The merge table passes between classes.

A stored target receipt contains its actual earlier target execution.
It retains the initial physical premises and selected path domains.
It also retains heap growth and extension of the returned merge table.
Current cache coverage therefore restricts to the historical initial table.
The target language follows from that actual history.
No future language or cache invariant is supplied.

`SourceCurrentMemoSharedTargetForce.Force` has two source branches.
A hit returns the stored value and the same complete shared state.
A miss executes the new demanded target and stores its actual result.
Finite physical completion uses the selected original path domains and a
finite actual-prefix range plan. It needs no language coverage premise.
Language coverage remains a separate warm-table invariant.

`SourceCurrentMemoSharedTargetLeaf.Leaf` forces the target before its native
intersection. The intersection uses the exact returned state and target.
It retains the completed merge table and all stored target slots.
Actual leaves derive physical effects, input-language inclusion, and retention
of accepted subterms that satisfy the captured original class.
The separate leaf receipt records force reads before native instruction reads.

## Simultaneous edits and class order

`SourceCurrentMemoSharedEditGraph` follows the signed edit trie.
Selected children execute in order. Unselected children remain unchanged.
Rows retain their original symbol and full guard.
Constructor and recursive head calls advance the heap without resetting
the merge table or returned target slots.

The domain proofs derive physical readiness, stored costs, stored merge
records, result availability, and transport of every tracked path domain.
The retention proofs preserve exact target values and completed entries.
They also preserve actual producer histories.
The cache and language proofs use the actual intermediate edit states.
They derive each reached cache invariant from the original one.
Unselected siblings can remain open.

`SourceCurrentMemoClassPass` executes the actual class right fold.
Each head captures the forest and merge table returned by its tail.
Fresh class slots do not reset that table.
Literal empty propagation follows the complete fold once.

The language theorem proves two independent bounds.
Every output term belongs to the input language.
Every input term that satisfies all retained original classes survives.
This is conditional exactness. Narrowing need not enforce the classes.
The exact caller must still check its original constraints.

## Combined finite endpoint

`SourceCurrentMemoClassPassComplete.source_cold` fixes the current plain/Top
merge guards. It starts with an empty completed merge table.
The physical heap and three global tables can already contain valid entries.
One returned `Pass` supplies all of these facts:

- Finite modeled execution under its actual-prefix range plan.
- Final native readiness, stored costs, and available result records.
- Valid stored merge records and retained physical entries.
- Preservation of every tracked selected path domain.
- Independent merge cache coverage and actual producer histories.
- The independent input/output language bounds.
- Its ordered `PassReads` and coherent final three-table effect.

The range plan remains an explicit precondition.
It covers entered branches and checks at actual returned prefixes.
The endpoint supplies no completed target, leaf, or class pass as a premise.
Guard interpretation laws, coherent original classes, original availability,
and the selected closed path domains also remain explicit.

## Boundaries and next work

Connect the new graph to executable memo-aware workers and the full current
scan/required entry. Transfer physical annotation fields to this new trace.
The earlier worker stability and annotation theorems remain preserved for
their older graphs. They do not prove the new bridge by themselves.

General current Scan and outer constrained-call completion remain open.
The new target state tracks completed serial merge requests.
It does not track actual pending thunk publication through the whole class pass.
The earlier serial publication theorem applies to one merge call.
Runtime forcing, concurrency, pointer identities, host cache operations,
and literal HashMap allocation order remain separate obligations.

Continue native allocation and checked transfer, machine bounds, import
trim/DFS/SCC, enumeration and waiting counts, templates, typed refinements,
heterogeneous generators, decision-model, curried/GHC integration, synthesis,
normal forms, and all distinct Sized contracts.
The full-library goal remains active.

The pinned full audit and preservation evidence use `/tmp/mcfta-memo-shared-*`.
Source refresh checks and the new prefix component are recorded in
`notes-main-0696b48d.md`.
