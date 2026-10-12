# Proper suspended dependencies

`EnumerationProgress.lean` defines `ProperState`. Pure equality slots have no
suspended paths. Graph slots contain only canonical, nonempty, nonterminal
tries. Each such trie supplies a proper descendant path.

The module proves this invariant for the initial state, allocation,
intersection, assimilation, node restriction, the terminal merge loop, the
mutual node and edge traversal, and `enumerateOut`. `enumerateFully_proper`
composes the actual complete-graph caller. Its initialized corollary derives
the invariant from the real initial state.

`findExpandable_not_stuck` follows the actual scheduler summary. If it returns
blocked work, each candidate has an incoming constraint from another eligible
graph slot. `ProperState` and a satisfying complete assignment turn that
constraint into a strict subtree dependency. A candidate with maximum assigned
term height contradicts that dependency. The theorem therefore excludes the
actual blocked result under the stated assignment and derived shape invariant.

`finished_free` proves that every pending slot after complete-graph termination
is a free equality variable. `EnumerationAssignment.completed_assignment`
now constructs complete equation assignments from this fact and the derived
fragment dependency ordering. Execution existence, sufficient execution
bounds, and no-loss remain open. A conditional theorem
that excludes blocked scheduling does not establish those properties.

Validation: `lake -d lean build MicroCFTA.EnumerationProgress`.
