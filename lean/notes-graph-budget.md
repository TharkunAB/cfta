# Structural graph budgets

`GraphBudget` derives the structural measure used by symbolic unification and
selection. A budget is positive at each state. The sum of the child budgets of
every transition is strictly below its parent budget. Guards do not enter this
condition. A rejecting guard cannot justify a smaller structural measure.

`ofRank` constructs a budget from a finite topological rank and maximum arity.
It uses `(width + 1) ^ (rank + 1)`. This need not be a tight budget. It supplies
a finite proof measure without enumerating accepted terms.

`intersection` constructs the paired budget as the minimum of both input
budgets. It proves all child-sum decreases. `restriction` assigns each template
copy its original state's budget. `condition_no_growth` therefore proves that
path conditioning does not increase the bound.

`project_bound` and `project_smaller` check the actual projection state-set
worker. The new root of a row union uses the maximum selected budget, with a
minimum of one for an empty union. `projection_no_growth` proves the full
union-root bound. `projection_decreases` proves strict decrease at a proper
path when the selected state set is nonempty.

These constructions close the mathematical budget-existence obligation for
acyclic explicit-state graphs and their supported intersection, conditioning,
and projection operations. The source interned identities must carry the
corresponding constructed graph states. The source acyclicity check must supply
a valid topological rank. Whole-driver termination also needs the secondary
measure for its current path and pending constructor work.
