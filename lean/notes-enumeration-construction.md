# Constructive local enumeration and execution bounds

`EnumerationConstruction.enumerateNode_complete` constructs a successful
actual `enumerateNode` execution for each finite `Accepted` term. It selects
the accepting edge, installs fresh equality witnesses, runs the children in
source order, and records the residual predicate. The final assignment agrees
with the input assignment at every previously allocated variable.

The theorem uses the explicit `CompleteGraph` and `IntersectionCorrect`
interfaces. Its state premises are `Safe`, a satisfying assignment, valid and
bounded inherited tries, and inherited references to pending classes. These
are local premises. The complete initialized caller must establish them and
show that repeated expansions terminate.

`EnumerationCompleteness.mergeTerminal_terminates` constructs the complete
representative scan, union loop, winner lookup, and duplicate assimilation.
Equal satisfying pending values pass each structural-empty check.
`enumerateNode_terminal_terminates` also constructs the final node restriction.
Neither theorem assumes successful execution of the action it constructs.

`EnumerationExecution.runs_moreFuel` retains the exact successful returned
term, residuals, and state at every larger execution bound. Its proof follows
the actual mutual traversal, full caller, and renderers. The caller result
also applies to its general callbacks and recursive bookkeeping.
`findExpandable_terminates` constructs a successful scheduler scan from a total
forest. `findExpandable_progress` proves that a satisfying safe proper state
has a sufficiently bounded scan that returns completion or available work.

Whole-caller execution existence and final renderer existence remain open.
Local no-loss and scan progress alone do not prove them. The next termination
obligation is to show that each scheduled expansion removes its selected
pending term and introduces only pending proper descendants.

Validation: `lake -d lean build MicroCFTA.EnumerationConstruction`.
