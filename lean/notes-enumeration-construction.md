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

`EnumerationOutConstruction.enumerateOut_complete` constructs the selected
root reads, local execution, ancestry updates, and final fragment write.
`EnumerationDecrease.enumerateOut_height_origin` proves that each selected
expansion removes its own pending slot. Every remaining pending term at that
height or above comes from the same pending slot before expansion.

`EnumerationHistogram` counts pending graph slots by assigned term height.
It proves a strict decrease at the selected height and nonincrease at higher
heights. It also preserves the fixed initial height bound. `HeightOrder`
proves this finite descending count order is well-founded. Counts at lower
heights can grow without a fixed upper bound.

`EnumerationTermination.initialized_complete` now constructs a successful
initialized `enumerateFully` execution for each accepted root term. The final
assignment satisfies the final state and still assigns that term to root zero.
The proof derives all internal scheduler and state conditions. It assumes no
execution step or termination measure law.

Final renderer existence remains open. The remaining invariant must exclude
reachable pure equality holes that have no stored graph restriction. The
existing fragment dependency ordering then supplies finite rendering bounds.

Validation: `lake -d lean build MicroCFTA.EnumerationTermination`.
