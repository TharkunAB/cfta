# Physically checked prefix bind inversion

Frozen at: 2026-10-20T18:23:53+02:00.

The sole public theorem is `MicroCFTA.SourceCurrentNativeTracePrefixBind.bind_prefix_cases`. It splits the supplied actual bound trace. The unfinished arm retains an actual unbound trace to a nonpure control at the SAME final checked state. Its bound control equals the supplied final control. The completed arm retains both actual physical traces, their SAME middle state, and their exact fuel sum.

The proof uses direct induction on the supplied physical trace length. A yielded inner step takes its physical check from `inputs_before_bind` applied to that SAME bound step's check. `step_bind` and equality of yielded outcomes retain the exact controls and full checked states. The proof does not erase to a raw split and then invent physical admission.

A pure unbound return costs zero instructions. An initially pure control uses an inner trace of length zero and the complete original bound trace as its continuation suffix. At fuel zero, this is the zero-plus-zero split. Error and blocked inner steps cannot match an actual yielded bound step. There is no supplied split, future completion, `Good`, `Fields`, semantic relation, or owner premise.

Validation: selected strict `trace-bind-direct-1` returned zero with an empty raw log. Selected `trace-bind-public-1` returned zero and prints the complete explicit public statement, proof, and axiom list with all eight settings. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the axiom report. Both actual jobs use pinned Lean, all linters, 4 GiB MemoryMax/MemoryHigh, zero swap, and a five-minute timeout. Their inner cgroup readbacks and fresh usage gates are retained.

Counts: one generic public theorem, zero constructed heads, two actual Lean jobs, zero failures, and zero owned canonical jobs. No repository or canonical file was changed. The separate compiled-root-to-owner prefix producer remains unproved; this theorem supplies its physical continuation split only.
