# First frozen fixture scope

Status: NOT RUN. No accepted-source counterexample or Haskell defect is established.

Use the real FirstOrder source Library with opaque component groups `fix :: forall b. (b -> b) -> b` and `k :: forall a. a -> Int`, no query arguments or exclusions, Query Int and source size3. Type variables have distinct component names. Each actual use still chooses its own instance. No Haskell value named fix is evaluated.

The negative candidate is `k (fix fix)`. The finite positive control at the SAME source size is `k (k fix)`. Preserve the exact existing rawSearchSpace, public solutionsOfSize, reduced runsBy, and raw runsBy routes. The diagnostic only observes their outputs. It adds no custom automaton, pruning oracle, stop rule, native provider, depth bound, runtime clone or new solver.

Each process selects ONE route. A supplied output observation limit is not a worker fuel or proof bound. Absence can be reported only after actual list exhaustion. A process timeout, output cap, exception or unfinished construction is not rejection. Same-run typed terms and residuals are printed together for a matched candidate.

Root owns compilation and execution. This packet changes no package source or existing frozen artifact.
