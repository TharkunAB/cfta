# Seeded worker soundness validation

Final source: `SourceCurrentAllocatedSeededWorkerSound.lean`, 133 lines.
SHA-256: `797e3621cb19eceb88dbf069af8c513892f8a95d3537945aa2c580645c108f49`.

The root-managed canonical batch passed with 1278 build jobs and exit 0.
`actual-build.log` records both Sound and WorkerActual. Only the preexisting
unused-input dependency warning remains. No canonical process was started
by this agent.

The direct source check passed with exit 0 and no warnings in
`sound-direct-2.log`. `sound-direct-1.log` records an earlier check before
the Stability dependency existed. It did not elaborate the source.

`sound-public.log` contains five public axiom reports and five full endpoint
signatures. `sound-kernels-2.log` contains five named integration proofs,
five axiom reports, and five full signatures. Both final probe commands
returned exit 0. Neither final log contains errors, warnings, or `sorryAx`.
The reported foundations are limited to `propext`, `Classical.choice`, and
`Quot.sound`. The first kernel log retains an unused-section-variable
warning. The probe declaration was narrowed and the clean second log is final.

The five kernels establish:

1. A supplied seeded return has the same actual graph, CostHeap, same-cache
   loaded Fields, available result, and closed result.
2. That result can enter the next generated native query. The next inventory,
   admission, closed result, and common-subtree inclusion are derived. Only
   the next reached WordRanges and the other operand's initial residency and
   closedness are additional query inputs.
3. Three source paths run the literal rotation `[first, second, seed]`.
4. Empty paths retain the complete checked state at every bound.
5. A failed prefix retains its exact fault and state and does not enter the
   continuation.

The public proof constructs a finite relational graph from legitimate
initial Good, physical Ready, Scoped, Idle, Values, anchor growth, selected
PathSupport, and reached ranges. It then aligns the independently derived
stable worker return with supplied success through unconditional result and
whole-state uniqueness. It does not assume a successful native observation
is already a physical trace. It does not require whole-forest closedness,
a future result invariant, or a completed child callback.

The semantic receipt retains an initial concrete inventory and proper
selected paths. Its language conclusion is common-subtree inclusion.
It does not claim a target exact-language equivalence. Concrete host global
tables, lazy forcing/publication, and GHC execution correspondence remain
separate. No Haskell or older Lean source was edited.
