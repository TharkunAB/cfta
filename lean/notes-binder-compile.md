# Finite cyclic graph conversion

The source is `Data.CFTA.Interned.fromFTA`. It assigns one reference per state,
builds nested binders for cyclic states, and shares closed nodes across strongly
connected components. This development proves the graph-to-binder semantic
construction and the law that permits component sharing. It does not yet
prove the whole source SCC and lazy-map adapter.

`BinderGraph.Run` gives independent finite-run semantics with an external
language at each already bound state. `least_exact` proves that removing one
active state and inserting its least recursive binder preserves its complete
language. The proof handles arbitrary cycles and guards. It does not assume
productivity or the language law of recursive graph conversion.

`BinderCompile.compile` recursively builds constructor rows and nested binder
syntax. The active state set decreases at each step. The construction therefore
terminates for every finite input, including unproductive cycles.
`compile_exact` proves its complete open-language meaning. `closed_compile_exact`
proves that a closed finite graph and the resulting syntax accept exactly the
same finite terms. `compileClean` uses the source binder cleanup at each step.
`closed_clean_exact` proves the same complete-language law for this variant.

`BinderComponents.run_local_exact` proves that only reachable external states
can affect a root language. `external_child_cannot_return` proves that a child
in another strongly connected component cannot return to a bound state in the
parent component. `component_shared_exact` derives the source sharing law.
The theorem uses the mathematical mutual-reachability definition of a component.

`BinderSchedule.build` follows the source decision to omit a binder at an
unmarked state. `build_exact` proves exact meaning for every successful
construction, for any cycle test. `BinderTermination` supplies stable execution
bounds from an active-set decrease and a structural rank.
`BinderCycles.cycle_ranked` derives that rank by counting reachable active
states. `cycles_closed_total` proves total, stable, exact conversion when the
cycle detector marks every actual cycle. Extra marked states are harmless.

The source's `Data.Graph` SCC adapter must establish that cycle contract in
each reduced component. Exact component tables, lazy per-context maps,
reference allocation and `createMu` callback substitution still require
correspondence. No theorem identifies those source operations with the model
by assuming the final language law. `BinderSubstitution` supplies the local
substitution theorem, and `StateMap` supplies injective state renaming.

Validation: the pinned `lake build MicroCFTA.BinderCycles` succeeds. The
modules contain no proof placeholders or additional axioms.
