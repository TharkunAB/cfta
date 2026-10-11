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

The current compiler binds each visited active state before cleanup. The source
uses SCCs to skip unnecessary binders before construction. Its exact finite
component tables, cycle test after each binding, lazy per-context maps, reference
allocation and `createMu` callback substitution still require correspondence.
No theorem identifies the reference compiler with those source operations by
assumption. `BinderSubstitution` supplies the local substitution law, and
`StateMap` supplies injective state renaming.

Validation: the pinned `lake build MicroCFTA.BinderComponents` succeeds. The
modules contain no proof placeholders or additional axioms.
