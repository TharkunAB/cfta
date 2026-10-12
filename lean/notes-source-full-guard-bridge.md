# Complete unambiguous guard and pruning correspondence

`SourceFullGuardBridge.evaluate_equal` proves the entire source guard traversal
across equal observation reads. It covers Top, Bottom, Same, Entails,
Satisfies, Holds, Substitute, Not, And, and Or. It retains the outer guard's
one actual table across every nested scope. Missing paths and failed scope
resolution agree. Boolean polarity and source short-circuit folds agree.

`SourceKnownScopes` derives all resolved identity flags from the gate's empty
ambiguity table. `SourceScopeSymbols` proves exact structural comparison
through the source literal symbol replacements. `SourceQueryDecisions`
instantiates the complete ordinary and Holds query transports. These local
results supply every case of the full guard proof. No premise assumes that
an entire guard, source query, or pruning pass already preserves its result.

`SourceFullGuardBridge.complete_decision` connects each decided cell to the
public complete-term evaluator. It uses the independently proved
`unambiguous_decided_exact` after transporting the cell's query. Conflicting
names and allocated actual declarations are permitted. The earlier
conflict-free condition is not required.

`FullGuardPruneStable.prune_exact` composes the full guard result with exact
finite graph specialization and the repaired candidate loop. Every
successful return preserves the full confirmed term language, including the
case which restores the original guard after ambiguity. The theorem includes
all current guard constructors and arbitrary nested source scopes.
`gate_unambiguous` proves that the Haskell conservative identity check, which
uses an always-unknown comparison callback, excludes every ambiguity of the
more precise sparse root callback used by the evaluator. Both gate sites in
the executable graph candidate model now use that exact conservative callback.

The solver premise is explicit. `SourceQueryTransport.Transport` compares
declaration domains and both formula meanings in both directions under the
actual source name map. Both environment maps are constructed. `entails_iff`
and `supports_transport` require no equality of solver verdicts. They prove
mathematical transport, including positive and negative evidence.

`SourceQueryTransport.Stable` is the additional backend contract needed for
exact Yes/No/Unknown preservation. It says that a backend retains its verdict
under those proved lossless name transports. This is stronger than repeated
identical-query stability. Soundness alone does not imply it. The supplied
Z3 backend is not asserted to satisfy it. GuardAlphaBoundary gives a concrete
ambient-declaration collision which changes Unknown to Yes.

The query-domain model contains the exact generated declaration list with
the original-name sort-domain function. Equating it to a complete configured
SMT context also needs ambient declarations, ambient assumptions, default
free-name declarations, and collision checks. Timeout and IO exception
behavior remain backend boundaries. The final sparse source graph adapter,
recursive pruning driver, and equality narrowing composition remain in their
separate modules. This theorem does not certify that whole adapter by a
generic callback assumption.

Validation: `lake build MicroCFTA.FullGuardPruneStable` succeeds with the
pinned toolchain. The six new bridge modules contain no admitted declarations
or native proof evaluation. No production source changed for this milestone.
