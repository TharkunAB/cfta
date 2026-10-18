# Structural class row origins

Frozen at 2026-10-19T00:56:26+02:00.
Production: `SourceCurrentClassStructuralOrigins.lean`, SHA-256
`707ab1c2163127be66b0edb10a8fb534fa16b72d1b2acb7d118256cd1e51619c`.

The checked `node` theorem covers an arbitrary structural `RowAt` in the
result of an actual completed node edit. It returns an indexed structural
occurrence in the input with `RowOrigin`, or an occurrence in an actual
native leaf result or Head exposure. `RowOrigin` preserves the complete
symbol, guard, and arity. It does not assert child identity.

`Event.leaf` requires the actual leaf reads and initial native writer history.
`Event.head` retains actual Head reads and the recursive body reads. Its event
value is the exposed value before the recursive edit. It is not an arbitrary
final result. Recursive event lifts follow the actual body edit.

`Event.ordinary` retains the canonical output row index and the raw rebuilt
row index separately. Both indices select the same complete parent row.
`RowEvent.here` retains the actual ordered child read, its selected output,
and the full `SharedEditChildLineage.Slice`. The slice includes the exact
prefix, selected dispatch or identity, and suffix states and memo tables.
`ChildEvent` and `RowEvent` retain the scan offsets through earlier siblings.
An unselected child preserves its whole structural occurrence by identity.

The proof uses mutual induction on `NodeReads`, `ChildrenReads`, and
`RowsReads`. The ordinary case derives the canonical survivor from the
actual `makeNode` equation. The child and row cases derive intermediate
physical support and history from actual completed prefixes. The proof uses
the existing physical edit effects and exact child slice producer. It does
not assume a Required origin or any desired future row law.

The assumptions are initial `SharedReady`, input availability, path safety,
valid memo tables, native writer history, populated edit syntax, a leaf,
and allowed class paths. The observed completed `NodeReads` supplies the
actual calls. This theorem does not construct completion or a fuel bound.
The source arm retains a complete original row object and its structural
occurrence. The event arm retains a structural occurrence in the event
value. Its path is not asserted to equal a suffix of the original output
path. Canonical row indices can change during reconstruction.

This result extends root-row coverage to descendants. It does not prove a
fold-wide initial occurrence, semantic observation origin, native operand
ancestry, a decreasing result measure, or global renewal or termination.
Head and native event obligations remain explicit. Structural Mu-body
positions do not imply observational epsilon origins.

Selected checks: `class-structural-direct-9` has exit 0 and a literal empty
log. `class-structural-canonical-1` has exit 0 and 1477 jobs. Its only warning
is the unchanged `InternedFreshOrdinaryClosedCompletion.lean:24:5` dependency
warning. `class-structural-public-1` prints all four public heads with full
proofs and axiom reports. The hardened check confirms all eight printer
options, no omitted terms, and only the standard three axioms. All runs
have verified 4 GiB memory and high limits, zero swap, and a five minute cap.

Attempts 1 through 8 remain unchanged. They failed on local elaboration:
the row binder type, an ambiguous `Ordinary` name, index binder types,
explicit actual graph witnesses, and singleton row membership. They do not
establish a mathematical counterexample. Attempt 9 is the selected source.
Counts: 4 public heads, 0 constructed heads, 0 auxiliary heads, 11 capped
Lean runs. No new source-built fixture is claimed for this component.

The next composition must transport structural occurrences across earlier
completed class phases, or resolve the explicit native and Head events.
The theorem does not identify a phase value with its Required input.
