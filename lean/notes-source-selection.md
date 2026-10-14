# Ordered source child selection

`MergedSourceSelection` models the `recursive`, `kept`, and `accepts`
expressions in `mergedUnion` in
`cfta/src/Data/CFTA/Interned/Operations.hs`. It tries the original
closed Mu operands in order. It preserves every closed Mu. It removes
another child only after a successful `subsumes` call. Open children pass
the free-variable gate without comparison. Canonical identity removal
follows the completed filter.

`recursive_member` connects the source's identity membership test with the
closed-Mu predicate on coherent available source inputs. Each comparison
uses the actual ordered stateful checker. A failed comparison retains its
cache effects before the next candidate is tried. This model uses no
assumed comparison result or abstract recursive callback.

`select_complete` derives one sufficient fuel bound for the complete
ordered selection. Every larger bound returns the same exact retained
list and actual cache. The proof derives each demanded comparator bound
and preserves `Facts`, cache growth, issued-name history, and `NoNewMu`.

`MergedSourceSelectionSemantics.select_replay` proves that this completed
selection returns exactly the same canonical input records in every
later cache, with no cache effect. `any_replay` and `retain_replay` give
the same statement for the ordered cover search and pre-deduplication
filter. Replay includes the failed comparisons before each successful
cover and before each retained input.

`select_coverage` proves a stronger operational statement. Every original
input is retained, or it is closed and has a successful comparison with a
retained original closed Mu. The comparison replays as true with no cache
effect in any later cache. `retain_recursive` ensures that the selected
cover cannot itself be removed. Coherent complete records ensure that
identity deduplication cannot replace a retained payload.

`select_exact` composes these witnesses with the proved stateful
comparison theorem. The retained records and original inputs have exactly
the same union language in any later source cache that retains facts,
preparation, and input availability. `select_actual_exact` derives this
equation in the exact cache returned by the original selection. Both
lists use the finite-term graph of that returned cache. No global `Ready`
premise or warmup is required.

`select_complete_exact` derives one stable sufficient fuel bound, exact
retained output and cache, exact replay in that cache, and exact union
language from the original source facts. It has no recursive termination
or semantic-correctness premise. The successful stateful comparison
theorem discharges every language-inclusion obligation.

The structural restriction remains `Prepared`: each complete Mu body
satisfies `PreparedWithoutMu`. The guard interpretation must make each
guard accepted by the source `noConstraint` predicate true for every
term. The concrete guard representation remains an explicit source
correspondence boundary. Selection preserves the accepted term set; this
statement does not equate generator multiplicity or term weights. The
outer merge memo wrapper and repeated equality-pass convergence remain
separate obligations.

The pinned Lean 4.34.1 build checks the operational and semantic modules.
The imported-theorem audit permits only `propext`, `Classical.choice`,
and `Quot.sound`. Its focused log is
`/tmp/mcfta-source-selection-semantics-audit.log`.
