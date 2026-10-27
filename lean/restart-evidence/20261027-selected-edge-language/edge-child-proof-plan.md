# Native edge-child evidence draft

The draft is `drafts/SourcePruningEnumerationEdgeChildLanguage.lean`.
It uses the actual `EdgeInputs.children` list. It does not introduce a graph or a runtime operation.
Root must run the Lean checks. No compiler or parser was run during this draft.

`child_evidence` consumes the exact effective-bucket `All₂` relation from
`TraversalCompletion.complete_with_fragments_semantics`. Each actual input must also
retain its full bucket: the child is an ordinary node, its bucket has a terminal
constraint, or its bucket is empty. This condition is explicit. A non-node with a
nonempty nonterminal bucket otherwise exposes only the empty effective bucket.

The forest proof maps the left side to the actual native value and the right side
to the filled fragment. `List.zipIdx_map_fst` removes only the indices. It preserves
the original order, duplicates and child count. The indexed proof uses
`all₂_get_right`, the actual input-map lookup and `List.getElem?_zipIdx`. The retained
bucket is then exactly `descendScs index (scs ++ suspendedVars start tries)`.

`restrictions_from_children` takes this native forest and full indexed evidence.
The forest proves the actual term count equals `edge.children.length`.
`edge_equalities_from_children` derives the fresh own equalities from explicit
validity and fresh arity. `suspended_descent_complete` derives the inherited
restrictions from explicit inherited validity and arity. The explicit nonterminal
inherited gate discharges its root-path obligation. `descendScs_mono` restricts the
combined descendant evidence to inherited constraints.

These are conditional semantic helpers. The old operational SelectedEdge producer
does not prove all their gates. In particular, native readiness does not prove
cached guard normalization, fresh arity, inherited trie validity or structural
retention. The projection audit supplies own validity and guard decomposition only
under its separate actual annotation-heap condition. Fresh arity stays explicit.
This draft does not claim full edge guard acceptance, parent acceptance, rejection
safety, language completeness or a new H6 result.

Defining source positions read:

- `SourcePruningEnumerationEdgeInputs.lean:15`: actual child list.
- `SourcePruningEnumerationTraversalLanguage.lean:83`: effective bucket relation.
- `EnumerationSemantics.lean:434`: ordered map and right-index evidence.
- `EnumerationCorrectness.lean:504`: descent inclusion and own equality recovery.
- `EnumerationState.lean:483`: inherited restriction recovery.
- `InternedGuardedLanguage.lean:110`: native forest and ordered `All₂` equivalence.

The adjacent JSON records the exact source identities and draft identity. It is
source evidence only. It is not a compiler report.
