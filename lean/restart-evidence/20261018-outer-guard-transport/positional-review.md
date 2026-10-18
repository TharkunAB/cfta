# Positional row provenance

Checked on 2026-10-18. The production source is
`SourceCurrentPositionalRowOrigins.lean` at SHA256
`8e1e08ecdc22b8d5b6b9ac87ca7bc8bbc1f6423827da67cb20bd4b6af21c6b46`.

## Result

`required_children` and `edit_children` prove literal option equality at
an absent child-map key. They use only the actual child graph and absence.
Other selected children can use arbitrary recursive calls and intermediate
heaps. No condition on their syntax or returned values is added.

`required_rows` and `required_node` retain an indexed original row,
the complete original guard, symbol, arity, and exact unselected child value.
They use actual completed Require graphs, initial SemanticReady and CostHeap,
and resident rows or an available original node. They derive constructor
readback from those facts. They do not assume a returned-origin relation.

`edit_node` derives the same positional statement through actual EditRows
and normalized makeNode. It uses the existing RowsReads, Populated, Allowed,
shared Ready, initial row residency, RowsSafe, and initial memo Valid.
These premises remain explicit. Ready includes current physical and semantic
admission, merge storage/coverage, and receipts for already filled slots.
This theorem does not construct those initial facts or a future edit graph.

A returned row can have a different row index after rejection and canonical
normalization. Source indices are existential. No injectivity or fixed row
order is asserted.

## Exact footprint

Three kernel equations compute the actual Needed and Edit compilers for
`{0,100,01,1001,101}` and the explicit classes `{0,100}` and
`{01,1001,101}`. At forest position 1, each trie has only key 0.
Thus an ordinary value at that position retains child 1 in each surviving
row. These equations concern the explicit path lists. They do not add a
new theorem about equality normalization; the earlier normalized-list
check remains an executable diagnostic.

The causal plain-exposure correction is recorded separately in
`positional-review-correction.md`. Existing `accepted_head` can classify
recursive exposure from an actual accepted gate and a produced causal
Mu-profile heap. A global raw-edge plain annotation heap is not required.
This component does not derive that causal heap at each reached Head.

## Constructed check

The fixture constructs a closed ordinary source with a literal guard 17
and two equal productive raw Mu children, `mu(pair self self)`. An actual
Required worker run selects child 0. That child changes from Mu to an
ordinary node. A surviving output row retains the exact original Mu at
child 1 and the full guard 17. The proof invokes `required_node`.
SemanticReady, CostHeap, availability, the successful worker equation, and
the completed Require graph are all derived within the fixture.

The guard type in this fixture is Nat. The fixture tests literal guard
retention. It does not assert an effective equality class for guard 17.
It does not execute a full class Edit or Parent call.

## Validation and attempts

Selected strict: `positional-draft-4`, exit 0 and zero-byte log.
Canonical: `positional-canonical-1`, exit 0, 1364 jobs. Lake replayed
warnings from unchanged dependencies. The new source strict log is empty.
Selected imported public: `positional-public-2`, eight complete
signature/proof/axiom checks. Selected constructed strict:
`positional-kernels-3`, exit 0 and zero-byte log. Constructed full probe:
`positional-kernels-public-1`, one complete check. All selected probes
use the eight explicit options and only the standard three axioms.
All executions record effective 4 GiB maximum/high and zero swap.

Draft 1 failed because source-index types were not explicit. Draft 2
checked the initial four lemmas with an empty log. Draft 3 checked all
proofs but reported unused instance warnings in the three pure compiler
equations. Draft 4 moves the instance scope before those equations.
Kernel attempts 1 and 2 failed only in fixture elaboration and a constructor
disequality tactic. All numbered sources and raw logs remain unchanged.
Public 1 checked the same definitions before the imported public check.

## Remaining boundary

This result is a per-stage completed-call positional law. The full
Required/class-fold/Parent chain at the relevant source occurrence remains
to be composed. It does not prove that every repeated child-1 dispatch is
unrealizable. It does not exclude every active physical key collision,
bound fresh recursive requests, or prove general outer termination.
