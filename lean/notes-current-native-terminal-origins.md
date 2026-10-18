# Closed native query origins at actual terminal writers

Proof checkpoint: `e66b49b7`. Source main: `c0cc8a05`.
Starting local checkpoint: `f85e3e98`.
Evidence: `restart-evidence/20261018-native-terminal-origins/`.

An actual completed query with closed operands now derives an explicit
terminal classification for each selected physical root row. The proof
recovers the captured request and writer from final native history. It
retains the actual forwarding route, returned cell and protected writer.
It does not assume the desired row origin as a future result.

`SourceCurrentNativeQueryClosedTerminal.route_closed` proves that literal
swap and reset forwarding preserve both operand closures. Its
`closed_residual` theorem excludes left-reference and right-reference
branches only at that terminal writer. It does not exclude references
inside recursive body calls. It retains the same route, returned cell,
writer, full row and self or ordinary result from the earlier theorem.

`SourceCurrentNativeUnionWriterOrigins.left` and `right` inspect the actual
captured union compiler. Each theorem retains its full writer trace,
evaluating owner and one-step finish. It derives the literal union members
and their ordered physical walk. It selects an actual member and returned
value at the same index. It gives the exact prefix walk, child request,
suffix walk and fuel sum. The same full row, including its annotation and
ordered children, has an epsilon-or-reachable origin in that member result
at the final reader heap. Both compiler endpoints grow to that heap.

Closed operands, NodeReady and coherent Good state derive Original inputs
at the captured writer. That step is required for the existing union row
law. Availability alone does not imply Original for arbitrary open values.
WorkInputs for a reduced makeUnion instruction also does not imply that
all values of the unreduced member list are available. The proof uses
neither of these invalid implications.

`SourceCurrentNativeMuWriterOrigins.Schedule` records the actual entered
domain and its two identities. It records the child body request, exact
physical child trace, body availability at optionalBinder entry, literal
maybeMu outcome and exact returned checked state. The compiler fuel is the
child fuel plus two. If the intersection pair is absent from the body's
free-reference list, the result is that same body and the heap is unchanged.
This is the no-construction case. It is distinct from unused-local smart
cleanup after a Mu construction.

The Mu `trace` theorem derives this schedule from an actual compiler trace.
Its `returned` theorem recovers that trace at the same historical evaluating
owner. It retains Good, NodeReady, both growth relations to the reader and
native memo retention. A final native History is not a source-publication
history from the empty heap at an earlier optionalBinder entry. The new
proof does not infer that missing history backwards.

`SourceCurrentNativeQueryTerminalOrigins.Resolved` composes these producers.
Its self branch retains the exact selected row. Its ordinary branch retains
the existing full joined-row witness. Its union branches retain the actual
ordered member result described above. Its Mu branches retain the exact
physical schedule. The `returned` and `request` theorems derive this
classification from an actual completed closed query. The latter also
derives final History, Good and heap growth from initial facts and its
physical trace.

The Mu predicate does not mention the selected row. It does not establish
row occurrence in an original body. General used-Mu writer alignment
therefore remains open. The word Resolved describes an explicit terminal
branch classification. It does not assert complete recursive source-row
lineage. No global rank, BinderFree restriction, finite ordinary Cap or
future semantic origin is added.

The four production strict logs are literally empty. All twelve public
statement, full proof and axiom pairs pass with all eight required settings
and only propext, Classical.choice and Quot.sound. Canonical builds and
full Audit retain only the existing baseline warning. Audit passes 3269
jobs and 71342 dependency checks. Jobs record 4 GiB maximum/high and zero
swap. Failed elaboration attempts remain preserved and unselected.

The integration builds one source with an ordinary leaf, an unused raw Mu
around that leaf, and a union of two raw Mu values. It derives its own
initial Good state, operand availability, closure and numeric headroom.
The existing initial instruction producer constructs both physical query
traces. A separate literal computation identifies their result with the
ordinary leaf. The actual right-Mu query yields its captured body schedule.
The actual right-union query yields its selected ordered member call and
the same full leaf row. Both queries derive the new terminal classification.
The source uses unused binders. It does not establish general used-Mu row
alignment or recursive outer completion.

The integration strict log is empty. Its two public pairs and private Claim
pair receive the same full printer and axiom checks. An earlier check was
interrupted without a result. The retained final proof factors its literal
computation out of the large completion-proof context. Earlier namespace
and Boolean simplification errors remain in unselected raw receipts.

The independent review pins all four final source files and the selected
production receipts. Read
[the review](restart-evidence/20261018-native-terminal-origins/terminal-origins-review-report.md).
It finds no material issue. Its possible narrower ordinary-result Mu
cleanup split is explicitly unproved. It still needs causal publication
history at the actual optionalBinder entry.

The next main target is the missing Mu row reconstruction at that historical
writer. Then compose terminal origins through class folds, Parent and
actual walk dispatch. Existing positional descent needs an exact initial
source anchor for each runtime request. It does not produce that anchor.
All-ancestor node-key exclusion and a finite fresh-call bound remain open.
Collision exclusion alone does not prove termination. Repeated convergence,
equality-operation resources, host Int adequacy and public Haskell
correspondence remain separate obligations.

No Haskell source changes in this checkpoint. No new executable defect is
claimed. FINDINGS keeps the external repair registry first. Field-pool
repair `b9219b9e` remains fixed in `c0cc8a05`. All earlier proofs, repairs,
counterexamples and marked drafts remain unchanged. Publication awaits
the existing direct approval. The full-library goal stays active.
