# Ordinary Mu query rows from actual binder readback

Proof checkpoint: `ed544648`. Source main: `c0cc8a05`.
Starting local checkpoint: `2a1c488f`.
Evidence: `restart-evidence/20261018-native-mu-row-readback/`.

A selected physical ordinary row returned by a native Mu query now has an
actual reconstruction witness. It retains the captured compiler, domain
entry, body request, literal optional-binder result and full returned row.
The proof covers the absent-pair and constructed branches. It adds no
BinderFree restriction and no finite ordinary Cap condition.

`SourceCurrentNativeOrdinaryMuFinish.selected` first inspects the literal
smart cleanup result. A selected nodeEdges row excludes the retained Mu
and bare-self Empty branches. The returned value is the exact stored body,
with the same selected row index. The produced probe invariant Correct
then proves that usesLocal is false. Correct relates that actual stored
body to its actual depth and ordinary probes.

The implication is false for arbitrary unrelated body and probe values.
Cleanup inspects storedBody.free. The usesLocal test inspects the probes.
The constructor generates Correct for its exact selected winner. The proof
does not add it as an unexplained future semantic law. This is a correction
to a proof premise. It is not a new Haskell defect.

`SourceCurrentNativeConstructReaderReadback.construct_row` decomposes the
actual completed construct call. It retains both current probes, the raw
ordinary stored-substitution execution, root filtering and canonical request.
The literal request selects an actual stored Mu winner. The theorem keeps
that winner at the constructed endpoint and at the later reader. It does
not replace the winner with the current candidate.

The completed constructor supplies Correct at that exact endpoint. A
selected physical ordinary row derives usesLocal=false, exact stored-body
return and the same indexed row. Grows.nodeRecords carries the complete
selected Mu record forward to the reader. The reader's causal publication
history supplies the unused cleanup law for the actual current ordinary
probe. Root filtering then preserves full row origins in the actual raw
ordinary substitution. The theorem proves this relation for every view,
including guards and ordered children. It does not equate changed children
with their original input values.

No publication history is inferred backwards at an earlier optionalBinder
entry. Native memo History and source-publication History have different
contracts. The new construct theorem needs the later actual publication
history and forward heap growth. Initial SemanticHeap and Available supply
the ordinary constructor obligations. No extra reader semantic premise is
needed. The constructor's final context supplies Correct.

`SourceCurrentNativeQueryMuRowOrigins.OptionalOrigin` separates the absent
pair from actual construction. In the absent case the result and heap are
literally unchanged. In the constructed case it retains the full readback
above. Its MuRow predicate retains the same actual captured writer, owner,
entered domain, exact body trace and child fuel. It retains the literal
maybeMu endpoint, writer-to-reader growth and native memo retention.

The `returned_mu` theorem recovers the captured compiler from native memo
history. The actual child trace transports the captured Good semantic heap
to the optional-binder entry. Domain entry leaves that heap unchanged.
The exact post-binder checked state identifies the constructed heap, so
the existing writer growth reaches the same final reader.

The composed `returned` theorem preserves the existing self, ordinary,
union and closed forwarding alternatives. It replaces the old schedule-only
Mu branch with the actual full row readback. The `request` theorem derives
final publication history from initial publication history and the executed
physical query trace. It also derives final native History, Good and heap
growth. No future publication or semantic row result is a caller premise.

The root integration derives initial publication history from its own closed
source. Its right-Mu and right-union queries derive complete physical traces
and the expected selected leaf. They apply the stronger query theorem.
These source binders are unused and exercise the absent-pair branch.

A separate constructor integration builds an open source union of the exact
pair reference and an ordinary leaf. It derives its own source semantic
heap, body availability and publication history. The pair is free in that
body. Actual construct and maybeMu calls return the selected leaf row.
A fresh later edge allocation changes the reader. Forward history and
Grows retain the selected winner there. The new construct readback theorem
supplies the exact full row. A warm construct returns the same value and
reader state. This example exercises the constructed branch.

Three production strict logs and both integration strict logs are empty.
All nine production public, three constructed and one private Claim pairs
pass in six groups with full statement, proof and axiom checks.
They use all eight printer settings and only propext, Classical.choice and
Quot.sound. Full Audit passes 3272 jobs and 71349 dependency checks. Jobs
record 4 GiB maximum/high and zero swap. Successful root jobs peak at no
more than 391 MiB. The first root strict attempt exited zero with two
unused-instance warnings. It remains unselected. The final source moves
the unnecessary Symbol equality instance below the private helper.

The first constructor example public printer exited zero but reported a
failed expression print. The verifier rejected that receipt. The final
example moves the identical checked proof to a private theorem and exposes
the same public statement as an alias. The retained comparison proves byte
identity of both the statement and moved proof. The second public print is
complete. The failed receipt and attempted manifest remain unselected.

The independent production review finds no material issue. Read
[the review](restart-evidence/20261018-native-mu-row-readback/mu-row-review-report.md).
It records the necessary Correct premise and exact stored-winner scope.

The selected root row is physical. These theorems do not establish epsilon
exposure of a retained used Mu. General raw ordinary and union substitution
already have indexed source-row and ordered Calls producers. The remaining
source-lineage case is arbitrary nested stored Mu reconstruction, including
rows exposed after that reconstruction. An epsilon Origin is not itself a
proper original source occurrence or hereditary field proof.

Derive that missing source anchor, then compose through class folds, Parent
and actual walk dispatch. All-ancestor node-key exclusion and a finite
fresh-call bound remain open. Collision exclusion alone does not establish
termination. General recursive outer completion, repeated convergence,
equality-operation resources, host Int adequacy and public Haskell
correspondence remain separate obligations.

No Haskell source changes in this checkpoint. No new executable defect is
claimed. FINDINGS keeps the external repair registry first. Field-pool
repair `b9219b9e` remains fixed in `c0cc8a05`. Every earlier proof, repair,
counterexample and marked draft remains unchanged. Publication awaits
the existing direct approval. The full-library goal stays active.
