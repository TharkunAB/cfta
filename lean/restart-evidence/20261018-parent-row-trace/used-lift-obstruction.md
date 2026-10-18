# Used-source induction: exact remaining lift

This is a read-only design review. It adds no Lean declaration or checked theorem.

`UsedBinderOutputTags.StrictBodyIH` quantifies over arbitrary reference and
value relations. It cannot be discharged for those arbitrary relations.
A variable needs a lexical base law. A row needs an ordered child value law.
`RootMatch` uses the value relation on ordered children and on complete Mu
atoms. Its conclusion alone does not produce that value relation.
See OutputTags lines 219-230 and RootAlternatives lines 24-40.

The existing `StoredNormalizedPlans.Related` supplies a concrete recursive
value relation. It preserves full row fields and ordered children. An open
Mu compares the two stored bodies after binding each original self name to
one common argument. Closed captures agree literally. This last condition
respects the actual stored-execution closed shortcut.
However, its union relation preserves member order. Actual normalized
unions can reorder and deduplicate different fresh own references. The
checked alias boundary rules out adopting that ordered relation unchanged.
See StoredNormalizedPlans lines 23-49.

A candidate lift must retain that relation's lexical Mu extension and
closed-capture rule, but compare root union alternatives by occurrences.
It must keep full symbols, full guards, ordered child relations, and the
reference-versus-Mu distinction. It must also retain the bare-self test
needed by root filtering. Actual alias transport and output reflection
already produce the latter test; it is not a future output hypothesis.
This candidate is a design proposal. Its definition and closure laws are
not proved by this review.

The used-Mu branch has a separate causal obligation. `request_probes`
recovers the selected record with the current complete probes. It does not
recover the current candidate's body: the actual winner can be older and
can have another source body. A strict current-source-size induction does
not make that earlier writer body smaller than the current requester.
See NativeRequestProbes lines 17-30.

The checked unused law shows the required causal proof order. History
induction first establishes the earlier-store law after Depth, ordinary,
reservation, and the body callback. Only then does it establish and publish
the new candidate law. Keep-first retains any earlier winner's law.
See NormalizedComparisonExecution lines 381-423. A general used law must
follow this order and remain stable through NoNewMu. History.retain alone
does not imply physical growth or availability.

The exact missing producer is therefore a simultaneous source/history
proof. Smaller source bodies must produce the recursive lexical value
relation for actual outputs. Every first publication must establish its
body-versus-ordinary reconstruction relation under a common local argument.
An actual warm read must use that earlier writer's proved law and current
full probe readback. Neither a matching probe pair alone nor a stored record
with the desired relation supplied as a premise closes this obligation.

No new unused-only branch, relation-only wrapper, future completion
hypothesis, whole-forest closure, finite Cap, or runtime claim is added.
