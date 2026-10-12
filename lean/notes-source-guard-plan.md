# Current guard signatures and sparse trie adequacy

`SourceReadAgreement.lean` proves the source evaluator's actual read
dependencies. Entails and Satisfies read refinements. Holds reads the ordered
refinement list and its fixed repeated-path aliases. Same and all actual and
formal positions read complete symbol observations. The proof covers every
Guard constructor, including nested substitutions and pushed negation.
`evaluate_reads` permits different constructor names and leafness at positions
where the guard reads only a refinement. Actual tables are supplied to this
inner evaluator theorem.

`SourceIdentityReads.lean` then proves the table dependencies. Actual paths
are symbol-sensitive. Read agreement preserves the actual table, chosen
representatives, conflict counts, and ambiguity set. Exact actual tables
also require equal fresh-name avoid lists. When there are no conflicts,
fresh-name spelling cannot matter. `no_conflict_signature_exact` proves that
the full public evaluator returns exactly the same verdict for equal source
signatures in that case. It covers nested substitutions; it is not restricted
to guards that contain no substitutions.

`requested_observations_exact` proves a second result without the no-conflict
restriction. Retaining the complete observations at all requested paths
preserves the full avoid list and every actual table operation. The observer
can omit all unrequested positions. Public evaluation remains exactly equal.

`SourceGuardPlan.lean` ports the current `planGuard` request construction.
It uses the ascending set of every current Guard path and the exact
symbol-sensitive need. `lookup_plan` proves both the requested path set and
the observation kind. `signature_exact` connects the executable trie read
to the preceding source signature definition.

`planned_evaluator_exact` proves that this actual sparse trie retains all
information read by the evaluator, including in the conflicting-actual case.
`planned_decided_exact` combines that result with the full unambiguous
sparse-to-complete guard theorem. `signature_group_exact` proves a constant
public sparse guard result across equal trie signatures when there are no
actual-name conflicts.

Two semantic transports remain. A signature can have fresh-name conflicts
while refinement-only positions have different constructor names. The avoid
lists can then select different fresh spellings. That case requires alpha
equivalence of the scoped query, not equality of its syntax. A nonempty actual
ambiguity set can also make the sparse identity partition finer than the
complete partition. SourceEntailment proves the local logical laws for those
renamings, but their complete declaration and nested-scope adapters remain.
No full pruning preservation claim uses those laws without their adapters.

Validation: `lake build MicroCFTA.SourceGuardPlan` builds all three modules
with the pinned toolchain. There are no proof placeholders or new axioms.
