# Actual Merge Empty support

Reviewed and checked: 2026-10-21 01:58 CEST.

The final 80-line module exports EmptySafe, empty_safe, run and call.
EmptySafe restricts only the completed result at the tagged Empty key.
The actual Run/Call mutual induction preserves that law in the same returned table.
The call theorem also proves input = Empty implies output = Empty.
All actual code, state, result and table indices remain in the statement.
The proof needs no Good, Stored, SemanticReady, availability or language premise.

The existing reference_empty theorem proves that only Empty has this tagged key.
An Empty miss has an actual pure Empty body. Completion retains either its old
law or that actual candidate. The final winner lookup uses the same returned table.
A hit uses its exact stored entry. General instructions preserve the table law.
This is an actual transition invariant. It is not an existential producer wrapper.

The arbitrary Empty-to-owner cache in PhysicalMergeSupportBoundary.empty_hit
violates EmptySafe whenever owner is not Empty. Physical Stored and forward
language Covers alone do not imply this additional invariant. The empty table
satisfies it, and real sequential workers preserve it. The result does not prove
full structural path support, active owner exclusion, completion or runtime refinement.

Selected strict direct-3 has exit 0 and an empty raw log. Selected public-1 has
exit 0 and a complete 16,252-byte log. It prints all four types/declarations and
scoped axioms with the eight printer settings. EmptySafe and empty_safe use no
axioms. run and call use only propext and Quot.sound. All are within standard three.
Effective caps are 4 GiB high/max, zero swap and five minutes for every Lean job.

All attempts remain. direct-1 failed before Lean because the sandbox could not
connect to the user bus. It has no effective-cgroup receipt. direct-2 is a real
capped failed elaboration: Run.rec had already introduced the hypothesis in
its call motives. direct-3 changes only those two intro steps to rename_i.
There are three Lean jobs, one failed elaboration and one separate prelaunch failure.
There are no constructed examples, canonical builds, official edits or Haskell edits.
