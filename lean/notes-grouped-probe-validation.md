# Validate discovered recursive family minima

`recurGrouped` discovers keys and minimum sizes by repeated body evaluation.
Each step combines the old table and the reached table. It retains every
key and the least minimum seen for that key. This loop terminates for a
total builder over finitely many keys. Termination alone does not make the
retained table equal to the final body table.

The retained public reproduction inspects `countsAtSize self 0`. An empty
initial family has no records to reject, so this query returns an empty map.
The callback then declares a size-zero base. Later, the discovered occurrence
has a construction marker. The query returns `QueriedRecursiveOccurrence`,
and the callback chooses a size-one base. A guarded recursive alternative
remains in both bodies. Discovery retains zero although the final body has
no size-zero member. Before validation, `minimumSize` returned `Just 0`,
while size counts were `[0,1,1,1]` and `smallest` returned the size-one value.
The probe is `/tmp/mcfta-changing-key-minimum.hs`; its original output is
`/tmp/mcfta-changing-key-minimum.log`.

The source now compares the actual final probe table with `keyMinimums`
before returning a recursive family. A changed key set or minimum returns
`InconsistentRecursiveFamily`. Existing construction errors, the finite
unused-occurrence shortcut, and unguarded-recursion errors keep precedence.
This adds no body evaluation. It checks the probe already used for guards.

`GroupedProbeValidation.checked_fixed` derives equality of the actual final
body table and every successfully returned discovery table. `checked_entry`
rules out retained keys or minima absent from that body. The old union loop
and the repaired rejection have checked counterexamples.

The proof also derives monotonicity for sources, occurrences, pays, choices,
and products. Starting from the empty table, their discovery iterations
reach a true body fixed point. `checked_program` proves that these programs
pass the new check with exactly their previous result.
`checked_program_minimum` retains the independent least-attained-size
theorem. The public callback that changes its base is outside this syntax;
the source rejects its observed inconsistency instead of assuming the
callback is monotone.

The check establishes agreement with the final body table. It does not
prove that every arbitrary Haskell callback keeps its schema, values,
effects, or productivity across evaluations. Complete recursive records
retain those explicit callback and representation boundaries.

Validation: all 194 generator and 142 refinement examples pass in
`/tmp/mcfta-family-discovery-validation.log`. The existing recursive-member
case now checks both minimum and grouped-count rejection for the callback.
Core source is unchanged from the prior passing 284 examples.
