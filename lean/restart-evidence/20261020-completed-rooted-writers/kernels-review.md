# Completed-build rooted writer integration

Checked 2026-10-20 15:36 CEST.

The source root is `union [mu x.node7[x], mu x.union [Empty,node7[x]]]`. Both binders use smart construction. The first literal completed call installs a used Mu. The second call uses different syntax and returns the same Mu at the same heap. The complete root call returns that Mu. The final heap is Ready, and the returned value is Available. The exact node-table entry and stored Mu payload are retained.

The witness applies `SourceCurrentCompletedBuildRootedWriters.build_writer` to the actual complete root call from empty. Its initial Context comes from `empty_context`. The initial absence of Mu records follows from the literal empty heap. The witness destructures the resulting rooted `Written` once. It retains the SAME publication event, its `Reached` source receipt, exact key and candidate equality, first-write missing cell, callback issued paths, and final heap growth and issued extension. It constructs the older `NativeMuIssuedWriters.Written` from those same fields.

The warm call applies `build_writer_or_prior` with a Context derived from the actual first build. The witness retains the resulting prior-cell-or-rooted-writer disjunction. It also proves the exact cell is present before that call. It does not select the new-writer alternative or identify the existential publication syntax with either source binder.

`rooted-kernels-direct-1` returned exit 0 with a zero-byte log. `rooted-kernels-public-1` returned exit 0. Its one complete statement, full proof, and axiom report pass the hardened all-eight-option check. The axiom report contains only the three permitted standard axioms. The public theorem aliases a private checked witness. Both jobs use Lean 4.34.1 with effective memory.max = memory.high = 4294967296 and memory.swap.max = 0, under a five-minute cap. Both handles were personally observed terminal. There are no failed or incomplete attempts.

Counts: 0 owned production public pairs; 1 constructed pair; 2 Lean runs; 0 canonical builds. Root-owned production probes are not counted here. The source and receipts are stored under `/tmp` only. The package copies stable production inputs and uses relative manifest paths. Its verifier checks copied bytes and the selected completed receipts without loading repository artifacts.

This integration proves source-rooted publication provenance for this completed call. It does not prove uniqueness of the selected source occurrence, publication syntax identity, ancestry of later native captures, a decrease of generated children, global renewal, termination, or Haskell correspondence. The general production theorem still needs its explicit initial Context and either absence of initial Mu records or the prior-cell alternative.
