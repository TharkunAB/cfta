# Protected checked finish prefixes

Status: frozen. `SourceEqualityNativeDemandProtectedPrefix.lean` has 184 lines. Its SHA-256 is `10c94c24f825b70b2443e32a18ceb10f6faec69133a912153458d6ba820833b0`.

The ten public helpers expose actual finish ownership without a future query-completion premise. `finish_node_cases` and `finish_edge_cases` split an arbitrary raw frame prefix. A zero-step prefix retains the frame and the entire incoming checked state. A positive prefix executes exactly one literal finish and retains the actual suffix from the updated full checked state.

`node_body_owner` and `edge_body_owner` accept the actual body trace to its pure return. They use `trace_done` on that same finite trace and the existing running-cell retention theorem. The exact captured request remains evaluating at the body return. The literal finish then installs that same request with its actual returned value. No availability, result language, word range, or future physical trace is assumed by these structural helpers.

`node_cases` and `edge_cases` apply the existing checked prefix split. They retain its pending-inner alternative. In the crossed-return alternative they expose the actual completed body trace, its exact middle checked state, its captured owner, and its immediate publication state. They then split the remaining finish-frame prefix into zero or positive steps. They do not identify a nested finish frame with an enclosing frame from syntax alone.

The returned count satisfies `bodyFuel < fuel + 1`. A body trace may use the entire supplied appended-body prefix when that prefix stops at its finish. If a preceding request-publication step belongs to the enclosing call prefix, the body trace is strictly shorter than that call prefix. The joint strong induction can prove availability or edge residency on this actual smaller trace. These helpers do not supply that physical postcondition as an oracle.

`bind_nonpure` retains the nonpure current-control condition through an appended continuation. `inputs_bind`, `words_bind`, and `entered_bind` retain the current physical input, key-word, and domain-enter checks. Each requires the inner control to be nonpure. An already pure control can expose the outer continuation, so these lemmas do not omit that condition.

Validation uses pinned Lean 4.34.1 with both unused-variable linters enabled. All three production direct checks pass without diagnostics. Their exact source snapshots remain in this directory. The final production source is direct attempt 3. The canonical `state-protected-build.log` passes with 1094 jobs. Its only warning is the historical unused `inputs` warning from `InternedFreshOrdinaryClosedCompletion.lean`.

`protected-prefix-public-1.log` checks every public declaration with explicit types, proofs, universes, deep terms, and ten million print steps. All ten axiom/signature pairs pass without diagnostics or `sorryAx`.

`protected-prefix-kernels-2.log` checks two constructed executions. The first starts with an actual evaluating Empty node owner, runs the compiled Empty body and its finish, and stops before the outer read. The second starts with an actual evaluating edge owner, runs the checked arity-mismatch body, executes the actual sentinel constructor work, finishes the same owner, and stops before the outer read. Both kernels apply the main prefix classifier. The completed inner trace bounds exclude the pending-inner branch. Both retain the exact publication, operation state, and other memo family. No completed body or desired result law is supplied to either kernel.

The first kernel attempt contains a record-update syntax error. Its source and log remain unchanged. The final two integration pairs pass without diagnostics or `sorryAx`. The production module and probe files end with one terminal newline.

This module is a support component for simultaneous prefix admission. It does not establish initial-only recursive query word safety, constructor resource bounds, or general constrained reduction termination. No older proof, Haskell file, Git state, Audit source, or restart authority was changed.
