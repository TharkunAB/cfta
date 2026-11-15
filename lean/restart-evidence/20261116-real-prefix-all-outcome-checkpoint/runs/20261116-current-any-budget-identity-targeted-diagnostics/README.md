# Targeted identity worker diagnostics

Status: UNCOMPILED. The original any-budget worker theorem remains open.

The prior 539-line candidate failed. The log is in `../20261116-native-actual-source-alphabet-anybudget-check/20261116-current-any-budget-identity-alphabet-resource-bundle.txt`. The successful component reached an 8M WHNF limit at the declaration. The Empty component reached that limit at a local first-projection `rfl`. The final worker goal also rejected two result matches that printed identically.

This packet contains two independent small append jobs. It does not contain a new full worker proof.

1. Append `APPEND.lean.txt` to the current owner, then append `COMPONENT-PROBES.lean.txt`. The first theorem checks the prepared-seed alphabet projection without any resource context. The second theorem derives the exact continuing preparation branch from an actual identity-prefix receipt. Its proof generalizes the actual `runWithChild` result, then splits its pair and Option. It retains every original runtime argument. The proof-checking limit is 2M.
2. Independently append `TYPE-ONLY.lean.txt` to the same current owner, then append `TYPE-ONLY-PROBES.lean.txt`. These declarations define the original successful and Empty propositions. They provide no proofs. Unused proof binder names have an underscore prefix. Their premise types and conclusion propositions remain the original types. Each declaration has a 500k proof-checking limit and enables Lean diagnostics. These checks separate statement elaboration from proof checking. Do not count these definitions as proved resource statements.

Do not append the old full consumer or the already published task, scan, or opaque helpers. No additional import is needed for these small jobs. The current owner defines the private resource predicates used by the type-only checks.

The existing `SharedPreparedRecursiveChildPolicy.resume_prepared` theorem at line 260 covers configured outer narrowing. It uses `SourcePruningOuterNarrow.narrow`. It does not directly provide the identity-narrowing equation checked here.

The original public declaration, public header, internal header, prepared header, successful header, Empty header, and original probes are retained byte for byte as reference files. `HEADER-COMPATIBILITY.json` records this comparison. Only the component probes or type-only probes belong in these two diagnostic jobs. The old public probes refer to the still open worker theorem.

If the small projection and type-only checks pass, the remaining 8M failure is in the component proof or its checked term. If a type-only check fails, preserve its diagnostic output before changing a proof. If the operational branch theorem passes, use its exact equality to transport the composed resource receipt in the full worker proof. This avoids requiring equality of separately generated match functions.

No live source, compiler, Git, board, Haskell, or temporary-directory action was performed for this packet. The full finite accepted-completion and single-assignment objective remains open.
