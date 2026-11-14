# Prepared shared path origins: normalization repair

Status: UNCOMPILED. The root agent owns validation.

The public theorem header is byte-identical to the typed-index repair.
The complete inputs, conclusions, endpoints, and conjuncts are unchanged.
The header SHA-256 is c8be2113d8160aaa00001012d5f1399dfc9cf98de645784aa334d171ab8d5bff.

The previous private check reported three normalization errors. This packet
makes exactly three proof replacements:

- Add `Function.comp_def` when simplifying the composed staged child maps
  and the bucket projection.
- Add `Function.comp_def` when simplifying the complementary partition
  predicate.
- Use `rfl` for the projection conjunct. The actual projection case split
  has already rewritten that goal to a reflexive equation.

The inverse replacements restore the complete previous source bytes. No
premise, provider, conclusion, endpoint, or linter setting was added.

The public candidate remains:

`MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.prepared_terminal_child_written_path_origins`

The source and target audit remains in:

`lean/restart-evidence/20261114-current-prepared-shared-written-path-origins-draft/NOTES.md`

The full emitted-root finite completion and compatible assignment target
remains open. This theorem covers one actual prepared child and its actual
shared write. Preservation through a later recursive clear remains open.
No Haskell defect or change was established.

No compiler, live source, Git, board, Haskell, or temporary evidence was
changed. Both earlier frozen packets remain unchanged.
