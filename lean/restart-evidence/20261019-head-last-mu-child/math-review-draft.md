# Last selected Mu call: mathematical review draft

Review time: 2026-10-19 14:33 CEST. Weekly allowance check: 3 percent remains. No Lean job was run.

## Existing producers and new content

`RecursiveHeadChainRows.Chain` retains actual union member indices, actual stored-body calls, and intervening Keeps. `Chain.verified` derives current Ready, availability, and closedness. `Chain.warm` derives replay at a forward reader. `Rows` and `actual` recover a chronological terminal ordinary record for each exact physical Head result row. These APIs do not expose the last Mu cut or a suffix without explicit Mu steps. The proposed decomposition adds that missing cut. The focused search found no equivalent last-call producer.

Use `LiteralRootParts.Row`, which traverses root unions only. Do not replace it by structural RowAt or full epsilon Origin. Those relations can cross another Mu and would invalidate the suffix argument.

## Minimal decomposition

A suffix relation needs only reflexivity, literal union-member selection, and advance by actual Keeps. It must retain both heap and value endpoints. Its constructors must exclude an explicit Mu step.

For actual `Chain before root terminal value` and `Row value row`, derive either `Row root row`, or witnesses for all of:

- A prior Chain from the same initial before/root to `muBefore` and the exact selected Mu.
- The exact stored-body execute equation at muBefore, with that Mu's selfEnvironment, returning exposed at muAfter.
- A suffix from exactly muAfter/exposed to terminal/value.
- `Row exposed row` for the same complete selected row.

Induction on the finite Chain suffices. Start gives the initial literal alternative. Member lifts the row into the previous union before applying the induction hypothesis. Advance changes only the suffix heap. At a Mu constructor, choose that actual call and an empty suffix. This is last relative to the selected branch derivation. It is not a unique global last execution.

A suffix advance can include physical Mu work on another collector branch. Therefore a suffix with no explicit Mu constructor is not a global no-publication or NoNewMu interval. Do not infer either fact from Keeps.

## Supported child and Head consumers

The prior Chain's verified facts supply semantic support and availability at the actual last Mu entry. The exact call is definitionally that Mu's unfold. With `History empty reader` and forward growth from its return to reader, `StoredMuUnfoldChildContexts.unfold_child` derives the same selected Mu's Written receipt and Child for its actual stored body. No earlier history is required. Suffix growth followed by the caller's terminal-to-reader growth supplies the needed forward interval.

An actual Head consumer should obtain its branch from `RecursiveHeadChainRows.actual`, then form a literal Row of that terminal node and apply the decomposition. Retain the Head output row index separately from the terminal source row index. Canonicalization can change their positions. The complete row and its selected child index remain unchanged.

Physical publication history is an independent premise. Chain.advance and terminal-to-Head Keeps do not derive it. An empty-rooted reader history can instead come from an actual initial prefix and `RequiredPublicationHistory.head`, with that producer's semantic, cost, and availability assumptions. Do not add a false inference from arbitrary reader Keeps.

## Limits

The strict child size is measured against the actual selected stored body. The result does not identify that body with a current native callback or an initial query operand. It does not bound the returned child or prove a global renewal rank. It classifies the selected branch only, and does not establish a universal derivation or publication-order uniqueness theorem.

This is a read-only design review. The proposed decomposition and consumers have not been independently checked in Lean here. No production source or old evidence was changed.

- `lean/MicroCFTA/SourceCurrentRecursiveHeadChainRows.lean`: `a3528355fd0fc5a021eb50c8c42e9665e029442c92480a7ec413912ef0840587`.

- `lean/MicroCFTA/SourceCurrentLiteralRootParts.lean`: `d2d0bddaf1aa4f3397505ca751915b04ebf190a528c8c27db53255c29cbea4df`.

- `lean/MicroCFTA/SourceCurrentStoredMuUnfoldChildContexts.lean`: `24b36c50bbcf0249d0c7cbf1059607b7e9814e198b011564af211428171bf1cb`.

- `lean/MicroCFTA/SourceCurrentRequiredPublicationHistory.lean`: `92178786551d33349633ef66dc97df3331d474030ff0dbbfb7dad354a88c82f4`.
