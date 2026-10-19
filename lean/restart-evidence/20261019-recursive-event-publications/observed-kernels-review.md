# Same-site publication integration

Reviewed 2026-10-19 14:25 CEST.

The selected source is `observed-kernels.lean` (`030de065b2c1d8cefea4aea0d90cd741fc333606c234c14e8f93d6642e2dee91`). The public theorem is `MicroCFTA.ObservedPublicationKernels.nonroot_publication`. It has no supplied premises. The source expression has two ordinary rows. Each row has a distinct used Mu child. Each Mu has a nested used Mu that captures its outer local reference.

The actual outer projection uses path `[0,0]`. Its first branch allocates a new nested Mu record. The selected second branch has source index 1, operand index 1 and read index 0. Its Entry has initial path `[0]`. The resulting observation has remaining path `[0]`.

`pair_site` proves the exact heap from data. The distinct child values exclude source row 0. The two-row lookup excludes larger indices. The actual singleton prefix and `SourceEqualityProjectionAPI.node_unique` fix the selected start at `firstAfter`. This proof does not identify frames by equality of Prop proofs.

`captured` applies `RecursiveEntryPublicationSites.entry` once. It retains that SAME observation and its Site. It proves `observation.before = firstAfter`. The selected key is absent at the initial heap and present at that SAME observation entry. The actual prefix History supplies `Written heap key value`. Initial `closed_history` and the same prefix supply `Written empty key value`. Initial semantic support, availability, costs, plain guards and issued history come from the actual closed source construction. No History is inferred from Grows or Keeps.

The public theorem aliases a private checked theorem with the identical full proposition. The final proposition and all original concrete data definitions are identical to the pre-optimization direct-4 source. The statement comparison receipt checks this identity. Definition transparency and symbolic Site helpers change elaboration only.

Selected checks: `observed-kernels-direct-6` exits 0 with a literally empty log. `observed-kernels-public-1` exits 0 and prints one complete statement/proof/axiom group. All eight required options are present. The hardened checker finds no omissions, warning or error. The only axioms are `propext`, `Classical.choice` and `Quot.sound`. Each of the 11 owned Lean attempts records effective memory.max and memory.high of 4294967296 and memory.swap.max of 0. Every attempt uses the five-minute wrapper cap. The component owns zero production declarations and one constructed theorem.

All failed and partial attempts remain unchanged. Direct-1 and prefix-1 pass only their partial claims. Direct-2, direct-3 and direct-5 retain their exact local proof errors. Direct-4 and diagnostic-2 reach the time cap. Diagnostic-1 is stopped by an exact recorded SIGINT. Diagnostic-3 exposes the missing `Lean.Elab.Command` import for the diagnostic commands and two local proof corrections. The final strict source contains no diagnostic IO. The selected source uses `Elab.async false` and marks concrete data irreducible after its checked computation facts.

The installed pinned Lean source shows why raw stderr can remain buffered: `stderrAsMessages` defaults to true in `Lean/CoreM.lean:581`, and `Lean/Language/Lean.lean:767` isolates command streams. `Lean/Elab/Command.lean:468` also isolates asynchronous command streams. The diagnostic source-pin receipt records exact file hashes and excerpts. The missing diagnostic import is recorded in diagnostic-3. These facts do not establish that imports dominate elaboration time.

This fixture proves a concrete non-root observation and actual publication at the same entry. It does not prove a full class fold, a false primary gate, a full physical observation interval, general observer transport, productivity, termination or Haskell correspondence. It does not convert nested RowAt into an observational Origin.

The manifest uses an explicit allowlist. It excludes mutable peaks and root shared state. `observed-kernels-final-peaks.txt` is the immutable 11-row resource snapshot. No new production or old evidence file is changed. The verifier reuses the final prefix/site source and selected receipts without adding production counts or Lean runs.
