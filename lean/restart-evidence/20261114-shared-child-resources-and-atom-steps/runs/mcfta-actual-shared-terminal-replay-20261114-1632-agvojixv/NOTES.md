# Exact actual shared terminal replay

Status: UNCOMPILED candidate. Root owns strict checking and publication.
Add only SourcePruningEnumerationSharedCachedTerminalStability.lean.
The candidate adds three public proofs and one private pure list lemma.
Every operational definition and existing proof remains unchanged.

The actual namespace is SourcePruningEnumerationSharedCachedTerminal.

incomingCacheAdapter_some_stable retains the exact successful Unit raw list,
reached caller, saved queries, outer read core and Some cache at independently larger r/n/p/h/k.
It uses actual SharedIncomingNode.run_ok_stable followed by the existing pure
SourcePruningEnumerationIncomingCacheAdapter.adapt_some_stable.
The pure adapter sees the identical reached heap, read core and actual raw result.

raw_ok_stable retains the complete fragment raw list, caller, query memo, outer core and moved waiting state.
It covers both empty rejection and a literal successful singleton.
It uses the same pure TerminalPrefix.run_singleton_stable, the actual rawFold_ok_stable,
and the actual SharedIncomingNode.run_ok_stable.
The raw operation is fully qualified because its name otherwise conflicts with the raw row parameter.

run_some_stable retains that same exact fragment result and the entire Some cache.
It uses actual fold_ok_stable and incomingCacheAdapter_some_stable.
The no-cache incoming path cannot yield the supplied Some cache.
No missing cache is replaced or assumed.
Empty rejection preserves the reached caller, saved queries, outer core, moved waiting state and exact cache.
All five work bounds may grow independently. Recursive depth is not changed or added as an input.

The one private pure map lemma derives a clean incoming Unit row from its actual mapped fragment row.
It handles [] and successful singleton rows and is used by both terminal proofs.
There is no assertion for arbitrary error rows or absent caches in the cached terminal law.
No Context, Packet, semantic invariant, resource certificate, future result or callback provider is supplied.
The current actual observation, clean row condition and bound comparisons are the only premises.

The native and conjunction backend remains the actual Shared backend throughout.
The common pure TerminalPrefix and IncomingCacheAdapter.adapt constants are literally the operations
used by the existing shared kernel. Their existing stability laws are reused without copying them.
The imported IncomingCacheAdapterStability module also contains an older run lift;
this candidate uses only its pure adapt_some_stable and never invokes that older backend.
No legacy terminal, cached terminal, fold or incoming replay theorem is substituted.

Root reported SharedIncomingNodeStability strict PASS with two standard-axiom reports at16:29 CET.
Its canonical source is present and matches the frozen actual leaf byte-for-byte.
The canonical SharedCachedFoldStability source is also present and matches frozen c382da source.
This packet makes no independent compiler or axiom-closure claim for these dependencies or its new proofs.
The source pins identify both canonical modules and their original frozen inputs.

Static checks verify the exact cached successful header shape, actual backend references,
use of only the common pure helpers, absence of new operational definitions and an acyclic import graph.
No compiler, Lake, Nix, heavy job, live edit, Git, board or child agent was used.

Actual SharedSelectedContinuations.ChildDispatch replay and its pointwise resource transport still need
composition above this terminal layer. This packet is not every-budget worker output inclusion.
One finite common accepted original-root term and assignment, parked backward recompletion,
and all original typing, LPO, language, stream, count, weight, rank and compiled-Haskell clauses stay open.
