# H8 Haskell baseline count audit

The actual failed checkpoint receipt and complete stderr were read and retained.
The failure is the old count assertion in verify-preservation.py:98. It is not a Lean failure.
H7 starts with 268 .hs paths. H8 starts with 292 .hs paths. No old .hs path was removed.
The difference is 24 H7 metadata snapshots: six archived plan/header/review directories with four files each.
Each directory contains Operations.hs, Memo.hs, Cache.hs, and Type.hs snapshots. Exact paths and hashes are indexed.
The H8 top-level counts are cfta61, cfta-generator111, cfta-ghc13, decision-model5, lean77, specftacular22, and specftacular-ghc3.
The active package count remains 207. The 24 additions are outside those active package directories.
Propose only 268→292 in the current preservation count and current H8 count claims.
occurrences.json identifies all 15 current sites: verifier1, doc updater2, two update texts, nine current doc prefixes, and the focused note.
Keep every historical 268 claim, previous-publication.json, frozen preparation, old audit, and failed input unchanged.
The preservation source retains exact baseline byte/mode checks, tracked .hs set equality, active-package set equality, and disjoint changed paths.
Do not exclude archived paths, ignore mismatches, or change either equality. No Haskell source correction is needed.
The old bound doc updater, preservation tool, current update texts, focused note, failed receipt, and stderr are retained byte-for-byte.
This author prepared the earlier count adaptation. No verifier, Git, network, runtime, compiler, or official edit was executed.
