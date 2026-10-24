# Pure partial pruning matcher review

Reviewed at 2026-10-24 02:43:45 CEST. Status: SOURCE-ONLY DRAFT REVIEWED. The complete90-line candidate was read. It has not been compiled, imported or executed. No Haskell or repository file was changed. This is author self-review, not independent approval.

Candidate: `SourcePruningPartialMatch.lean`, 3684bytes, SHA256 `e772e0c7bcbd30ecc33a560b1d1cee63cd9afd22990557f74fd1e737ecd2274d`. The namespace is `MicroCFTA.SourcePruningPartialMatch`. The only data alias is `Pending Symbol := List (Template.Pattern Symbol × Nat)`. Public `matchPartial` takes `[DecidableEq Symbol]`, then an existing `Template.Pattern Symbol`, then an existing `Language.Term (EnumerationState.PartialSymbol Symbol)`. It returns `Option (Pending Symbol)`. It has no Guard parameter, state action, fuel, arbitrary matcher argument or semantic oracle. The mutual child helper is private.

The exact source-to-model map is:

| Source | Candidate | Preserved behavior |
| --- | --- | --- |
| Pruning.hs42–45 | lines12–18 | Pending aliases the existing pattern and raw hole ID; partial terms reuse existing types. |
| Pruning.hs303 | line20 | Hole accepts every term without inspecting its shape. |
| Pruning.hs304 | line21 | Empty AnyPrefix accepts every term, including truncation and malformed holes. |
| Pruning.hs305 | line22 | Only a raw hole leaf suspends the remaining exact pattern and original ID. |
| Pruning.hs306 | line23 | Truncation rejects unless one of the two earlier wildcards already accepts. |
| Pruning.hs307–313 | lines24–35 | Concrete nodes use the same exact/prefix and symbol tests. |
| Pruning.hs315–317 | lines24–29,38–46 | Exact matching checks equal arity before ordered child recursion. |
| Pruning.hs318–319 | lines30–35,38–46 | Prefix matching checks sufficient arity and ignores only trailing children. |
| Pruning.hs320 | line36 | Other shapes reject, including nonempty raw-hole children for nonwildcards. |

The child helper traverses requested pattern/term pairs in order. It stops on the first rejected match, then appends each earlier child's pending list before the rest. This is the pure Option equivalent of `concat <$> zipWithM matchPartial`. Its empty-pattern clause accepts any remaining child list. The caller's exact-arity guard prevents that clause from accepting extra children for exact patterns. The prefix-arity guard prevents too few children. Extra children remain unexamined for prefixes. No duplicate is removed.

The concrete symbol test uses `expected = symbol`. Its symmetry with the source's equality test introduces no additional assumption beyond decidable symbol equality. A symbol-specific empty prefix remains symbol-specific: unlike `anyPrefix []`, it suspends on an unresolved hole and rejects truncation. An exact empty any-node pattern likewise remains nonwildcard. These distinctions follow from the top-level clause order.

Four public branch lemmas are included at lines49–88: `matchPartial_hole`, `matchPartial_anyPrefix_nil`, `matchPartial_rawHole`, and `matchPartial_truncated`. The latter two expose all wildcard exceptions instead of adding assumptions. Their proofs use constructor cases and reflexivity only. They introduce no relation, datatype or state observation. The matcher itself is sufficient for a later resume proof: equal actual partial terms give equal pure results by substitution. No pruning-soundness theorem is claimed here.

Recursive calls use finite term children and their ordered lists. The public/private mutual shape follows the existing `Template.matchesTerm`/`matchesChildren` definitions at Template.lean84–98. Automatic termination and elaboration remain unverified until Root's compiler review. There is no fuel workaround or proof-limit option.

`source-index.json` records the exact live full-file bytes, hashes and line counts, plus complete text/hashes for every cited API cut. Its Pruning cut also includes the actual resume definition at lines287–297, solely to fix the future consumer interface. It does not implement resume, callback traversal, representative reads, observer congruence, full driver behavior, template soundness, or native runtime behavior.
