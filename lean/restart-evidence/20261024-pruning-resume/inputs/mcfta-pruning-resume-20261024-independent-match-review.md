# Independent partial matcher review

Review time: 2026-10-24T02:48:36+02:00. Status: SOURCE_CORRESPONDENCE_CLEAR after the two reported keyword escapes. The original candidate has the known unescaped `prefix` proof-case syntax at lines 73 and 88. This review did not execute either candidate, invoke a compiler, edit the repository or change either input.

Read scope: all 90 lines of the original candidate, its complete two-line delta to candidate2, the complete live Haskell `matchPartial` function, and the term/template/symbol representation cuts below. Candidate2 is byte-identical to the original after exactly replacing the two proof-case names with `«prefix»`. Its executable matcher and theorem statements are unchanged. I did not author this matcher.

The pure executable behavior matches the source on finite, fully defined inputs under the constructor-preserving term/template encoding, the same encoded raw UVar IDs and symbol-equality correspondence. This is a source review, not a proved Haskell-to-Lean simulation theorem.

| Case | Source and candidate behavior |
| --- | --- |
| `Hole` / `.hole` | Accept every shape with no pending entries, including raw holes with children and truncation. This branch has first priority. |
| `AnyPrefix []` / `.anyPrefix []` | Also accept every shape with no pending entries. This branch precedes both hole suspension and truncation rejection. It is not restricted to concrete nodes. |
| Raw UVar hole with no children | Suspend the exact original pattern and exact raw ID, unless one of the preceding two branches already accepted. No representative lookup, normalization or pattern simplification occurs. |
| Raw UVar hole with nonempty children | Reject unless one of the preceding wildcards accepted. The empty-child shape check is intentional and matches the source fallback. |
| Truncation with any children | Reject except for the two preceding wildcard cases. A symbol-specific empty prefix is not an unconditional wildcard. |
| Concrete symbol with an exact-node pattern | Require the same symbol when specified and exactly equal child counts. AnyNode omits only the symbol check. Wrong symbols and wrong lengths reject before child matching. |
| Concrete symbol with a prefix pattern | Require the same symbol when specified and pattern length no greater than child length. Match only the requested initial children. Ignore every extra child, including an extra malformed or truncated subtree. |
| Child mismatch or truncation within the matched prefix | Reject the whole match, unless that child's own preceding wildcard case accepts. A zero-length prefix consumes no child. |

The private mutual helper has the right source behavior. Its `[], _` case returns `some []`; its cons/cons case recursively matches the first pair, then the remaining pairs, then returns `first ++ rest`; its nonempty-pattern/empty-term case rejects. At every public call, the exact/prefix length guard has already checked admissibility. Therefore it implements the source's `concat <$> zipWithM matchPartial parts children` without padding the unused prefix tail with new pending entries. Pending entries keep left-to-right, depth-first child order. Duplicate patterns and duplicate IDs remain duplicated. Failure is `none`, not successful empty pending.

All four displayed theorem statements agree with those branches. The raw-hole and truncation theorems explicitly distinguish `.hole` and `.anyPrefix []` before the remaining patterns. Their constructor case splits require the reported escaped name only; no semantic premise or theorem result needs a repair. Termination/elaboration and strict-linter acceptance remain compiler matters owned by Root.

The source `CT.Node` pattern exposes every native term constructor as its root symbol and ordered child list. The Lean tree has that same structural view and no imposed arity. The three partial-symbol tags remain distinct from real symbols. This review does not equate native `Int`/UVar representation with arbitrary `Nat`, cover partial or infinite Haskell values, equate allocation or evaluation costs, or establish native serialization/interner correspondence.

No semantic correction is requested. The only observed correction is the already planned two-name keyword escape. This matcher does not access the enumeration state. It establishes no root-canonicality fact, pruning soundness/completeness, language preservation, typing theorem, driver equivalence, callback congruence or callback transport. Those require separate contracts and proofs.

## Exact inspected identities

Full-file hashes below identify the live inputs. Cut hashes preserve original line endings.

| Input | Full bytes / SHA256 | Lines / cut SHA256 |
| --- | --- | --- |
| `/tmp/mcfta-pruning-resume-20261024/SourcePruningPartialMatch.lean` | 3684 / `e772e0c7bcbd30ecc33a560b1d1cee63cd9afd22990557f74fd1e737ecd2274d` | 1–90: `e772e0c7bcbd30ecc33a560b1d1cee63cd9afd22990557f74fd1e737ecd2274d` |
| `/tmp/mcfta-pruning-resume-20261024/SourcePruningPartialMatch-v2.lean` | 3692 / `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` | 1–90: `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` |
| `specftacular/src/Specftacular/Pruning.hs` | 16989 / `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` | 302–322: `b914141a3f364484e8a1dbea2b148d220aee87261d34654825d81f8be668c0b0` |
| `cfta/src/Data/CFTA/Template.hs` | 34297 / `0acb6104d585454ee23c848b8e909b9e4f2f7f613a330b729c29af3681edc150` | 59–74: `b273aea839b1590d208a01edd480ecf6ec78a55211b214684d94c4768f4305bf` |
| `cfta/src/Data/CFTA/Term.hs` | 10184 / `9201ca9e5f7a7a5dc89b3737b71e406c2245cec2a36aa68ae32fb3eef8572e3f` | 87–113: `0ab1f3b52575930bc9f87db6b0ebeb6401b2a00de824f95270b5535fa5249663` |
| `cfta/src/Data/CFTA/Enumeration.hs` | 71269 / `949c484539483f0e646b069899be127a57f0897353b24b92e51a5d90654cec07` | 126–135: `b3a29ce6e068f620d9df6166fa8e7fa1858522daec5b4b752309844a31312d05` |
| `lean/MicroCFTA/Template.lean` | 11254 / `67abebd52ddc3320afd88a142e46b92b357c9bb7947efd7e290976a1cd5530d8` | 16–22: `1a0ed22b6cd8b863b86481c498e024ba1d39f75a30882552745b193efb3b2dbb` |
| `lean/MicroCFTA/EnumerationState.lean` | 33489 / `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 334–339: `65cde8c85b18d7700b79708e4d6cc47769bfa833845d33f0c2e99729477a7665` |
| `lean/MicroCFTA/Language.lean` | 24311 / `fd78e01d01a4894a6580be076e3fdee877d171ca1d31525876cc2539386573fc` | 22–25: `f6e0e3fdf4508af2a4e5e3dd7fe084098f3bb661540fc096105541cb7afde520` |
