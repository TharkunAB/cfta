# Pure template-oracle helper proposal

Reviewed at 2026-10-24 03:10:34 CEST. Status: SOURCE-ONLY, UNCOMPILED. I read the complete171-line selected source and the complete live Pruning.hs. This is author self-review, not independent approval. No compiler, runtime test, prepared program, repository edit or network operation was run. Root owns compilation and installation.

Selected source: `SourcePruningTemplates.lean`,8359bytes, SHA256 `c527891cb3f90a3b5ced0091c2cbee887ace89ac82431f6418481d6fd73af54c`. Namespace: `MicroCFTA.SourcePruningTemplates`. `Symbol` aliases existing `SourceObservations.Label FullSyntax.Formula`; `PartialTerm` aliases existing `Term (PartialSymbol Symbol)`. The model adds no template, term or symbol datatype and no generic alphabet callback. Existing `FormulaExecutable.formulaDecidableEq` supplies equality. Ordinary literals mean the exact full labels `("app", Formula.top)`, `("filter", Formula.top)` and `("(->)", Formula.top)`.

The complete149-line String proposal and its initial self-review remain under `drafts/` as PRE-FIDELITY history. `String-to-full-labels.patch` records the exact transition. Root identified that native interned Symbol equality includes refinements. String alone would lose distinct fixed-head keys and would recognize refined app/filter/arrow names too broadly. The selected helper keeps every full symbol at stored nodes and in spine keys. Literal recognition tests the entire label, including Top. It does not merely test the text. Native interning, Text and formula representation correspondence remain separate proof obligations.

| Live source | Selected source | Exact interface or behavior |
| --- | --- | --- |
| Pruning.hs41–45 | lines16–25 | Existing full labels, existing partial terms and exact fragment-hole IDs. |
| Pruning.hs347–352 | lines22–25 | fragmentTerm recursively maps nodes, preserves child order and leaves raw hole IDs unchanged. |
| Pruning.hs322–326 | lines27–35 | programs skips filter annotations; an exact ordinary app/4 is first, then function programs, then argument programs. All other shapes yield no programs. |
| Pruning.hs271–278 | lines37–45 | templateSpine follows only exact raw app/4 function slots and ends at an exact node with one child. The returned head retains its complete label. Prefixes/wildcards/unrecognized shapes yield none. |
| Pruning.hs280–285 | lines47–55 | partialSpine uses the same raw shape, with no representative read and no annotation/marker inspection. Holes and truncation cannot fix a key. |
| Pruning.hs260–270 | lines57–68,125–140 | indexTemplates uses position-tagged generic/fixed finite buckets and the ascending-position union described below. Unknown heads retain the original catalog. |
| Pruning.hs334–343 | lines70–90 | structuralTemplate enters only an exact ordinary app/4 root. Internal Hole is allowed. An internal app requires Hole annotation and either Hole or exact ordinary arrow/0 marker. A one-child node requires its sole pattern to be Hole and retains its full label. Other shapes reject. |
| Pruning.hs228–233,239–245 | lines92–107 | isProgramRoot is exactly ordinary app/4 or ordinary filter/2. rejectEarly transforms the original catalog with structuralTemplate, then tests indexed matches over fragmentTerm programs for the exact some[] result. |
| Pruning.hs248 | lines109–113 | startMatches traverses programs first and their indexed templates second; it retains every Option result and duplicate. |
| Pruning.hs249–250 | lines115–118 | finishChecks concatenates resumed before started, drops none, prunes on any empty pending check and retains every nonempty check in order. |
| Pruning.hs235–237 | lines120–123 | order returns the first candidate contained in the raw pending-ID support. It neither sorts candidates nor reads/canonicalizes representatives. |

The requested public functions retain their argument order. `isProgramRoot : Fragment Symbol → Bool` is the one small shared predicate requested by the concrete oracle author; it prevents a second spelling of the early/empty-pending branch condition. `startMatches` returns `List (Option (Pending Symbol))`; `finishChecks` takes resumed results and then started results; `order` takes pending checks and then offered Nat IDs. No Guard parameter, state action, fuel or semantic oracle was added to these pure helpers.

Index construction and container boundary:

- The catalog is tagged by `zipIdx`. The representation stores `(pattern, original Nat position)`, reversing the source pair layout only.
- Generic entries are exactly those whose templateSpine is none. The fixed bucket for a full `(Symbol × Nat)` key contains ALL tagged entries with that key. This retains the source Map.fromListWith IntMap.union behavior when several templates share a head. It does not overwrite the earlier or later entry.
- Each bucket represents a finite position-to-template map through exact position lookup. Original positions are unique even when the templates are equal. A known key uses left-biased generic lookup, then fixed-key lookup. This is the source IntMap.union direction.
- Enumerating `List.range templates.length` gives ascending original positions. This models IntMap.elems of the merged finite map, not `generic ++ fixed`. For fixed entries at positions0 and2 with a generic entry at1, the output remains0,1,2. Equal templates at distinct positions remain repeated.
- If a known key has no fixed bucket, every fixed lookup is none and the result is the generic fallback. If the program head is unknown, the exact original catalog is returned.
- `indexTemplates_known` exposes this exact tagged-union selection equation. `indexTemplates_unknown` exposes the literal fallback. Neither theorem assumes the desired final table. The draft does not claim an additional native IntMap/Map implementation refinement, allocation/cache behavior, bounded Int arithmetic, or a stable-filter substitution theorem. The finite map lookup/ordered-elements abstraction is explicit in the executable model.

No DecidableEq instance for Template.Pattern is required or added. `rejectEarly` distinguishes `some []` by constructors. The arrow-marker test distinguishes the exact literal pattern by constructors and full-label equality. This avoids both global pattern equality and an arbitrary matcher parameter. Generic AnyPrefix[] is not admitted by structuralTemplate. The ordinary app spine tests intentionally do not validate markers: that is the source index behavior, distinct from structuralTemplate.

The remaining lemmas expose only concrete branches: raw fragment hole, filter/app program order, early-hole rejection, empty finishChecks and empty offered candidates. They do not claim template/pruning soundness, observer congruence, full driver equality or convergence. Automatic structural descent and the small simplifier/reflexivity proofs still need Root's Lean check. All calls recurse into finite existing pattern/term/fragment children; no fuel or proof-limit option was introduced.

`source-index.json` pins complete live file byte counts, hashes and line counts, with exact text/hashes for every source/API cut above. The selected source is the proposal; the historical String draft is not an installed or checked source. The existing matcher remains an imported dependency with its current installed hash. No Haskell change or repair is claimed by this package.
