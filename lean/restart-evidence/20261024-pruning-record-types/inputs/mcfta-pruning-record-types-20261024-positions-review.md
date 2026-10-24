# Pruning position helper review

Reviewed at 2026-10-24 04:05:30 CEST. Status: **SOURCE_HELPERS_CLEAR**. I read the complete 188-line author proposal in two untruncated cuts, native Pruning.hs147–213, relevant symbol/raw-UVar definitions, existing canonicalIds contracts and the complete author self-review. I then read Root's complete repair delta to the selected 201-line source, SHA-256 `d5504f3e508afd8d1eab5619bcf78b6693733dae8918f26de3c7e531d47ab605`. I did not author either version, run Lean or native code, edit repository files or mutate Git. Compiler acceptance remains Root-owned.

All three definitions use the existing Fragment, PartialTerm, Term and full `SourcePruningTemplates.Symbol`. Ordinary app/4 and filter/2 tests compare complete `(name, Formula.top)` labels. Refined lookalikes take fallback branches, and output concrete labels keep refinements. Native literal construction and the constructing direction of `Symbol` produce ordinary Top labels. Native pattern-synonym projection and interned-identity equality remain extraction details; they do not justify dropping refinements from literal tests.

`typePositions` matches every native branch. A raw type-position hole inserts that ID using `canonicalIds (uv :: types)`; a program-position hole returns the original list. Type-position nodes fold all children as types. App/4 retains the nested annotation/marker type fold around the function/argument program fold. Filter/2 applies its program child's result as the annotation accumulator. Every other symbol/arity treats all children as types. The exact nested foldr expression is a pure source correspondence, not a claim about strict evaluation order in lazy Haskell.

The existing canonicalIds definition erases duplicates and sorts ascending. Its membership, Nodup and sorted contracts support the new insertion theorems. It is used **only at a type-hole insertion**. Other branches retain the actual input list. Native IntSet fidelity requires a canonical ascending unique input observation and a separate complete-helper preservation argument. The candidate's global output is not asserted canonical for arbitrary malformed list inputs; its current sorting/Nodup theorems concern insertion. No global `typePositions_canonical` theorem is claimed.

`programHoles` preserves raw IDs, order and multiplicity. An incoming type position contributes none. A raw program hole contributes its singleton ID. Ordinary app/4 concatenates function holes before argument holes; filter/2 visits only its program child. Other shapes contribute none. There is no representative lookup, sorting or deduplication. The repeated-hole equation explicitly retains `[uv, uv]`.

`openProgram` models native openProgram, not the stricter openTypes. Type holes become ordinary `?`; program holes become ordinary `?program#` plus `toString` of the same Nat ID; truncation becomes ordinary `Mu`. Hole and truncation branches ignore their children exactly as native openProgram does, including malformed partial terms. Concrete type nodes map all children as types. Ordinary app/filter program nodes use the exact mixed child positions; other shapes map all children as types. All concrete labels and output child order remain intact.

The program-hole equation is literal in this Nat/string model. Native signed-Int `show`, Text packing and nonnegative representable Int/Nat extraction need a separate formatting bridge. It is not established by the `toString` equation. Truncation is only a marker observation; it does not establish successful completion below recursion. This helper makes no source lexical, native overflow or interning-extraction claim.

All 22 public statements and their proof bodies were read. They expose actual branch equations, insertion membership/sorting/uniqueness, ordered hole membership, duplicates and concrete marker/fallback rendering. They add no abstract callback, state action, graph query or new typeclass instance; existing formula equality is only enabled locally. These are finite helper observations, not typing, pruning or language-preservation theorems.

Root's 188→201-line repair changes recursive partial applications to explicit eta-expanded map/foldr lambdas, adds `termination_by sizeOf fragment` and `termination_by sizeOf term`, and repairs equation-proof elaboration. Reversing exactly the eta expansions and two measure lines recovers the entire original definition prefix byte-for-byte. Every one of the 22 theorem headers is byte-identical. The recurrence, source branches, fold/map order, arguments and outputs are unchanged. The public programHoles definition is unchanged. The termination declarations express descent on the actual finite input; they add no fuel, callback, success condition or output premise. I make no claim about the eventual compiler result from this source review.

The frozen owner remains the unchanged 188-line proposal with SHA-256 `3ca5e05619e3b65f7dcd26acae4d90aec3708d734c0ec4903e907f9a8d16e201`. Its exact 16 safe relative payloads and complete recursive file set passed read-only byte/hash checks, excluding only top-level `pins.json` and `FROZEN.json`. All eleven retained cuts match their complete live-file hashes and original line slices. The selected repair does not overwrite that owner history. A packaging identity guard stopped before report creation when it noticed the selected path had changed; I inspected and checked the repair delta before this final report.

No source correction is required at the reviewed helper hashes. This supports the concrete recordTypes wrapper's use of typePositions. It does not prove typedTypes, openTypes's runtime-error exclusion, narrowing, stopping, native mutation histories, a partial term's completion or semantic pruning. The native representation boundaries and any later canonical-preservation proof remain explicit.

## Exact reviewed inputs

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| `/tmp/mcfta-pruning-record-types-20261024/SourcePruningPositions.lean` | 10985 | `d5504f3e508afd8d1eab5619bcf78b6693733dae8918f26de3c7e531d47ab605` |
| `/tmp/mcfta-pruning-positions-20261024-proposal/SourcePruningPositions.lean` | 10499 | `3ca5e05619e3b65f7dcd26acae4d90aec3708d734c0ec4903e907f9a8d16e201` |
| `/tmp/mcfta-pruning-positions-20261024-proposal/pins.json` | 2279 | `0ea3ffaebbdd0eb9c40a8946c6e257bf0e61a2abb5e1ddb8547e42b86723ee57` |
| `/tmp/mcfta-pruning-positions-20261024-proposal/FROZEN.json` | 488 | `17d0598dde01ddc0e08770e8bc897124d3b31ce7e2963e559186b66fe2892203` |
| `/tmp/mcfta-pruning-positions-20261024-proposal/source-index.json` | 4965 | `cc90189b2e404b2622ae6692cd225c407dbc752cb169bfe9a2bb1b31ffaee282` |
| `/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs` | 16989 | `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` |
| `/home/tritlo/Code/mcfta/lean/MicroCFTA/EnumerationBuilderCaches.lean` | 27843 | `f4882be07a73362a667a994f9e37344b9fb4619565dcf53ca0e857ecd21ccb9d` |
