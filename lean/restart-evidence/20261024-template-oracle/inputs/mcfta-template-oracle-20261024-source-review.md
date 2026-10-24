# Actual templateOracle source review

Source-only assessment at 2026-10-24T03:08:37+02:00. I read the complete live Pruning.hs219–350 helper/oracle region and reused the exact reviewed matcher/resume identities. No compiler, selected execution, repository edit, Git mutation, network or board operation occurred. This is a source/schema review; the forthcoming drafts still need complete source review.

## Required branch and result obligations

| Source branch | Exact result and effects |
| --- | --- |
| `Right node` | Pure `(False, original pending)` for every pending list; ignore the node payload. Do not render, resume or normalize current. |
| `Left fragment` with `rejectEarly` true | Pure `(True, original pending)`. This branch precedes the next fast path. It does not return the filtered pending list. |
| `Left (TermFragmentNode symbol children)`, empty pending, and root not exact ordinary app/4 or filter/2 | Pure `(False, [])`. A raw UVar fragment with empty pending does NOT take this branch: its rendered value can contain a new program match. |
| Remaining `Left fragment` | First run actual full `expandPartial`; then the full ordered traversal of `resume current partial` over every existing check; only then construct new pure matches and combine them. Return exactly `(any null checks, filter (not . null) checks)`. |

Here `started` enumerates `programs partial` in program order, and for each program enumerates the actual indexed candidates in catalog-position order. `checks = catMaybes (resumed ++ started)`: old resumed checks precede every new match. `none` removes an unsuccessful template match; it is not a pruning flag or an action failure. `some []` is a completed match and makes the returned flag true. Nonempty checks remain, in order and with duplicates, even when another check sets that flag. An incoming empty pending check is not silently discarded before its resume read/traversal. All stateful reads precede the final pure check combination, including when an early part yields none.

The expansion-order helper is also literal: make a membership set of the raw IDs in all pending pieces, then return the first supplied candidate whose raw ID is in that set. Deduplication changes only membership lookup. It does not reorder candidates, alter pending, normalize either ID, or provide scheduler equivalence from Frame alone.

## Exact finite candidate index

Use original position tags, with templates tagged 0 through length-1. The generic finite map contains exactly entries whose `templateSpine` is none. Each fixed-key map contains all entries with that complete key. Repeated fixed keys merge their disjoint position maps; repeated equal templates at different positions remain distinct. Source `Map.fromListWith IntMap.union` combines by position, not by template equality.

For a known head, select the matching fixed bucket (empty if absent), take the left-biased union `generic UNION fixedBucket`, and enumerate its values by increasing original position. Arity's agreed representation uses finite-map lists plus private position lookup and enumerates positions0..catalog.length-1. That is an explicit executable representation of the constructed source maps. It must not become `generic ++ fixed`, a set of template values, or an arbitrary candidate callback. For an unknown head, return the entire original catalog in its original order. A stable catalog filter is a useful extensional theorem, not an unproved replacement of the indexed construction.

Example: catalog tags `[0:fixed-g, 1:generic-a, 2:fixed-f, 3:generic-b, 4:fixed-f]` yield `[1,2,3,4]` for known f, `[1,3]` for an absent known head, and `[0,1,2,3,4]` for an unknown head. The two fixed-f values remain twice if equal. Left bias is exact, although generic and a constructed fixed map cannot share a tag. Mathematical Nat tags/counts model ascending non-overflowing source Int positions/counts; this adds no native Int width or native container extraction proof.

## Pure helper details

- `templateSpine` descends only exact raw TemplateNode ordinary app/4 through its function child, increments the spine count, and finishes only at an exact one-child TemplateNode. Other nodes, wildcards and every prefix form give none. Annotation and arrow-marker contents do not constrain this raw spine test. A one-child head can itself have the text app; it is not an app/4 descent.
- `partialSpine` performs the corresponding descent through concrete ordinary app/4 terms, and ends at a concrete one-child head. Holes, truncation and unsupported shapes give none. Keep its output key family distinct from a pattern value.
- `programs` unwraps exact filter/2 into its program child. Exact app/4 returns that whole application, then programs from its function, then programs from its argument. Every other shape returns no programs. It does not traverse arbitrary children or annotations.
- `structuralTemplate` accepts only an outer exact app/4 template. Its recursive program helper accepts Hole; an app/4 with annotation Hole and marker either Hole or exact ordinary (->)/0; or an exact one-child symbol with annotation Hole. It preserves full constant labels and changes only accepted app markers to Hole. Other patterns fail. In particular, generic AnyPrefix[] is not admitted as an early template, even though the actual matcher accepts it unconditionally.
- `fragmentTerm` is the pure ordered constructor map from immutable fragments: concrete symbols stay complete, and each raw hole becomes a hole leaf with its original ID. It performs no representative read or expansion. `rejectEarly` considers only app/4 or filter/2 roots, then tests whether any early candidate has matchPartial result `some []` on any listed raw program.

Do not require new Pattern equality. The source comparisons `matchPartial ... == Just []`, marker membership, and `null` can be represented by exact Option/list/constructor cases. They inspect no equality of opaque template values. FormulaExecutable supplies the existing structural equality needed for full symbol/key comparisons.

## Full symbol correction and existing proof route

The initial String-only plan loses a material source distinction. Native `Symbol` is interned Text plus a refinement Formula. Equality is full-symbol equality; its `Symbol text` pattern view alone does not establish that text is an injective encoding. Root corrected the plan before final drafts: use existing `SourceObservations.Label FullSyntax.Formula`, aliased as SourcePruningTemplates.Symbol, and existing FormulaExecutable equality. The ordinary app/filter/arrow literals are exactly `(name, .top)`. A refined label with the same name is not that ordinary literal. Fixed head keys, partial terms, pending patterns and returned constants must retain the full label. Any preliminary String draft is historical, not the final alphabet. Native interning, Text encoding, container implementation and machine-Int bounds remain separate correspondence boundaries; no new symbol datatype is needed.

Instantiate the existing `EnumerationState.Oracle` with this full Symbol and the outer pending-check list. Use the SAME immutable graph, catalog, supplied fragment/event, raw current and pending input for a paired observation theorem. Pure branch selection is then identical. The stateful branch composes existing expandPartial_frame/agrees/transport/moreFuel with SourcePruningResume's four properties and ordered stateful-list composition. Transfer left Total after the actual render and each actual resume through their complete frames. Finite right transport must start each resume at the actual constructed right render/previous-check endpoint. A common right bound can be the sum of the separately constructed render/traversal bounds, raised by existing Retains lemmas that keep exact intermediate states. Never assume equal original fuels across different forests or restart a tail at the initial state.

The resulting observer contracts can preserve complete Frame, agree on exact `(Bool, List Pending)` results at independent successful bounds, construct finite right success from one actual left success, and retain exact endpoints with more fuel. No Safe, Finished, canonical-current, desired right-success, arbitrary callback-congruence law or pruning-soundness premise is needed. Uniform left Total is sufficient for the read-composition proof, but does not by itself prove arbitrary rendering termination.

These are callback behavior and observation contracts. They do not prove that early marker erasure is semantically safe, that a completed partial match rejects only unwanted completions, that LPO-produced templates are valid, or that the driver/phase4 implementation refines the model. The actual caller's app/4 type-constructor guard is separate evidence for its encoding discipline, not an extra silent behavior inside the helper. Complete native mutation histories, cached-driver composition and typing/pruning soundness remain open.

## Exact live input identities

The source review reads are bounded as recorded below. Previously fully reviewed model modules are identified by full hashes; these hashes do not claim a new full manual proof-body read.

| Source | Full bytes / SHA256 | Relevant cuts / SHA256 |
| --- | --- | --- |
| `specftacular/src/Specftacular/Pruning.hs` | 16989 / `5970dd7d9e67bb925fbd079921768ac08dc91d1c34e9ecfbc3d59795f0287f61` | 219–250: `2e1ac73753911a7c03b9e248ba33a36b7bc5095a0422056743712d34cb2c3deb`<br>253–286: `855a3749944dabfa53709a64a54062fd1440ce8e73ec8465c307a8f962a21b42`<br>289–297: `101d4649504a7070ff4238b2e29a49000b3dd89e530a2ecfb78387ecc490aeee`<br>303–322: `a5abf4b1246a0f5f78cf9452d3c70497378a024e69d31ba7be2cfd5443fb5889`<br>325–350: `10f3415e59eaddc0307861ef196bbc28191b99c360a4b5a44ce092670087abde` |
| `cfta/src/Data/CFTA/Symbol.hs` | 5657 / `31983078475d136d2e69f5d94461f56f7c2fa3b3822144be1eee324ba0637f02` | 1–85: `762e37043b9b94fef9ee31eb87759e18303ae796c7335de2b6e4383aebf58aab` |
| `specftacular/src/Specftacular.hs` | 77825 / `b5a19e8c83908ff2de3cf3ee704731733224d96f36b7fb597afcd0fa017dbace` | 1048–1051: `fbfeb0801048f8e35b58c4cf2a421f0d7b4479ac01722bb6db93416006ef1fb3` |
| `lean/MicroCFTA/SourcePruningPartialMatch.lean` | 3692 / `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` | 1–90: `08c3662ac9bc664eb809448522505834105fb173b05971a432f9741c2e275509` |
| `lean/MicroCFTA/SourcePruningResume.lean` | 15277 / `593d1b84050ba85d130f32a57947be90374b29f66ca9a649a1070855757d024d` | 38–48: `86fc6aee94a827c3fb332d370dad0863607466c8f4deb48afea9a7b16d586e2e`<br>178–240: `6b6bdacadc836530168cd0837f71abb686a338854b0a8da867829936a026b0a9` |
| `lean/MicroCFTA/EnumerationState.lean` | 33489 / `83a898b883ec7b52469bccd87e8afa4f7abb320e3c935bf48f3d80ad77003cc4` | 296–299: `7f85be7142aaa58064c981230203fc2b0da8fd865e29dc53e3f6668ae637d0f5`<br>334–355: `8f7c1137d887dc5a5f886eeed7b3a33515552c96cb494ffaafcb48c71ed21037` |
| `lean/MicroCFTA/SourceObservations.lean` | 8738 / `3f65467c7cc9e15921dc5ea9e6173ade0f431054844ca1250079440ed5410cc8` | 12–15: `31da894eb6ce58777c453f8e81317447e2c328df796e125c04f3518e7e674a21` |
| `lean/MicroCFTA/FormulaExecutable.lean` | 5638 / `5d164443fe3dd60d9b1eff44a132aa97c649bd199e1930b5d1a64f14859a5af3` | 12–24: `246b3c73445cf68c528f589fe0a69257b99334953b364b4f7ebf72e80691e7fd` |
| `lean/MicroCFTA/EnumerationPartialCongruence.lean` | 9302 / `7452999a98756fdb92be845b4eb52f08926c5a12ce9c42752df1333d457bcb60` | 71–79: `d8e9e1fe447f718bc6027f64be853c0e44d828524f6e0e65c78a066281d48d5d` |
| `lean/MicroCFTA/EnumerationPartialTransport.lean` | 9581 / `cfb86bcdf59c125625bb78f0fea7da467789adc162f27c4f1a4e45f630b5674c` | 36–44: `ca36914f8f8695ad530c5470f9d92bd4e4bd33338cb9db2cfc387ffcf7976017` |
| `lean/MicroCFTA/EnumerationPartialObservation.lean` | 4692 / `e407fa36087e6f5521dbd2da098aa49d1fe37817f16a2c9d32227d56153e67bc` | 64–69: `05d4215a8b37d71b7de8f620101b8ceacbefbf86e81833cec0955ac72436f278` |
