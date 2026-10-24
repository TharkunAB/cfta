# Generated node view test and build coverage review

Reviewed at 2026-10-24 03:24:20 CEST. Upstream input: `c4f7319acf84213fccc8ea389487d4176e4f0b62`, merge PR113, first parent `0db62d26b87e8e55b6c2719f6312ece6f93ed31b`, feature parent `716a145f6178431a37f24464118d5030c9a213f6`. Status: **SOURCE_REVIEW_CLEAR; native validation remains Root-owned**. I read the complete 127-line test, 64-line Cabal file, 73-line implementation and integration diff through `git show`. I did not compile, execute Haskell, merge or change the repository. The host is Linux.

## Exact committed coverage

There is one Cabal test suite, `node-views`, with **four Hspec examples**, six successful top-level derivation splices and five failure checks inside one example. The failures use TH `recover`, so compilation must produce an expression that later evaluates to `True`. They establish rejection, not the diagnostic text. They discard successful returned declarations when constructing `False`; they do not test that those declarations would typecheck.

| Test source lines | Coverage |
| --- | --- |
| 92–100 | Generated/manual typed views have equal cardinality and complete value lists. The language has exactly 38 terms. Every term has the same generated/manual `rankOfValue`, and generated rank/unrank round-trips each term. This is finite concrete integration coverage, not a theorem about all datatypes. |
| 102–106 | Generated/manual scalar-refinement views have equal value lists and equal `unrank` results at indices 0 through 3. The invariant is integer range 0 through 2. This case does not call the refined rank function or separately assert the expected value list/cardinality. |
| 108–114 | Shapes for parameterized record, newtype, named infix constructor and ordered arithmetic alternatives; empty datatype shape; record `nodeFields` preserves its two supplied fields and constructor index. |
| 116–123 | Rejection of one GADT, one constrained existential, one symbolic type name, one type synonym and one generated type-name collision. |

The six successful splices at 80–85 cover `Expr`, `Amount`, `Record`, `Wrap`, `Pair` and `Empty`. An empty datatype has no constructors; it is distinct from a nullary constructor. The design note's separate claims about nine invalid declarations, two-process agreement, README compilation and edit/recompile checks describe earlier validation. They are not additional committed Hspec examples or tests I ran.

## Supported and rejected source forms

Implementation lines 40–60 accept `DataD` and `NewtypeD` with an empty datatype context. They preserve constructor order and arity for `NormalC`, `RecC` and named `InfixC`. They replace every field by the one fresh scalar parameter, drop source parameters/selectors/strictness and emit an ordinary `data` view with `Generic` and `NodeView`. A source newtype therefore produces a data view. No `HasFTA` instance is generated for the source; integration still uses its existing requirements.

Lines 44–55 reject other reified declaration forms, datatype contexts, every `ForallC`, and both ordinary and record GADT forms. Lines 65–73 reject symbolic source type or constructor names and check generated type/value namespaces separately. The committed tests do not separately cover data families, datatype contexts, record GADTs, unconstrained existential constructors, symbolic constructors under an ordinary type name, generated constructor-name collisions, nullary constructors, or copying a strict source field as a plain view field. These are coverage limits, not observed implementation faults. Records of measures remain outside this scalar generator's documented purpose.

## Focused build and test command

From the repository root, under Root's existing serial 4 GiB / five-minute job containment:

```sh
nix-shell --run 'cabal v2-test cfta-th:test:node-views -j1 --enable-tests --ghc-options=-Werror --test-show-details=direct'
```

This command builds the library, splice-containing test module and required local dependencies, then runs only the new suite. The root project selects `ghc-9.14.1`; Cabal bounds require `base >=4.22 && <4.23` and `template-haskell >=2.24 && <2.25`. `shell.nix` supplies Z3, which the scalar-refinement integration needs, but does not supply GHC or Cabal on Linux. Those tools must already be available on the inherited host PATH. `-j1` serializes Cabal jobs; it does not provide the external memory/time cap. No fresh build directory or optimization override is required for this focused check. The repository defaults local packages to unoptimized builds.

The changed files are **root `cabal.project` and `.github/workflows/ci.yml`**. There is no `ci/cabal.project` at this commit. Adding `cfta-th` to project packages includes it in existing `build all`, strict `-Werror` build, `test all` and dependency planning. The workflow also explicitly adds formatting, hlint and package metadata checks. It does not add a new doctest target or release-artifact check for `cfta-th`. The aggregate test command uses optimization 2, whereas the focused command above uses the project's default optimization setting.

## Small additional native smoke

The committed suite is already substantive end-to-end coverage. If Root adds one short external probe, use `data Colour = Red | Blue; $(deriveNode ''Colour)` and assert `nodeShape (Proxy @ColourNode) == Just [("RedNode", []), ("BlueNode", [])]`, `nodeFields (RedNode :: ColourNode Int) == (0, [])` and the corresponding blue result `(1, [])`. This covers two nullary alternatives, their order and the generated phantom child parameter without a solver. A separate expected-failure module with `data Source = C Int; data Occupied = CNode; $(deriveNode ''Source)` should report the **value-name** collision at `CNode`; the existing `ClashNode` example checks the type-name branch only. A data-family rejection probe is a lower-priority third missing branch. Keep expected-failure modules separate from the successful test executable and verify the specific splice diagnostic, rather than accepting an unrelated compilation failure.

No native failure or counterexample is established by this review. Passing the finite examples would not prove general TH hygiene, all rejected-form diagnostics, semantic preservation for every source datatype, or new Lean correspondence. No existing runtime algorithm is changed by this package addition.

## Input identities

| Path at the upstream commit | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `cfta-th/test/Spec.hs` | 127 | 4906 | `96a56edbb5961629be572af4041a86695f098743a196738f8790486571f0ce5b` |
| `cfta-th/cfta-th.cabal` | 64 | 1523 | `41d194a56ea881d3fc03e57de3b3ce09c3e1cd5a8948e5c1e749a5a25aa9427d` |
| `cfta-th/src/Data/CFTA/TH.hs` | 73 | 3196 | `f1c7b9a41f6f897a6ecf1ba7e17afadef4622d94c26c12a02f1d7f5252ac6105` |
| `cabal.project` | 34 | 630 | `74e510696a35b2c624ff7b685a5322e4d2047dacb4d7d6f31ab11d8929469484` |
| `.github/workflows/ci.yml` | 153 | 5205 | `ed3ccf93847129ed42222ca2efc8895209129f2168be70e43aee004cda0178f4` |
| `shell.nix` | 25 | 787 | `0473bdc0b22330870d20db83651b81b4af4d854d7592badb12264576cbee7d08` |
| `docs/generated-node-views.md` | 61 | 3176 | `3bfeb6c685417b3a18de781ab0eb6088db6d2632e9afd40e5b9ea90b022fc1c6` |
