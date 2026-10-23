# Core review of the main refresh

Reviewed on 2026-10-24 at 00:40 CEST. No core correctness blocker was found by source inspection. No build, test, probe, benchmark, or Lean command was run by this reviewer. H39 remains paused.

The upstream endpoint is `6b62b4afefca80bb05f5a37546212a99980aa3df`. The previous imported endpoint is `794903b3fbad3becb8b28736fc33463760731fc7`. The pre-merge formalize endpoint was `d501c53489b4ba9a41fd178c7ccdd0bf530dcde7`. The current merge is `78904be72914616af4bf41046ab27f65a60c6142`.

The complete upstream diffs for Enumeration.hs, Template.hs, Equality.hs, EqualitySpec.hs, and ADR 5 were read. Their changes are respectively +104/-38, +19/-9, +2/-1, +0/-1, and +36/-0 lines. Surrounding implementation and the specific Lean statements below were also read. This is not a claim to have manually read all 34 upstream changed files. References below use the current merged files, which match this upstream endpoint for these five paths.

## Enumeration behavior and obligations

`cfta/src/Data/CFTA/Enumeration.hs:912-919` now expresses the old driver as `enumerateUntil' Nothing`, identity narrowing, and the same eager `enumerateNode`. The repeated-recursion path remains. This supports the old complete-result behavior. One operational detail changes: `981-991` rejects an empty narrowed node before the pre-expansion oracle; the old driver called that oracle before the failed empty-node expansion. A literal source equation that includes that callback must be updated, even if successful terms agree for terminating observing callbacks.

The new public `termsPruneUntil` at `1168-1193` uses shallow expansion. Each eligible ordinary child can become a separate UVar choice. Narrowing runs before the pre-expansion oracle. A replacement retains the same suspended constraints (`981-989`). The stop test runs first and checks every entry in the expandable index, including blocked entries (`960-972`). Caller state is retained separately on each nondeterministic branch.

A precise counterexample to an incorrect complete-acceptance claim is:

```
termsPruneUntil () noExpansionPreference (\_ _ n -> n)
  (\_ _ -> True) keepEverything (EmptyNode :: Node Symbol)
== [Term.Node (UVarHole (intToUVar 0)) []]
```

This is source-derived and has not yet been executed. The stop test accepts the initial root before the empty-node check. The partial renderer returns its unresolved root hole (`1018-1046`). The API explicitly permits a partial term with no completion (`1177-1178`). It is intentional behavior, not an identified implementation defect.

New correspondence work must cover the stop/index condition, shallow child deferral, replacement with suspended constraints, and partial rendering. A no-stop/identity bridge must distinguish successful complete runs from partial results. Callers must justify their own narrowing and rejection rules. The new shallow API can expose different callback events from eager `termsPruneWith`, so arbitrary stateful oracle behavior is not interchangeable between them.

## Exclusion memoization

`cfta/src/Data/CFTA/Template.hs:184-208,243-279` creates one `refined` closure for an exclusion and memoizes `(wanted, unwanted, node)` within it. Prepared-template equality, ordering, and hashing all use the same catalog identifier. Each closure captures its own catalog and projection functions. No global table was introduced.

This scope is necessary: distinct catalogs can assign the same identifier to different templates. A shared process-wide table keyed only by these identifiers would be wrong. The selected code keeps those catalogs separate. The existing finite/total-template and consistent symbol Eq/Ord requirements remain at `177-179,214-232`.

ADR 5 records this design at `docs/adr/0005-exclusion-memo-per-application.md:15-18`. Its allocation and runtime figures at `24-26` are upstream measurements; this review did not repeat them. The unchanged `Interned/Memo.hs:58-62,81-93` allocates a cache for the evaluated memo application and uses the existing pure-result insertion path.

One small documentation issue remains: `Equality.hs:78-87` describes the memo tables collectively as process-global and never released. That wording does not distinguish this local exclusion cache. `Interned/Memo.hs:52` also calls `memo` process-global despite its scope-dependent allocation documented at `8-11`. Clarify these descriptions if documentation is changed. This is not a merge blocker.

`Equality.hs:114-123` only adds the public `intToUVar` re-export. EqualitySpec removes its corresponding internal import. The constraint algorithm is unchanged in this core diff.

## Existing Lean correspondence

The merge does not modify the Lean models. Their existing theorems keep their stated scope. `lean/MicroCFTA/EnumerationDriver.lean:487-514` specifies an observing oracle and the prior eager caller equation. `EnumerationExact.lean:76-85` proves finite-term support for its modeled complete runs under `CompleteGraph` and `IntersectionCorrect`. Neither statement establishes acceptance or extendibility of the new early-stop holes. A literal search found no `termsPruneUntil`, `enumerateUntil`, or `enumerateShallowHere` model in `lean/MicroCFTA`.

The complete-term pattern relation in `Template.lean:65-105` and ordered split result in `SourceTemplateShapeSplits.lean:135-157` still concern the same matching/split semantics. They do not prove the new mutable-cache lifetime or catalog-key isolation. Those require a memo transparency and same-catalog key argument. No whole-library, Haskell-refinement, or new full-pass claim follows from this refresh.

## Focused verification handoff

The smallest useful addition to the existing EqualitySpec pruning/template checks is `/tmp/mcfta-main-refresh-20261024/CoreIntegrationProbe.hs`. It has nine assertions: finite no-stop identity, no-stop empty rejection, speculative early-stop empty hole, actual child narrowing, annotation-only stopping, and four checks for exclusion catalog separation and closure reuse. It uses only public APIs and compares term multisets. It does not claim recursive, blocked-equality, performance, or concurrency coverage.

Probe SHA256: `243e0779fe8f8d8c6d95492194d17c4b74e28cc21ccfaf94cb1d5da18ddc4cf1`.

The probe was written and read completely but was not compiled or executed. No direct `termsPruneUntil` test was found in `cfta/test`. Root owns the current unit/golden jobs and any probe execution. Existing green suites alone would leave the new stopping cases unchecked. A later equality-constrained narrowing case and constrained-recursion case would extend coverage if this new path is formalized further.
