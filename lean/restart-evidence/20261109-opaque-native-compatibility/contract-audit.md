# Partial output contract audit

Source inspection only. No code changes or execution. This is not a public Haskell defect report.

The current README states the relevant limit explicitly. `cfta/README.md:443–447` says that a constraint whose paths descend into truncated `Mu` is dropped. A marker term does not establish a nonempty language below that marker. `Enumeration.hs:1185–1186` separately documents that an early partial branch need not have a completion.

## Actual source behavior

- `cfta/src/Data/CFTA/Enumeration.hs:723–732`: `enumerateNode` partitions the supplied suspended constraints. With no terminal endpoint, `Mu` and `InternedUnion` call `addUVarValue (Just n)`. They do not install the supplied descendant bucket.
- `Enumeration.hs:391–396`: `addUVarValue` initializes the new slot as `UVarUnenumerated x Sequence.Empty`. `expandable` at 472–474 excludes a recursive boundary with that empty stored bucket.
- `Enumeration.hs:1046–1054`: `expandPartialTermFrag` produces `TruncatedRecursion` only for a decoded recursive boundary whose STORED bucket is empty. Other pending slots produce `UVarHole`. An empty stored bucket does not prove that the original descendant bucket was satisfied.
- `Enumeration.hs:1057–1082`: `expandTermFragWith` and `expandUVarWith` replace a recursive boundary by the caller's nullary marker. Both functions match any stored bucket.
- `Enumeration.hs:1144–1180`: `termsPrune` delegates to `termsPruneWith`; the latter runs `enumerateFully'` and then `expandUVarWith`. `truncatedTerms` at 1094–1100 instead preserves the explicit `PartialSymbol` tag.
- Synthesis does not call `termsPrune` here. `cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:904–925` uses `runsBy` or `runsNarrowedBy`, selects each run's term, and applies `toProgram`. `Enumeration.hs:1287–1303` shows that their common `runsFrom` also renders with `expandUVarWith`. `toProgram` removes annotation fields; that removal does not itself prove a joint typing completion.

## Existing Lean contracts

`SourcePruningPartialMatchSemantics.lean:14–23` defines the relevant shape relation:

```lean
inductive Completes (assignment : Nat → Term Symbol) : Term (PartialSymbol Symbol) → Term Symbol → Prop where
  | concrete (symbol : Symbol) (partials : List (Term (PartialSymbol Symbol))) (terms : List (Term Symbol))
      (children : All₂ (Completes assignment) partials terms) :
      Completes assignment (.node (.concrete symbol) partials) (.node symbol terms)
  | hole (uv : Nat) : Completes assignment (.node (.hole uv) []) (assignment uv)
  | truncated (partials : List (Term (PartialSymbol Symbol))) (term : Term Symbol) :
      Completes assignment (.node .truncated partials) term
```

The last constructor permits every complete subtree. It supplies no native membership or omitted-equality solution. Raw holes share one assignment; truncation markers do not retain slot identity.

`SourcePruningEnumerationPartialOutput.lean:159–176` already gives a useful positive statement without a model-existence premise:

```lean
theorem rootPartial_complete
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (level : Nat → Nat) (frontier : Nat) (before : State Symbol EnumGuard)
    (safe : Safe before) (stratified : Stratified before level frontier) (inside : 0 < before.counter) :
    ∃ bound observedTerm after,
      (∀ extra,
        Success (rootPartial heap (bound + extra)) before observedTerm after ∧
        ExceptT.run (rootPartial heap (bound + extra) before) = [.ok (observedTerm, after)]) ∧
      RenderStable before after ∧ Frame before after ∧ Stratified after level frontier ∧
      ∀ (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
        (assignment : Nat → Term Symbol),
        Satisfies language meaning assignment before →
          Satisfies language meaning assignment after ∧
          SourcePruningPartialMatch.Completes assignment observedTerm (assignment 0)
```

Here `inside` is the current allocation fact `0 < before.counter`. The actual observation precedes all model observers. No model-existence premise is used. `SourcePruningPartialRenderingSemantics.expandPartial_completes:39` has the same conditional direction. Old `HistoryPartialOutput` is indexed by the old executor and cannot be cast to shared history.

For concrete rendering, `SourcePruningEnumerationRendering.Discharged` at 23 requires EVERY pending slot to have `node = none` and `scs = []`. `render_assignment` at 143 also requires actual rendering and checked residuals. It does not derive discharge from successful recursive truncation. `Language.lean:10–17` explicitly separates finite accepted terms from this enumerator's truncated output.

## Original-source bridge still needed

`SourceSynthesisHereditaryProgramFields.lean:26–52` restricts Program values to Empty or ordinary nodes and retains recursive Program operands. Its Type fields only require `Annotated (Origin lib)`. `HereditaryMemoFields.TypeRow` at 36 similarly retains annotated guards and children. Neither predicate forbids a recursive boundary inside Type fields or proves child-bucket retention. `OriginalCheckedHereditarySharedCompletion.accepted:90` and `SharedPreparedSelectedDriver:180` attach `ValueFields` to the one actual reduced/startup value. They do not supply a retention invariant for every later selected driver child.

The next concrete source theorem is to derive, or refute on an actual original-source route, the existing R208 retention condition for every reached child `(value,bucket)`:

```text
value is an ordinary node OR bucket has a terminal endpoint OR bucket = []
```

This is an internal producer obligation, not a new caller premise. Current role certificates do not discharge it. The generic local countermodel does not establish original-source reachability.

Positive next attachment: extract `Packet.safe` and `Packet.ordered` from the SAME shared output's `OutputResources`, derive root allocation from the actual retained root, and apply `rootPartial_complete` at that output's heap/cache. This constructs finite partial observation and the conditional `Completes` clause without any model input. It does not replace the exact Sized/source objective.

Accepted-source partial semantics needs ONE complete source-accepted term related by `Completes`. Independent marker completions are insufficient: cross-path equalities can be incompatible. Current observation laws do not construct that joint witness. The public `r(Mu,a)` / `TruncatedRecursion` replay is not a verified bad concrete output.
