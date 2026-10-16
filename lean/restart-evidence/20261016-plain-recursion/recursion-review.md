# Plain Region recursion: independent interface review

Reviewed on 2026-10-16 at 15:43 CEST. This is a read-only source and proof-interface review. No Lean or Haskell build was run for this review. The new final node induction was not present when the interface was reviewed.

The proposed node-only induction is sufficient. No circular completion premise occurs in `SourceCurrentAllocatedPartialPlainRecursionDefs.Below` (line 37). It permits only requests with strictly smaller `nodeRank`. Its `NodeResult` (line 28) returns the actual graph, strict source reads, reached checks, full `Post`, available result, structural returned-domain invariant, and candidate `NodeLaw`. It does not require a future graph or result law. The final theorem must construct `Below` by strong induction. The helper theorems alone do not prove that it holds.

## Minimum interfaces and constructor paths

Use one fixed ceiling `R` in the internal helpers. Carry `ActiveAbove (R - 1)` through every ordered prefix. The child-rank condition is independent of inherited payload identity because `nodeRank` reads only the node value.

| Helper | Additional input facts | Actual constructor path |
| --- | --- | --- |
| Walk | `Values`, child `Region`, each child node rank `< R`, ready combined payload, `Context`, `Stored`, fixed active ceiling, `Below R` | `Walk.nil`; for cons, literal indexed descent, smaller `NodeCall`, then suffix at the returned caller and index + 1 |
| Children | Same child facts and ready combined payload | `.contradiction` erases slots at unchanged caller; `.live` uses Walk from index 0 |
| Descendants | Resident returned edge, Regions and rank bounds of its returned children, inherited ready | Actual inherited-first prefix, Children at its returned operations, literal same-arity raw rebuild |
| Rows | Resident original rows, `Region.Rows`, each original edge rank `< R`, inherited ready | `.nil`; for cons, independent finite EdgeCall, Descendants of its returned edge, then original suffix |
| NodeCall | Available Region input, inherited ready, initial `Context`, structural `Stored`, active above its own rank | Actual ready hit; or actual evaluate owner, constructed body, then finish the same handle |

All sixteen raw constructors have a path: two NodeCall, four NodeBody, two EdgeCall, one EdgeBody, two Rows, one Descendants, two Children, and two Walk. The source-read constructors and `PartialChecksComposition` constructors match these exact graph endpoints. They do not require a supplied future result.

For an evaluated node of rank `R`, derive the actual stored owner's value equality and Region with `PlainInputs.node_evaluate`. Derive its running context with `CallSteps.node_start`. `ActiveOrder.node_push` supplies `ActiveAbove (R - 1)` at that literal running caller. Construct its body by cases on the owner's Region. Do not apply the induction hypothesis to the same-rank body.

Empty and explicit union stop. Mu also stops traversal, but its source pattern reconstructs Mu. `PlainTerminal.complete` derives the actual rebuild from initial resident probes through `MuRebuild.resident_rebuild`; it returns cleanup at the same caller. Do not replace cleanup by the original Mu value. An ordinary body constructs Rows and then the literal ordered `RawRebuild.modify` branch.

## Rank and active-owner checks

`ActiveOrder.edge_lt_node` (line 44) gives each original ordinary row rank `< R`. Thus its rank is at most `R - 1`, and `.mono` supplies the premise of the already independent `PlainEdgeCall.finite` (line 74). No edge-call induction hypothesis is needed.

That call returns `Shape original narrowed`. `Shape.regions` and `Shape.height` in `PartialReturnedDomain` give Regions for the narrowed children and their height bound. `child_lt_edge` (ActiveOrder line 53) then gives every returned child node rank `< R`. This includes nullary original edges that return the singleton Empty sentinel. No equal-arity claim is valid for the parent stage. Same arity is needed only between the narrowed edge and its descendant rebuild; `Children.length` supplies it.

After each completed child, edge, or descendant prefix, use its actual `ActiveFrames.NoNewActive` to restore the SAME ceiling `R - 1`. Carrying only the child's weaker active bound can block the next sibling. `NoNewActive.activeExcept` (line 46) proves this restoration without a future completion premise. Natural subtraction causes no gap: a nonempty helper's rank hypotheses exclude `R = 0`; an ordinary node has rank at least 3.

Active-bound transport and owner survival are different obligations. `NoNewActive` is reverse inclusion of evaluating cells. It does not show that an earlier evaluating cell still exists. Exact parent-owner survival uses forward `PartialFrames.node_body` (line 273), with `Protocol.of_valid` from the derived running context. `CallSteps.node_finish` (line 104) already uses that frame to recover the SAME evaluating owner and finish its handle. No additional owner-survival premise is needed in `Below`.

## Structural and physical state checks

The new `ReturnedDomain.Stored` is separate from `Context.stored`, which concerns the merge-result memo. Return and thread the new invariant explicitly. It is needed for warm edge hits and is not a consequence of semantic `EdgeLaw`. Empty outer tables derive it. `beginNode`, `finishNode`, and lower checked advancement retain it. A completed edge evaluation installs `Shape` at its literal captured owner.

Only the parent EdgeBody result is stored in the edge-result table. Descendant rebuilding happens afterwards. Do not require the final descendant-rebuilt row to have `Shape original final`, and do not overwrite the edge cache with it. Output node Region and height descent are also unnecessary: the traversal does not recursively visit its newly returned node in the same pass.

`PlainPrefixes.descent` and `.inherited_prefix` derive actual completed allocation results and full `Post`. They retain the exact two outer result tables, `Stored`, and arbitrary active exclusions. Old-tail residency and inherited readiness must grow through the actual prefix effects. Each child starts at the literal descended payload and its actual returned equality operations. No state, native table, fourth memo, merge memo, or global bundle is reset.

Reusing `PartialActual.walk/children/descendants/rows` AFTER constructing their exact graphs, strict Reads, and Checks is not circular. Those theorems verify a supplied completed graph. They do not construct the missing smaller calls. The reviewed `PlainRows` draft follows this order, restores the fixed ceiling before each suffix, and threads the new structural `Stored` separately.

## Source correspondence and remaining scope

`cfta/src/Data/CFTA/Equality/Operations.hs:80-96` memoizes the node request, stops at Empty/union/Mu, then maps parent reduction followed by descendants in original row order. Lines 93-96 use the RETURNED edge's children and combine inherited constraints FIRST. Lines 143-145 erase on contradiction and otherwise use positional descent. Lines 160-168 memoize only the parent stage. The proposed graph follows that schedule.

Region requires effective `PhysicalPayload.own guard = .ok (some [])`, not only an empty raw equality field. `PlainInputs.own_empty` performs the actual accessor inversion, including positive-guard equality extraction. This is the necessary link to the independent finite parent endpoint.

No material interface or lifecycle defect was found. The remaining proof action is to discharge `Below` by strong node-rank induction and derive literal stable execution from each constructed graph. This review does not establish that action. General constrained completion, repeated-pass termination, runtime thunk publication/concurrency, GHC forcing, and native host-container correspondence remain separate.
