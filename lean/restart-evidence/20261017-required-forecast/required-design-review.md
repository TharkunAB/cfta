# Required forecast source and boundary review

Checked on 2026-10-17 at 12:21 CEST. The current restart heads describe the full-library goal. This component implements one pure resource forecast. It does not construct an actual Required resource bound.

## Literal schedule

- `SourceEqualityRequiredGraph.lean:28–39` gives node branch priority. Empty requirements return before value inspection. Ordinary nodes visit rows before `makeNode`. Mu and union heads run actual Head exposure, then the same requirement on the exposed ordinary node.
- `SourceEqualityRequiredGraph.lean:42–66` visits existing children in order. Unselected children stay unchanged. A kept row visits children, rebuilds its exact symbol and raw guard with `makeEdge`, then visits the row suffix. A missing required index rejects the row before child work. `RequireChildren.length` at line 70 preserves arity.
- `SourceEqualityRequiredWorker.lean:43–86` implements that schedule. Sibling scans reuse worker fuel. Recursive Head exposure consumes one worker layer before the ordinary phase. Worker depth and executed instruction count are different quantities.
- `SourceEqualityNeeded.lean:17–40` defines and validates the finite trie. Child requirements are structural subterms. `fits` at line 133 checks signed keys. `negative_key_boundary` at line 199 shows why an arbitrary signed negative key must not be treated as a natural index. `SourceEqualitySelectedRequired.paths` at line 22 converts canonical natural paths to signed paths, and `paths_nonnegative` proves the conversion property.

## Existing initial endpoints

`SourceCurrentRequiredWorkerNumeric.workFuel` at line 21 is `2 * sizeOf needed + 1`. Its `node`, `children`, and `requireAll` endpoints are at lines 130, 183, and 198. They replay the same actual graph with this worker depth. Reader fuel remains existential.

`SourceCurrentConstrainedCapSelectedRequiredWorker.complete` and `.caller` are at lines 30 and 60. They construct their own selected Required call from initial supported facts. They retain actual reads, the full Required receipt, Frame, caps, length, and caller Post. They do not return forecasted Fits or an initial numeric reader ceiling. The earlier `SelectedRequiredComplete.complete` and `.caller` at lines 34 and 69 supply the initial completion route that these worker wrappers reuse.

`SourceCurrentConstrainedCapSelectedRequired.node/children/rows/requireAll` at lines 175, 183, 191, and 203 retain local caps and causal guard stores through supplied actual graphs. These verifiers do not supply initial numeric resource bounds.

## Open Head support

Selected support does not require all roots to be closed. `SourceCurrentRequiredTipSupport.NodeTips` and `.ForestTips` at lines 23 and 29 describe only demanded tips. `selected_domain` at line 94 derives them from the original false primary gate. `ordinary_rows` and `head_rows` at lines 109 and 124 propagate them at actual branches.

`SourceCurrentSecondaryProjectionSupport.Support` at line 115 permits either a closed value or an available value with an actual false secondary trace at its anchor. `support_warm_head` at line 120 derives `SourceSecondaryGateHead.WarmHead`. That predicate, at line 23, permits an open ordinary value and same-heap Mu unfolding prefixes before an ordinary, empty, or closed suffix. It does not permit arbitrary open recursive execution.

The new `SourceCurrentOpenRowReadResources` supplies the required quantitative envelope. For scalar `q`, its definitions at lines 27–33 are:

```
readFuel q   = q + old.readFuel q + 1
readWidth q  = q + old.readWidth q
readGrowth q = q + old.readFuel q + readWidth q
headGrowth q = primitiveGrowth (readWidth q) (readGrowth q)
```

Here `old` is the closed reader resource module. Same-heap prefix identities lie in the initial issued inventory. A closed suffix uses the existing controlled collector. `complete` at line 230 constructs its own read. `read`, `read_ready`, and `head` at lines 250, 264, and 275 transfer exact actual graphs and replay certificates. The Head theorem requires WarmHead support and initial physical facts. It does not require global Closed.

The older `EditFrame.head` at line 153 and `ProjectionUnionResources.head` use closed inputs. The final Required forecast therefore defines a new Head profile from the new open `headGrowth`. It does not reuse the older closed Head profile.

## Implemented pure recurrence

Let `scalar p` bound node supply, edge supply, and stored payload mass. Domains stay unchanged in Head and constructor profiles. Define:

```
H p       = open Head profile at scalar p
C k p     = existing constructorProfile k p
S p       = join (H p) (C (scalar p) p)
P 0 p     = S p
row l W p = S (scan (P l) W p)
P (l+1) p = let start := S p; W := scalar start;
            S (scan (row l W) W start)
```

The numeric row and child limits are fixed at each entry. They do not depend on future heaps or actual returned profiles. The component reuses the generic `EditForecast.scan` arithmetic at lines 235–305. It does not create a dummy class record or a future leaf law.

The final module proves growth, component monotonicity, syntax-level monotonicity, exact successor equations, initial Head and constructor inclusion, and every scheduled row and child entry and return inclusion. These are static logical profiles. They are not executable allocation measurements or whole-library budgets.

## Next actual proof

Use an initial level at least the structural requirement size. Obtain original row and child widths from initial causal Stored plus availability and residency. Keep these original counts while states grow. A rejected row pays no actual work and fits by inflationarity. A kept row composes selected child calls, exact raw-guard reconstruction, and the suffix. The final node reconstruction fits the last stage. An ordinary input widens its initial Fits to the stage without executing a synthetic Head. A recursive input uses its supported actual Head, then the ordinary phase. Child requirement subterms decrease the finite level. A forest wrapper scans the original root count.

This actual node/children/rows induction is still open. It must derive Fits at each reached state and combine all actual reads under one initial reader ceiling. It must retain the full Required receipt and Frame at the same returned inventory. The pure inclusion lemmas do not assert these reached physical facts. No reached numeric bound, future successful execution, result Cap, or recursive callback law is assumed by this component.

Initial gate, seeded-query, Scan, complete outer resources, arbitrary constrained Mu, convergence, adapters, and full public Haskell correspondence remain separate obligations. Finite all-root Cap assumptions remain stronger than the full live source gate. No Haskell file or behavior claim changes here.

## Validation and prior envelopes

Final source: `SourceCurrentConstrainedCapRequiredForecast.lean`, SHA `aaed86ccba8696345bdf874b1504fda619516bcf28993a4f3eba6376b0c06354`, 207 lines. Immutable strict snapshot 4 checks with all linters and an empty log. Canonical build 2 passes 1520 jobs. Its replayed ClosedCompletion warning belongs to an older dependency. The owned source has no diagnostic.

There are 24 imported public signature/axiom pairs and two pure integration pairs. The first derives room for the exact new open Head profile, a constructor, and a scheduled child return from one final plan reservation. The second combines initial profile and level weakening. Both leave majorants symbolic. Only standard axioms occur.

Snapshots 1–2 and canonical log 1 retain the earlier pure closed-Head envelope. Snapshot 2 SHA is `6c172d30cd5052e9683b1fecc32587d78ad93b7403dedccfe7ab690041b2243a`. It is historical evidence, not the final open-support forecast. Snapshot 3 records a deterministic elaborator timeout after widening the Head profile. Explicitly unfolding only the profile and order removes that timeout in snapshot 4. All failed snapshots and raw logs remain. Historical hashes refer to their immutable snapshot paths, never to the final production path.
