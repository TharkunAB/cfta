# FirstOrder defaults and the shared prepared driver

Read-only source audit, 2026-11-11 19:34 CET. No source edits or builds. Four focal files: Gen/Synthesis.hs, Data/CFTA/Enumeration.hs, SharedPreparedSelectedDriver.lean, SharedPreparedRecursive.lean. Other references are their exact execution or policy dependencies.

## Public source route

`cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:904-914`: FirstOrder programRuns selects runsBy(spaceOrder), then decodes each run's term and tracks previously emitted Programs. `cfta/src/Data/CFTA/Enumeration.hs:1253-1256,1285-1294`: runsBy captures canonicalEdgesOf(Just weight) at spaceNode; runsFrom initializes enumeration, calls enumerateFully, renders root UVar 0 with marker "Mu", and renders residual obligations.

The exact defaults are Enumeration.hs:913-927: Unit client state, noExpansionPreference, callback returning `(False,state)`, no stop rule, identity narrowing, and **enumerateNode as expansion function**. These are not Specftacular typedTypes defaults.

## Parameter and state map

- **Typing/key:** choose Unit and `holeKey := fun _ _ => ()`. The source default has no client typing operation. `SourceSynthesisOriginalFiniteDriver.initialMetadata:46` permits `initialMetadata () [] []`, meaning empty pending/type/open lists. These are additional modeled metadata fields, not fields of Haskell Unit.
- **Templates/graph:** choose `templates := []`. Any well-typed dummy EnumerationState.Graph can be supplied because `SourcePruningRecordTypes.recordTypes_empty:76` eliminates the oracle branch. Graph contains node/intersect functions (EnumerationState:51); this does NOT authorize an empty native heap or replacement of the current actual caller.
- **Admission/fitness:** choose both functions constantly true. NativeView.keeps then retains every exposed row. PrefixCoverage.keeps_of_accepted:18 and narrowAt_accepting:78 provide the accepted-term direction without source-specific policy hypotheses. This proves semantic retention, not literal identity narrowing: NativeView.narrowAt:36 still calls nodeEdges and makeNode; Action.prepare:17 can replace the stored handle. OuterNarrow.narrow_mu/narrow_type:24,35 are actual identity cases. No inspected theorem identifies the complete constant-true narrowing call with Haskell's pure identity at every physical endpoint.
- **Stop/selection:** choose stop=none and `order := fun _ _ => none`, not typesLast/atTypes. Restart.decision:13 selects PureSelection.next; PureSelection.find/next:165-172 subtract waiting representatives. Haskell nextExpandableUVar:863-877 picks the least ready IntSet member when the preference is Nothing. Existing pure selection/cache correctness laws justify the modeled index behavior; identifying source IntSet/IntMap/UnionFind observations still requires a representation relation.
- **Callback:** recordTypes_empty is exactly pure `(false,{metadata with types := updatedTypes ...})`; recordTypes_inr:83 is pure `(false,metadata)`. RecordTypes_metadata:89 retains typing/openHoles. Thus false verdict and unchanged enumeration core are already proved for empty templates, but Left recording can change metadata.types. Forgetting this ghost field can represent the Unit callback; equality of the entire callback result is not valid.
- **Root/cache:** Haskell initEnumerationState:297-311 creates UVar 0 with the supplied node, empty constraints/obligations/waiting/ancestry, and its expandable flag. Modeled startup at OriginalFiniteDriver:50-53 uses EnumerationState.initial plus the same-shaped flag and empty waiting. Nodes.encodeNode/lookupNode:16-35 provide actual native-handle readback. They do not equate those Nat handles with Haskell NodeId. SharedPreparedSelectedDriver.start_selected:72 starts at a GIVEN successful root; run_selected:93 first performs a shared nodeCall, which is a separate operation to relate to source reduction before programRuns.
- **Row order:** map spaceOrder to the edge-weight function, not the hole preference. SourceCurrentEnumerationOrder.canonicalEdgesOf:30 and canonical_perm:80 formalize a root map plus per-node fallback and weighting. SelectorLanguage.canonical_accepting:56 obtains an accepting selected edge under the ACTUAL row permutation. Neither the resource theorem's one-sided selection assumptions nor a raw interned-row getter proves the required weighted source root-map correspondence.
- **Empty checking:** Haskell captures `_constrainedRecursion = reachesConstrainedMu root` at initialization (Enumeration.hs:311,555-562). Shared checkEmpty is explicit; a truthful adapter must produce this flag for the SAME root, not pick an arbitrary constant. Native checks use currentTupleBudget=10000 (SourceCurrentConjunctionTupleBudget:17), matching Enumeration.hs:663-664 numerically. Native heap/query/memo behavior is a further correspondence obligation.

## The expansion operation differs

Haskell enumerateFully' passes enumerateNode at line 927. enumerateNode:720-754 selects an ordinary row; enumerateEdge:757-777 calls enumerateEdgeWith **enumerateNode** on every child. Ordinary descendants therefore expand recursively inside this edge action, before its outer Left callback.

The modeled route is literal and different:

1. SharedPreparedRecursive.resume:150-154 calls SharedPreparedContinuations.run.
2. Its ordinary branch at SharedPreparedContinuations:76-80 calls SharedSelectedContinuations.NativeContinuations.run.
3. In that file, NativeContinuations.run:619-636 calls CapturedEdge.run:523-531, then SelectedEdge.run:455-467.
4. SelectedEdge calls ChildTraversal.run:211-220, which calls ChildDispatch.run:64. Its nonterminal observe branch at 46-59 calls ShallowChild.prepareChild:15-33.
5. That operation allocates an unenumerated ordinary child and returns a hole. The ready-hole loop expands it later.

The Haskell shallow helpers are **used**: enumerateShallowHere/prepareShallowChild:788-808 are supplied to enumerateUntil' by the public termsPruneUntil API at 1198-1201. They are not the expansion function of enumerateFully. Specftacular.Pruning.prunedPrograms:95-97 calls that shallow API; its typedTypes client remains a separate, richer callback. No equality between typedTypes and recordTypes follows.

## Observable limits and next proof

General equivalence cannot ignore callbacks, preference, or early stop. Static example: on ordinary r(a), an eager Left callback sees r(a), whereas a shallow Left callback sees r(?uv). A legal callback that rejects fragments containing holes distinguishes them. A stop predicate that accepts only positive UVar IDs can also distinguish a newly deferred child from eager completion. A preference receives different available-hole lists. These observations follow from the definitions; no runtime replay was performed here.

Even with the default no-op policies, erasing metadata does not establish equality of the ordered run list. Deferring descendants can change which sibling's choices are enumerated first. Decoding and Program deduplication occur after enumeration; they cannot be assumed to restore order. A claim about ordered output needs its own proof.

The smallest honest next bridge is a finite **default-policy deferral simulation**: relate the SAME current root and equality-variable assignments; turn one accepting eager ordinary-child expansion into actual shared shallow steps followed by finite ready-hole resumptions; preserve rendered finite terms and obligations under erasure. Current native effects must remain at their actual shared endpoints. This can support term membership/coverage before any stronger ordering claim. Common selected preparation already implements the analogous Mu unfolding/Union row construction (SelectedValue.run:19), but its exact native execution must also be related to Haskell enumerateOutUVarWith:888-910.

Work/recursive fuels remain modeled observation bounds, unlike the single fixed emptiness budget. Adequacy for a successful finite default observation must be derived, not inferred from arbitrary-depth resource completion. Rendering the shared cache, residual obligations, and programRuns' decoding/deduplication also remain part of the public adapter.

This is a model/runtime adapter gap, not evidence of a production behavior bug. All current statements about actual execution continue to refer to the literal shared Lean workers. No old Prepared execution, completed model, future Context, or future successful trace supplies this missing correspondence.

## Check this source snapshot

Run `python3 lean/restart-evidence/20261111-default-driver-operation-boundary/check.py`.
The checker verifies all recorded source hashes. It does not run Haskell or
prove an execution equivalence. No production Haskell change is proposed.
