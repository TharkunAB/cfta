# Actual source callers and the two emptiness gates

Status: FROZEN READ-ONLY CORRESPONDENCE AUDIT. No Haskell or Lean compiler, test, executable, benchmark, or heavy job was run. There is no new theorem credit, runtime change, or reachable-source defect claim.

## Result

The Haskell `checkEmpty` value is not a public option with a true or false default. It is the persistent `_constrainedRecursion` field, initialized to `reachesConstrainedMu` of the actual enumeration root. Even when that field is true, a second `reachesConstrainedMu` test on the actual new intersection can skip `provablyEmpty`. The second gate is already present in Lean. The missing caller correspondence is the first gate's specialization, rather than a missing inner check.

For the original raw FirstOrder source, the only possible recursive binder is the computed allTypes universe, whose body is unconstrained. Ordinary application and generalized-scheme equalities outside that binder do not make this detector true. The source structure therefore gives a false initial root gate. The existing checked Lean source ownership/guard laws cover every accepted signed size and current catalog; a header-only corollary for the exact root Boolean is frozen separately as UNPROVED. A reduced/refolded public Space must use its own actual root; this audit does not transfer the raw-root Boolean across those transformations without proof.

Neither enabling both gates nor receiving a successful singleton establishes native inhabitance. The emptiness algorithm is conservative and budgeted. Direct nullary Marker-versus-original-Type mismatches also have an independent syntactic native-intersection rejection route, so a skipped check is not evidence of an accepted-source defect.

## Public Hectare route

[programsIn](/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:969) calls `runsBy (spaceOrder space) "Mu" (spaceNode space)`. FirstOrder [programRuns](/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:949) uses the same function. The curried specializations may use runsNarrowedBy, which also reaches the same initializer. These functions expose no checkEmpty parameter.

`solutionsOfSize` first builds [orderedSearchSpace](/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:774). That route applies reduceWithOrder to rawSearchSpace. reduceWithOrder uses bounded reductions, and orderedSpace then refolds the resulting graph. Thus its enumeration root is the transformed `spaceNode`, not automatically the original raw graph.

[Enumeration.runsBy](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:1253) delegates to runsFrom. [runsFrom](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:1285) calls initEnumerationState on THAT root, then enumerateFully and the original root readback. Edge weights affect ordering; they do not override the root gate.

[initEnumerationState](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:297) sets `_constrainedRecursion = reachesConstrainedMu n` at line311. The only two reads of this field in the file are the actual assimilateUvarVal and mergeNodeIntoUVarVal paths, at lines501 and520. No later write to this field was found. Persistent state copies keep it.

## Optimized partial Program route

[Specftacular.Pruning.prunedPrograms](/home/tritlo/Code/mcfta/specftacular/src/Specftacular/Pruning.hs:85) invokes termsPruneUntil with the real type-position stop rule, narrowing, and typing callback. It has no checkEmpty option. [termsPruneUntil](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:1188) calls the SAME initEnumerationState on its supplied root.

The actual optimized caller [skeletonParts.typingsOf](/home/tritlo/Code/mcfta/specftacular/src/Specftacular.hs:1289) supplies `pruningRoot = preparePruning (refold space)` to prunedPrograms. It uses startTyping, extendTyping, constantFits and typeAdmits, then reconstructs typings with generalizeCarriersWithin. This is an actual typing/filtering route, not a generic empty-check switch. The other bucket route uses prunedTerms, which reaches runsInterned for no templates or termsPruneWith otherwise. Both also use initEnumerationState.

[defaultOptions](/home/tritlo/Code/mcfta/specftacular/src/Specftacular.hs:505) does not contain an emptiness flag. Its searchChecked option is not this native gate. No inference from that separate flag is used here.

The optimized root may have undergone reduction, refolding, compiled pruning and mergeTypeAlternatives. Its gate must be read from that actual graph. This audit does not establish that every transformed Specftacular root has only the original U binder, nor that every optimized output corresponds to the raw formal root without the existing transformation correspondence obligations.

## The two gates and the Lean mapping

[intersectUVarValue](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:204) intersects the two actual stored native nodes. Its emptyIfProvably branch replaces the result by EmptyNode only if ALL of these hold:

1. The persistent original-root checkEmpty field is true.
2. `reachesConstrainedMu newIntersection` is true.
3. `provablyEmpty newIntersection` returns true.

No semantic emptiness call occurs in this operation when either gate is false. When one old native handle is absent, no binary native intersection or optional emptiness call is needed.

[reachesConstrainedMu](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:555) tests cached recursive depth before the tag. At a Mu it returns `not (unconstrained mu)` and does not enter that binder. It traverses union members and ordinary children. Constraints on an ordinary ancestor are not themselves a reason for a true answer. [unconstrained](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:545) visits stored bodies and requires empty equalities and no residual at every reached ordinary edge.

The corresponding existing Lean layers are:

| Haskell operation | Existing Lean operation |
| --- | --- |
| Initial `_constrainedRecursion = reachesConstrainedMu root` | The engine's explicit checkEmpty Bool; the intended caller specialization is `SourceEndpointReachability.reaches SourceMemoGate.unconstrained rootValue` |
| Per-intersection reachesConstrainedMu test | `SourceEndpointMemo.run query queries` inside SharedEnabledEmpty.check |
| Depth/Mu/unconstrained/union/ordinary traversal | `SourceEndpointReachability.reaches` and SourceMemoGate.unconstrained |
| Conditional provablyEmpty call | SharedEnabledEmpty.check invokes the actual shared conjunction worker only after the query gate |
| True emptiness answer becomes EmptyNode | SharedIncomingNode.run chooses `.empty` when the phase returns true |
| Reject literal EmptyNode contents | IncomingNode.finish rejects the literal `.empty` replacement |

[SharedEnabledEmpty.check](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationSharedEnabledEmpty.lean:31) already executes the second gate. [SharedIncomingNode.run](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourcePruningEnumerationSharedIncomingNode.lean:74) first consults the externally configured checkEmpty Bool. [SourceEndpointReachability.reaches](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEndpointReachability.lean:16) has the exact corresponding structural branches. There is no claim that this read-only code comparison is a newly proved complete Haskell/Lean state correspondence.

[CurrentProgramEagerOutputs.accepted](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentProgramEagerOutputs.lean:44) quantifies checkEmpty at line53 and forwards it to the worker. It does not derive the actual Haskell initial root field. Specializing it to true without an actual caller derivation would change this correspondence.

## Raw accepted FirstOrder coverage

The only-binder assertion has checked source-wide support, rather than a sample-size argument:

- [CurrentUniverseOrigins.firstOrderRaw_overUniverse](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentUniverseOrigins.lean:62) quantifies every accepted lib/query/signed/whole. Its OverUniverse syntax consists of ordinary nodes/unions over the single computed allTypes atom.
- [CurrentUniverseOwnership.current_build_single_universe](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentUniverseOwnership.lean:286) lifts this to the actual original empty-heap build. It permits no resident Mu, or one exact replayable original U value; every resident Mu equals it. The source expression need not contain U.
- [CurrentSourceGuards.firstOrderRaw_guards_plainMu](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentSourceGuards.lean:320) gives clean top-only Mu bodies for the same fully quantified accepted source.
- [current_stored_universe_rows](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentUniverseOwnership.lean:332) retains the exact original top-guarded U body, marker, catalog rows and recursive references.

The corresponding Haskell [allTypes](/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:475) is one Mu with unconstrained arrow/variable/catalog edges. Generalization installs scheme equalities around its ordinary outer pattern and leaves an inserted Mu intact. rawSearchSpace builds the finite Program syntax around these types. Source constructor escaping applies for arbitrary catalogs, and signed-size acceptance does not introduce another source binder. This explains why the raw root gate is false despite application equalities outside U.

The prospective original_root_reaches_constrained_mu_false header has only accepted source and its actual original build as logical premises. It remains UNPROVED in this packet. The Haskell initialization equality is visible code; the named exact Lean root specialization still needs its small source-physical proof. Neither fact is transferred to reduced/refolded Space here.

## Conservative emptiness and finite membership

[provablyEmpty](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Enumeration.hs:604) explores at most 10,000 edge tuples. Open queries and unexplored/budget-overflow conjunctions count as possibly accepting. Its documented contract is one-sided: true certifies emptiness, false proves nothing. The Lean [currentTupleBudget](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentConjunctionTupleBudget.lean:17) is also10000. [AnswerSound](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceCurrentEmptinessMemo.lean:28) states only the true-answer rejection law. It supplies no finite member for a false answer.

Normal, syntactic non-Empty, and unconstrained are distinct from finite inhabitance. [Normal](/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedStoredMuOrigins.lean:24) packages physical facts, live edges, flat unions and proper member shapes. [StoredNonempty](/home/tritlo/Code/mcfta/lean/MicroCFTA/InternedNonemptyRecords.lean:17) requires nonempty ordinary edge lists and proper union lists; it imposes no productivity condition on a Mu. A generic recursion marker can denote no finite term, as the already checked EnumerationState.recursion_marker_not_acceptance shows. That generic example is not an accepted-source defect or a counterexample to the original U's four productive variable alternatives.

Two existing exact finite-member routes are useful:

- [DonePendingTypes.done_pending_type_members](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentDonePendingTypes.lean:84) gives every finite TypeIn choice at the SAME actual pending handle from actual done/cache validity, Normal, UnionNormal, source growth and each actual pending value's only-original-U atoms. Its closed Mu/union classification includes the original productive U. The actual source history must derive that only-U fact for each relevant endpoint; it is not supplied by the emptiness flag.
- [ColdProductivity.prechecked_table](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceFreshOrdinaryColdProductivity.lean:33) gives a computed exact structural productivity test from genuine semantic/readback heaps and availability/closedness. The test's TRUE result is equivalent to a finite structural term. It does not derive that true result from syntactic non-Empty. For actual guard membership, [PCSConstructors.plain_true](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceEqualityPCSConstructors.lean:37) supplies guard truth in a genuine gate-plain region; source/current preservation of that region and productive boundaries still matters.

No checked generic `Normal + closed + unconstrained + value != Empty -> finite native member` API was found. It would need a productive-boundary restriction. These two existing routes are evidence-backed alternatives to a new role wrapper; neither is silently treated as already producing a joint model of all historical buckets.

## Nullary Marker intersections

The genuine source Marker is the unconstrained nullary `"(->)"` node. The original U's root alternatives are the arrow head `"->"`, four variable heads and escaped catalog heads. The Marker is a CHILD of the U arrow, not a root Type alternative. Rigid Type heads have the same separation by [escapeConstructor](/home/tritlo/Code/mcfta/cfta-generator/src/Data/CFTA/Gen/Synthesis.hs:435).

For these exact original operands, native intersection can reject structurally: [intersectOpen](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Operations.hs:488) unfolds the Mu as needed and ordinary operands use the same-symbol hash join. No matching Marker root edge means no output row. [mkNode](/home/tritlo/Code/mcfta/cfta/src/Data/CFTA/Interned/Type.hs:582) converts that empty edge list to EmptyNode; mergeNodeIntoUVarVal/assimilateUvarVal then reject it by hasEmptyContents. This route does not require provablyEmpty. Matching the exact source Marker against itself instead reuses the same closed node and its nullary Top row has its concrete finite Marker member.

This is a code-level derivation for the exact original source operands, not a new strict theorem about every inherited native payload or warm recursive query. An arbitrary prior intersection can require its own actual shape/normalization proof. Its language being a subset of the singleton Marker language can still mean empty. The checked [original_universe_terminal_marker_native_restriction](/home/tritlo/Code/mcfta/lean/MicroCFTA/SourceSynthesisCurrentUniverseTerminalMarkerNativeRestriction.lean:38) establishes that subset and actual raw aliases, not existence of a member.

## Consequences for the full objective

A faithful source caller should specialize the outer Bool to its actual root detector and preserve that field. For the raw accepted original FirstOrder root, the current code and checked ownership/body laws support the false specialization. This is a correspondence step, not proof of finite completion. The transformed public Space has a separate actual-root and transformation boundary.

Setting checkEmpty=true is not a valid shortcut to the full goal: it is not the raw caller's demonstrated configuration, the per-query gate can still skip, and a conservative false answer does not prove inhabitance. Conversely, checkEmpty=false is not a defect: structural native emptiness and actual source occurrence/typing restrictions can reject incompatible branches independently.

The next semantic route can use actual only-U pending-boundary membership, a genuine productive plain native-domain invariant, or a source-qualified Marker/Type incidence argument. Each route must be produced from the SAME original branch and all original operation receipts. Independent per-domain members still do not satisfy all historical equality buckets under one assignment automatically.

The preserved target is ONE finite accepted completion of the SAME original source root, at its original supplied budgets, satisfying native domains, guards, stored equations and causal historical obligations under ONE assignment. No concrete reachable-source defect was established, so there is no new FINDINGS entry or external repair request.
