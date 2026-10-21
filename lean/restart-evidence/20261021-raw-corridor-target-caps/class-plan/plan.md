# Raw endpoint corridors through actual class edits

Date: 2026-10-21 04:49 CEST. This package is a source-only design. It runs zero Lean jobs and adds zero public proof pairs or examples. Proposed statements below are unproved. Keep the old 315-line OriginalGateProjectionCap source and its frozen packages unchanged.

## Minimal raw contract

Use a NEW signed-path inductive. Do not publish an alias of an inaccessible private predicate.

```text
RawCorridor : List Int -> Node -> Prop
full path value (bounded : exists depth, Cap Plain depth value)
node index path entry rows level free
  (children : forall row in rows, forall child,
    select row.children index = some child -> RawCorridor path child)
  : RawCorridor (index :: path) (.node entry rows level free)
```

The full constructor permits a finite nonplain endpoint or any remaining path in a finite region. The node constructor checks EVERY raw row and the SAME signed child index. It imposes no requirement on other child positions. A Mu, union, reference, or Empty can enter only through full. A finite Mu is hereditary Plain by Cap constructor inversion. No input/output availability or actual future completion is hidden in this raw syntax predicate.

A selected forest mask needs no new inductive: for a nonempty signed path `index :: tail`, require `forall value, select values index = some value -> RawCorridor tail value`. An empty root path can require every forest member to have a finite cap, but actual coherent nontrivial class paths exclude this case. Keep forest helpers private until an actual public consumer needs them.

The first concrete module should expose this inductive and one source producer. `of_origin_gate` takes the SAME Origin, ORIGINAL false NodeTrace, initial SemanticReady and original Available. It returns RawCorridor on the SAME prepared value and `path.map Int.ofNat`, without Project, a cap premise, closure, UnionNormal, or a future current heap. An actual requireAll wrapper may then derive the ordered All₂ Origin once and quantify each SAME prepared slot for every selected class/index/path. RequiredPrimaryExposure.false_edges_members and false_selected are public at lines30 and52. Reuse them with the exact installed edge equality instance instead of copying their private replay proofs.

Source proof route: copy only the finite-list/Origin/raw-corridor source part of OriginalGateProjectionCap (lines28–181), with public RawCorridor and the finite existential expanded in constructors. Reuse public PrimaryEndpointCap.endpoint_cap/reaches_cap and the existing pure Origin mutual recursor. Retain the original anchor availability for Mu annotations. Do NOT copy its actual projection/read/union proof (lines183–303) into this initial raw module. Estimated source size is about180–240 lines; this estimate is not a checked proof.

Public inductive constructors and recursors already support downstream cases. Extra public root/selected wrappers are optional. Do not add them solely to increase the API. A private two-line inversion of RawCorridor [] yields its finite whole-value cap.

## Smallest actual class preservation statement

Write privately:

```text
Preserves original result :=
  forall signedPath,
    RawCorridor signedPath original -> RawCorridor signedPath result
```

For one actual `Class record values before memo results after saved` with its SAME `ClassReads`, propose:

```text
initial physical Ready / inventory admission / Values
actual selected path domains / physical Merge Stored / CacheCovers / valid memos
current native cap laws and Merge cap laws at before
coherent record, Nontrivial record.paths
(forall p in record.paths, raw forest corridor at p.map Int.ofNat in values)
-----------------------------------------------------------------------
exists next, SAME actual class Receipt ... and
CurrentNative.At Plain after and MemoMerge.Stored Plain saved and
All2 Preserves values results
```

There is no global cap on every root of values. There is no callback-result cap or supplied leaf certificate. The class initializes its target slots empty. It derives finite target laws at actual misses and reuses the SAME earlier values on hits. At class return, only Current/Merge laws and the ordered relation need escape; class-local slots do not persist into the next class.

The universal ordered relation is smaller than an E-indexed class contract. If every current record path belongs to a monitored E, its raw corridors supply class placement. All2 Preserves then retains EVERY incoming E corridor, using the same root index through All2_signed. E belongs in the later phase induction, not in the local value relation. No positive ancestry relation or source-size bound is asserted here.

## Exact leaf pair coverage

Token membership alone is insufficient. AllocatedClassEditPlan.compiled_allowed (lines28–30) only says each action token belongs to record.paths. The joint full position/token fact uses:

* ClassEdits.edits (lines26–28): each original entry is `(p.map Int.ofNat, p)` for target=id.
* AllocatedClassEditPlan.compiled_disjoint (lines32–36).
* EditCompiledPaths.build_leaves (lines66–78): retained compiled leaves are a permutation of those SAME input pairs.
* EditDomains.HasLeaf (line17): an actual nonempty edit has an existing retained leaf pair.

Thus each literal leaf position is the signed image of its SAME class path token. Coherent plus Nontrivial derive nonroot paths; coherent alone is insufficient. Existing EditSupport.compiled_list/class_placement (lines80–109) gives the exact ordered placement pattern, but its endpoint is hereditary Annotated. Replace that endpoint with the finite whole-value inversion above. Do not reuse the old hereditary conclusion as if it were equivalent.

AllocatedSharedEditGraph has only native leaf, Empty, ordinary makeNode reconstruction, and recursive Head cases (lines30–45). Children retain exact indices and offsets, including unselected copies (lines47–59). Rows reconstruct every original row (lines61–70). Head consumes no child index. There is no extra LocalMerge edit branch: Merge occurs inside target forcing. The list-root editAt is ignored, and valid nontrivial classes exclude it (ClassEditPlan lines43–57).

## Private proof shape

Use one existing NodeReads/ChildrenReads/RowsReads mutual induction pattern. Reuse actual physical effect endpoints; do not copy the physical/semantic framework.

1. **Placement.** Define private finite AtLeaves, ChildrenAtLeaves, and RowsAtLeaves from RawCorridor. Derive class placement from the SAME compiled leaf pairs and captured masks. Use exact lookup offsets as EditSupport.ordinary_rows/children_head/children_tail (lines56–78).
2. **Native leaf.** Finite AtLeaves at editAt inverts RawCorridor [] to a full cap of the SAME actual input. Safe gives its closedness from the actual selected domain. The SAME force receipt produces a finite target. Choose max of these two depths and apply CurrentNative.step to the literal query. Its finite result satisfies RawCorridor.full for EVERY path. Return Preserves without a desired position premise.
3. **Ordinary node.** Children return All2 Preserves; rows return ordered child relations for the actual raw reconstructed row. makeEdge_children gives exact output child lists. For an incoming full corridor, node_edge gives finite original children; child Preserves at [] gives finite output children; a finite common max and makeNode derive a finite rebuilt value. For an incoming node corridor, All2_signed retains the SAME child index and source row. Actual makeNode membership restricts to canonical surviving raw rows. PathExposure.makeNode (lines31–48) shows the exact physical readback proof pattern. Nullary rows need no child-existence assumption; their rebuilt finite node uses an ordinary cap layer.
4. **Recursive Head.** HasLeaf plus finite AtLeaves gives SOME corridor on the recursive input. Its node constructor is impossible, so the WHOLE input has a finite cap. Actual ConstrainedCapOpenExposure.head derives the SAME exposed value's finite cap from semantic/cost/availability and the genuine current guard store. A finite exposed value supplies body placement for every retained edit leaf. Body IH at [] gives a finite WHOLE returned value. That returned value supplies every corridor. No backwards Head position law and no input global cap parameter are needed.
5. **Warm state effects.** Preserve Current/finite-slot/Merge laws at literal constructor or Head effects using CurrentNative.advance, unchanged native tables, actual guards, and forward keeps. Preserve each exact target slot value. Existing MixedEditStoreEffects.advance_stored/node/edge/head (lines30ff) supplies the small pattern; its old numeric slot Certificate cannot be converted from a merely existential cap. Reuse physical endpoints rather than its stronger Stored type.

The universal relation implements all overlap cases. At an edited ancestor, the full finite leaf result handles every suffix below it. At a monitored ancestor, finite child replacements rebuild a finite whole endpoint. Disjoint occurrences retain their ordered original child. There is no need for a separate public prefix/disjoint relation or event uniqueness theorem.

## Genuine dependency still missing

The checked RequiredSharedTargetCap.force_receipt is restricted to the literal actual prepared forest (lines168–196). Its private Operand/Fold helpers are not importable. It cannot simply accept a changed phaseValues argument.

Before the full class theorem is applicable to arbitrary phases, derive generic actual projected caps from RawCorridor, then a generic Force cap producer from captured record-path corridors. The public projection cap theorem currently exports only the original gate/Origin form. Its private project_corridor already shows the needed actual open induction (OriginalGateProjectionCap lines234–303), while its private ReadAll/Union helpers (lines183–216) use actual open reads. A new generic producer must derive these cuts, not assume their returned caps. The old ConstrainedCapSupportedProjection endpoint requires hereditary endpoints and closedness; it does not replace this finite open statement.

Generic target/Force proof then follows the checked 198-line module's SAME Operand/Merge winner, tail order, max query caps, and source-independent finite slot invariant. Replace only its source-specific Data/RequiredForestProjectionCap step with the new captured raw-corridor projection law. SlotReceipt keeps a historical graph and forward interval, not the complete past native entry laws; install caps during misses instead of reconstructing past laws from current readiness.

A realistic small sequence is: raw initial foundation about180–240lines; generic actual corridor projection plus target/Force about250–320lines; actual class universal preservation about220–300lines once those interfaces exist. These are design estimates. Combining all three into one300-line module is not a credible bound. Stop for source review if an actual component needs more scope or starts recopying a large framework. Root must approve implementation and ownership first.

## Chronology and remaining scope

Initialize masks only from the ORIGINAL false gates and actual Required origins. A later class captures the literal tail's phaseValues. ClassPassPhaseLineage.fold_indexed/fold_phase (lines28–155) fixes that tail/head/later schedule. Compose All2 Preserves along the actual right fold; never identify a later phase forest with prepared or assert a new false gate on it. Initial E coverage must include every executed record's actual paths.

This raw cap-preservation theorem would not prove positive-path source ancestry, Rel E transport, selected observer completion, native termination, global renewal rank, or Haskell refinement. Positive ancestry still needs the exact actual remaining Project/Read and SAME captured native writers. The finite caps would provide their input scope; they do not replace those causal receipts.

A nonvacuous future fixture should retain an unrelated nonplain opaque Mu sibling, a finite nonplain edited endpoint, a SAME-slot warm force, and a later class with a genuinely changed captured phaseValues forest. It should monitor one ancestor, one descendant, and one disjoint path without identifying different occurrences. No fixture or proof is run for this plan.
