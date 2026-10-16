# Causal quantitative outer returns

Reviewed: 2026-10-16 22:12 CEST.
This is a read-only design. None of the proposed quantitative laws is claimed proved.

## Recommended certificate

Use a universal conditional certificate at each complete stored owner. Do not store a fixed profile chosen by the caller that first demands the cell.

```
NodeCertificate owner result :=
  forall R A G H,
    QuantNode R A G owner.value -> height owner.value <= H ->
    QuantNode (nodeRows R A G H) (max A 1) (nodeGuards R A G H) result
      /\ height result <= height owner.value

EdgeCertificate owner result :=
  forall R A G H,
    QuantEdge R A G owner.value -> edgeHeight owner.value <= H ->
    QuantEdge (parentRows R A G H) (max A 1) (parentGuards R A G H) result
      /\ edgeHeight result <= edgeHeight owner.value
```

`QuantNode` must include `NodeShape R A`, plus a guard bound at EVERY nested edge. `QuantEdge` includes its own raw guard and its children. The edge certificate covers the result of `EdgeCall`, which runs the parent body. It does not include the later `Descendants` traversal. Keep the existing NodeNarrow/EdgeNarrow and semantic laws separate.

The complete `NodeRequest`/`EdgeRequest` includes `inherited`. Retain that owner in the cell and in the certificate. For this constructor/profile bound, the numeric envelope can ignore the size of `owner.inherited`. This stronger uniformity is justified by the source branch structure, rather than by erasing the argument. If equality-interner allocation, normalization work, or total instructions are included later, add a separate inherited-payload metric.

Define quantitative Stored over both returned tables. An actual evaluating finish installs only the certificate derived for that exact owner's actual body. Begin and demand create no returned cell. A lower advance retains the same outer tables and replaces native/merge certificates with the certificates proved for that lower return. This design also needs stronger lower guard certificates; current native OutputStored and MergeProfileCache.Stored bound structure but not guards.

## Why inherited size need not control the parent profile

Haskell `Operations.hs:207-213` tests the combined own/inherited payload for contradiction, but selects `unsafeSubsumptionOrderedEclasses ecs`, where `ecs` is OWN. Lean `SourceEqualityPrecheck.precheck:77-80` does the same. `live_payload:145-148` identifies a live class list with `ordered originalOwn`.

Thus use the maximum of the unchanged, erased, and live-own-class envelopes. A larger inherited payload can change the branch or the child payload. It does not add inherited records to the local class pass. `PartialPrecheckAllocation.run_correct:27-35` connects the actual accessor/operation-cache return with this pure branch. This avoids an unnecessary inherited-size parameter in the output row/arity recurrence.

The descendant prefix is different. `InheritedPrefix.run:30-41` combines inherited FIRST with the actual RETURNED edge's own constraint. `PartialDescent.Receipt.payload:45` gives the exact indexed suffix payload. Retain those actual operations and payloads. Do not replace them with an empty payload or replay the combine for each child.

## Guard metric and required transformer

For a first implementation, let G bound all of the following at each raw constraint: normalized stored path occurrences, the number and lengths of paths in outer positive Same atoms, and the number of relevant conjuncts. A vector is clearer than a scalar if the scalar requires repeated decoding. Use a contradiction case with trivial bounds. Count literal occurrences before deduplication to get a conservative bound. Residual guard atoms remain legal and need no solver assumption for this constructor metric.

The accessor bound must cover EFFECTIVE `sourceEqualities`, not only `constraint.equalities`. `Constraint.hs:129-136,171-176` adds positive Same atoms, while a residual guard suppresses the positive extraction. `GuardConjunction.atoms:13-16` flattens only outer And; `merge_mem:312-316` proves that a conjunction introduces no new atomic guard. Stored equality normalization still needs its own numeric bound.

Existing `EqualityTermination` supplies a concrete starting point. For prepared canonical input classes C, let M be `(members C).length`, D be `initialGap C` (one plus maximum path length), and alphabet be `initialAlphabet C`. `bounded_state:539-548` puts every successful normalization state in `words alphabet (D*(M+1))`; `anchored_class_bound:420-422` bounds the class count by M. `saturationDomain:598-599` and `mkEqConstraints_total_cases:627-638` avoid a future-normalization-success premise. Add a corollary exposing these bounds for the final normalized output, then derive a monotone join transformer J for two bounded stored fields plus positive guard atoms. This finite path domain is derived for each concrete normalization input. It is not an assumed fixed carrier for all future nodes or requests.

Required local closure laws are:

1. Actual native conjoin returns a guard bounded by J of its two inputs. `ConjoinAllocation.conjoin_correct:75-84` exposes the exact raw result and actual equality payload. Prove the guard law before installing the native returned certificate, including warm owner readback.
2. Projection and Required retain source guards during raw reconstruction. Merge small groups retain guards; large groups use Top (`MemoMergeGraph.small:59-61`, `large:68-72`). Prove and retain a universal merge guard certificate for every exact stored winner. An earlier winner cannot inherit a losing candidate's bound.
3. Class/Pass guard bounds follow the same tail-first order as their row bounds. The bounds must cover every nested output guard, because a later parent can inspect any of them. Existing profile/language laws do not imply this.
4. Parent root guard is the original complete raw guard on acceptance, or Top on rejection. Descendant raw setChildren keeps that returned guard. These are no-growth root-guard steps; their children still need the recursive guard bounds.

These are missing proofs, not assumptions already supplied by Ready or semantic equivalence. If the first new result proves only row/arity output profiles for a single parent, it can use the exact pure own payload and the existing ParentResources recurrence. It must not advertise hereditary closure for the whole outer traversal yet.

## Usable envelope and order

Set `A' = max A 1`. From the effective own bound, derive a class count K, maximum paths per class P, and path length D. Dominate each ClassResources.outputRows by a pure `classMax(R,A',P,D,H)`; then iterate that monotone function K times. This dominates the exact tail-first PassResources.outputRows at every own-class ordering. Take a maximum with R for unchanged/erased branches. ParentResources.outputArity:67-71 includes the original child count and sentinel; choosing the count ceiling A' makes the hereditary arity ceiling A'. Derive a corresponding parent guard envelope with the new lower guard transformers.

For node input height H+1, call this parent envelope `(PR,PQ)` for edges whose children have height at most H. Then use the node envelope at STRICTLY LOWER height H on every returned child with input parameters `(PR,A',PQ)`. One conservative recurrence is:

```
nodeRows(R,A,G,H+1)   = max R (nodeRows(PR,A',PQ,H))
nodeGuards(R,A,G,H+1) = max G (nodeGuards(PR,A',PQ,H))
nodeArity             = A'
```

The base handles Empty. The ordinary root retains at most its ORIGINAL number of rows. Raw modifyNode can filter rows but does not add them. ParentNarrow gives the child-height ceiling needed for H, including rejection. Use monotonic envelopes when the actual child has smaller height. This is a proposed recurrence schema; PR/PQ and monotonicity still need definitions and proofs.

The matching request recurrence pays each ORIGINAL row for: parent work, recursive calls on the RETURNED parent's children, one raw descendant edge reconstruction, then the original suffix. In schematic form, with parent costs PN/PE and original row count at most R:

```
nodeCost(H+1) <= 1 + R * (PN + A' * nodeCost(H,PR,A',PQ))
edgeCost(H+1) <=     R * (PE + 1 + A' * edgeCost(H,PR,A',PQ))
```

The extra node/edge requests are upper bounds; identity fast paths can skip them. This order is literal in `PartialGraph.Rows.cons:89-92`, `Descendants.run:97-101`, `Walk.cons:114-117`, and `PartialWorker.rows:128-131`. Earlier effects leave headroom for the next stage. The original row suffix keeps its original structural profile through heap growth; it does not use the widened parent result as its input list. Warm lower and outer cells use their universal owner certificates, so unrelated earlier allocations do not force a global fixed input profile.

## Warm requested-result transport

`PartialState.NodeRequest.key:44-45` is inherited identity plus tagged node reference. `EdgeRequest.key:48-49` is inherited identity plus edge identity. The cell keeps the first complete owner. Use Sound/physical validity to extract that exact owner and its availability/residency, then common-heap coherent readback to prove owner.value=candidate.value. Existing `OuterState.node_evaluate:99-116`, `edge_evaluate:119-136`, `Stored.node_ready:155-173`, and `Stored.edge_ready:176-194` show the exact pattern.

For the proposed shape-only certificate, value equality transfers its entire conditional input and output envelope. No equality of inherited payload metadata is needed because the numeric envelope is uniform in inherited. If a payload-sensitive metric is added, equal identities give equal physical trie keys only via `PartialKeyTransport.recorded_key_eq:87-104` with both Recorded facts and one valid common interner. Coherent canonical path metadata must then transport the metric. `sat_of_identity` alone transports a meaning predicate; it does not prove a numeric payload bound. Do not substitute semantic equivalence for this step.

## Counterexamples to weaker claims

- Height alone does not bound rows or arity: one ordinary node can have arbitrarily many distinct nullary alternatives at height one, or an arbitrarily wide single row. Domain and NodeNarrow therefore cannot replace QuantNode.
- Native output rows need not remain at the input limit R. With two f-rows on each side and child languages `{a,b}`, `{c,d}` versus `{a,c}`, `{b,d}`, the four matching pairs yield distinct f(a), f(b), f(c), f(d) rows. This is the source pair-product mechanism, not a tested executable reproducer here.
- The maximum input equality path length is not preserved by combine. Individually normalized classes `{[0],[1,1]}` and `{[0,0],[2]}` have maximum length two. Congruence adds `[1,1,0]` to the second class. The generated class has no strict-prefix collision. `Equality/Constraint.hs:427-444` gives this extension step. Thus `Dout=max Dleft Dright` is false; the example is a symbolic source trace, not a newly executed Haskell test.
- Stored empty equalities do not imply empty own classes: `Constraint EmptyConstraints (Same [0] [1])` exposes a nonempty effective class. Full guard extraction is required.
- Input height does not bound guard path length: a normalized class can mention a missing long path. Its language may be empty, but that does not remove its stored records or class work before the source checks it.
- Rejection can replace a nullary edge's children with one Empty child. Parent output arity is bounded by `max A 1`, not A or the original length.
- A warm cell with only semantic Sound plus NodeNarrow can carry a much wider, same-height result. A desired profile cannot be read from those predicates. It must have been derived and installed at the cell's actual owner completion.

## First concrete proof stage and scope

First prove an effective-own normalization envelope and exact raw conjoin guard transformer. Then strengthen native and Merge returned certificates with hereditary guard bounds, and lift those through existing local/class/parent constructions. Only then install outer node/edge certificates by the actual eight-family induction and use the height recurrence for initial constructor headroom. No helper that merely assumes the local certificate at finish closes this producer obligation.

Current ParentResources already constructs one exact parent from initial profile, path facts, and headroom. It does not establish the new hereditary guard recurrence. Constructor request bounds remain separate from equality allocation, total normalization/solver work, active-owner exclusion, width/key capacity, host laziness, HashMap representation, Mu/reference/union progress, and repeated-pass convergence. This design adds no Haskell repair and makes no whole-library completion claim.
