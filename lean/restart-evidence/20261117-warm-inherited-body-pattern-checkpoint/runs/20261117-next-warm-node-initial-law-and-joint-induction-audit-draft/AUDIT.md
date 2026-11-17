# Fixed-history warm query induction

Status: bounded source audit. The node initial-law candidate is UNCOMPILED. The edge seed header has no proof. The original full target remains OPEN. No compiler, Source, Work, Git, board, or temporary-file action was run here.

## Concrete progress

`cold_prefix_nodes_qualified_for_actual_warm_history` concludes the actual node `Returned` field required by `SourceQueryInduction.query_returned_and_raw_results`. Its law is the conjunction of the closed implication and the mixed implication under `MixedQualifiedAt newRoot oldSnapshot newCount`. It covers every returned node cell at the same old snapshot. No old authentic entry, result law, Profile, body law, OnlyU law, or model is an input.

The closed clause comes from the original cold C/M theorem. The mixed clause extracts its entry from the same fixed full later trace. The proof splits that trace at the actual entry, then applies the checked old-cell mixed Profile theorem to that same cell. The original source derives U's closedness. Full patterns, both universe-entry orders, both request orders, original height bounds, and all counts remain unchanged. In particular, the qualifier can use an entry later than an earlier memo read. No `Profile(fullPattern)` premise is introduced.

The candidate proves conditional cache meanings. It does not claim that all cached values are closed or that all requests are qualified. Its old actual trace can end at any cold prefix. The completed old query in FULL-OPEN is a specialization. The same full warm trace and its supplied budget remain explicit.

## Exact initial semantic fields

The existing source query engine takes two inputs at each starting state: `Returned nodeLaw before.native.nodes` and `Returned edgeLaw before.native.edges` (SourceQueryInduction:154 and165). Physical validity, source growth, operation validity, InputsThrough, and FieldsThrough are separate inputs. They do not imply either semantic field.

For the main C/M instantiation with a fixed whole warm history H, the node law is `(ClosedQualified → Profile) ∧ (MixedQualifiedAt H → Profile)`. The edge law is the existing ordered-zip contract: every original input pair is closed-qualified or mixed-qualified at H, then every returned row child has Profile. The candidate supplies the first initial field only. `EDGE-SEED-OPEN-HEADER.lean.txt` records the second field as a conclusion. It keeps genuine past inventory and old-root availability from FULL-OPEN. It assumes no old authentic entry and no row/result law. It is not a proof and must not be appended as a theorem.

Four distinct auxiliary meanings also remain necessary for the warm mixed-result callbacks. At the relevant entry D, let Kb=extend D[uid](pair bodyId uid), Kd=extend D[uid](pair uid uid), and Kt=extend Kd[uid](pair bodyId uid). The fields are:

- Returned BodyFirstKey.NodeResult(uid,bodyId,Kb,B,U) on nodes.
- Returned BodyFirstKey.EdgeResult(uid,bodyId,Kb,U) on edges.
- Returned CoherentOpenBody.NodeResult(uid,uid,uid,Kt,Kd,B,U) on nodes.
- Returned TopRow.EdgeResult on edges.

PastEntryNextQueryInnerLaws:493–559 already derives these four fields after a next query when its one authentic entry belongs to the supplied earlier cold source trace and the base keys match. It also derives the two completed raw-result laws. This is an existing semantic producer. It does not cover every new authentic entry whose first occurrence is in the current warm trace, nor does it convert arbitrary inherited tables into those meanings. The missing seed/adaptation must use actual producer receipts and key classification; it cannot add the four laws as external premises of FULL-OPEN.

These auxiliary laws cannot be replaced by unconditional closed Profile for every cache cell. The owner handles B/B and B/R products separately at NativeAllocation:2446 onward and uses `stored_open_product_optional_reclosure`. Keep their actual open-product meanings.

## Actual rank and witness coupling

The source query engine already uses strong induction on the supplied parentFuel (SourceQueryInduction:171). For a raw nested query, `0 < used` and `used + count ≤ parentFuel` give `count < parentFuel` (220–248). The child cache laws come from the SAME outer execution's smaller prefix `used < parentFuel` (280–285). This handles cells first produced earlier in the current warm query. No new chronology datatype or future cache oracle is needed.

The fixed history H is a semantic parameter of nodeLaw and edgeLaw. Do not shorten H when the fuel IH selects a smaller prefix or child budget. That would discard later authentic qualifiers. Only the actual consumed prefix/count and physical plans are restricted. The runtime budgets are not increased.

Mixed independently identified the concrete receipt rank from the existing origin APIs. If a returned cell at warm prefix H was absent at oldSnapshot, its writer gives H=F+1+S and therefore F<H. The same evaluating owner gives Q+1+B=F, so Q<F<H and B+2≤H. For a ready hit immediately after the literal domain enter, advance changes only the machine. The cell therefore already exists before that enter, giving F<newUsed. These inequalities rank actual receipts. They do not prove payload meaning or request qualification. Mixed owns that map; no origin proof is copied here.

Original operand height and the strict reference-alias bound remain qualification conditions. They are not a replacement for the existing bounded-fuel induction. No global strict decrease of U's height is assumed.

## Branch map and next proof order

An old cold retained B/P hit is covered by the checked HIT component reported by Root (88089). It keeps the same cell, literal later entry, lookup, demand, and ready endpoint. The present candidate lifts the existing old-cell semantics to the full initial NODE cache law; it does not depend on HIT. A same-warm-created hit instead consumes the engine's internally derived past cache law. A fresh evaluation consumes actual smaller node and edge result IHs in the nodeResults/edgeResults callbacks. Merely finding an earlier writer does not establish those result rules.

The checked auxiliary key theorem identifies authentic singleton bases/full patterns for the four exact auxiliary shapes. It rules out the particular source parent-pair collisions. It neither cancels arbitrary extensions nor establishes any returned payload meaning. Apply it at the coherent reader belonging to the SAME old producer and new entry before reusing an auxiliary semantic law.

GeneralCMHistory:78–138 currently closes its actual-prefix induction from complete empty initialization and calls the cold authentic inner histories for mixed finishes. Those start conditions cannot be replaced by oldSnapshot silently. The remaining work is to derive the initial edge and relevant auxiliary cache meanings from the old cold producers, then adapt the mixed finish/result callbacks to AuthenticEntryAt at the actual warm start. Reuse the existing engine and retain the fixed full H. An internally derived smaller-prefix cache law is a genuine IH. An externally supplied future Returned/Profile/body law would replace the missing proof.

NativeAllocation:2436–2442 shows the exact B/P optional-binder consumption: read the qualified child through the C/M law, get Profile, use its empty free list with `MaybeMu.unused`, then obtain no-new-Mu by reflexivity. The warm version must use the actual warm conditional result/cache law at that exact child endpoint. Source admission and prefix NoNewMu remain actual producer obligations. A before-prefix NoNewMu fact derived by step induction is legitimate past data. It is not available merely from Grows or physical validity.

A useful dependency order is to establish conditional C/M meanings first, then use them in actual source-admission/NoNewMu preservation. If a warm result callback needs source classification at a prefix, that classification must be derived from original root admission and a genuine earlier-prefix IH. This audit does not prove that callback adaptation or that second pass. FULL-OPEN, general warm NoNewMu, all-call source qualification, semantic chronology, native inhabitance, Type/Marker compatibility, and the one finite accepted-root model remain open.
