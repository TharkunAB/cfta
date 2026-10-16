# Independent checked edge constructor review

Reviewed source: lean/MicroCFTA/SourceCurrentAllocatedMkEdge.lean.
SHA256: edef55c0db42605c003a897b8637fc5bb26aba6fb922c1e8548eb67eb30c865b.
The source has 217 lines. It was not edited or canonically rebuilt during this review.

No material defect was found.

The wrapper follows Interned/Type.hs:566–568. The literal check selects the original symbol, guard, and child list when accepted. Otherwise it selects the same symbol, Top, and one empty child. The underlying allocation module tests stored contradiction before demanding the full equality accessor. build_contradictory retains this short circuit and equates the actual wrapper with its rejection constructor.

Sentinel construction derives the actual emptyField allocation at the reached operation state. It does not assume that Top was loaded earlier. The general rejected branch first threads the actual check state, then emptyField. The raw contradiction endpoint skips that accessor state. Both produce a ready same-cache Top field before installing the literal sentinel edge. reject_correct takes no children, child availability, child completion, or result-language premise.

Physical effects use the actual edge constructor's Keeps and semantic result. Annotation preservation lifts old field facts through operation growth and uses the selected guard's current FieldAvailable. It supplies no future Fields or SemanticReady. The wrapper retains complete native node and edge tables and the domain cache. It advances the constructor heap and actual equality operations, and derives machine extension and inventory At at that return.

The language theorem handles both source constructor outcomes. In the accepted branch, literal field equalities yield exact edge membership. In the rejected branch, the sentinel accepts no term. The converse uses the stored value's derived active-class invariant, PCS-to-source guard correspondence, and the accepted term's actual child arity. It does not assume a universal guard conjoin law or a successful future source check. The result is the raw original edge language, including arity-based rejection.

One independent pinned direct Lean kernel passed in mkedge-independent-probes-2.log. The first attempt also passed, with one unused section-instance warning. An omit declaration removed that evidence-only warning. The kernel starts from a resident source edge and initial checked Ready and At. It derives the actual same-cache load, stored readiness, selected FieldAvailable, and child availability. It then constructs the actual new edge receipt and derives its exact original-guard language. It also transports the unchanged three-global-table bundle and fourth memo through constructor heap growth. No separate Cached or load premise is supplied to this kernel.

The kernel has one axiom report and one full signature check. Only propext, Classical.choice, and Quot.sound occur. The log has no errors, warnings, or sorryAx. Existing sibling probes cover the public constructor endpoints; this review did not repeat them.

These statements cover completed resident construction and represented natural path arities. Host evaluation order, lazy noConstraint publication, physical identity representation, and machine-integer correspondence remain explicit adapters. The source rejects before forcing an unused child computation; the separate rejection endpoint preserves that boundary.
