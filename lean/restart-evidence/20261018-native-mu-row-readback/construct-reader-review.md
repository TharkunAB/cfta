# Final-reader Mu construct row readback

Reviewed and frozen at 2026-10-18 08:49 CEST.

Production: `lean/MicroCFTA/SourceCurrentNativeConstructReaderReadback.lean`.
SHA-256: `b100c33b37a347669cbe051a7d752bdc950be370322eacbe8845d67db0e90812`.

The two public declarations are `RowReadback` and `construct_row`. The producer takes the actual completed construct equation, initial SemanticHeap and body availability, a later reader with `History empty reader`, forward `Grows after reader`, and one literal indexed row in `nodeEdges value`. It derives the actual depth callback, current ordinary callback, selected request, raw repaired stored execution, and self-filter schedule. The receipt retains the complete selected Mu record at both the construct return and reader.

The selected row forces unused-local cleanup only after the proof derives `InternedFreshOrdinaryDepthHeap.Correct` from the actual decomposition's final Context. The proof does not infer this property from an arbitrary Mu record. The helper `SourceCurrentNativeOrdinaryMuFinish.selected` then gives usesLocal=false, literal body return, absence of the interned self name, and the same indexed stored-body row.

The proof transports the complete selected record forward with `growth.nodeRecords`. It applies `history_unused` at the later reader. It does not infer an earlier History from a later History. It does not assume publication History before construct. The older ConstructReadback module supplies imports, but this producer does not invoke its history-before-construct theorem. The later reader does not need a separate SemanticHeap premise.

The resulting equality identifies the actual value with erasure of the current ordinary callback. Actual raw context, availability, and the filter equation derive row Origin equivalence for every view and every complete edge. The positive selected row is also an Origin of the current raw ordinary substitution in every view. The complete EdgeValue retains its full guard and ordered children.

This result applies to a direct physical `nodeEdges value` selection. It does not assert that epsilon exposure of an arbitrary retained-used Mu implies unused-local cleanup. It does not prove general retained-used two-reconstruction correspondence, completion of outer recursion, or reference exclusion in internal native calls. It imposes no BinderFree, NoDeep, finite Cap, or closed-body restriction. Final reader History and forward growth are explicit inputs. Their causal construction from a native checked trace belongs to the root integration.

Selected evidence:

- `construct-reader-direct-1`: exit 0; raw strict log has 0 bytes; the immutable executed source matches production.
- `construct-reader-canonical-1`: exit 0; warning-free build completed successfully with 594 jobs.
- `construct-reader-public-1`: exit 0; two complete public signature/proof/axiom pairs. All eight print/linter options are explicit. Both #check commands use @. No omitted terms or printer failures occur. Axioms are limited to propext, Classical.choice, and Quot.sound.

Each execution uses the pinned Lean 4.34.1 toolchain and a five-minute heavy-management wrapper. The inner worker records effective memory.max=4294967296, memory.high=4294967296, and memory.swap.max=0. The direct and public commands execute immutable numbered sources with -Dlinter.all=true and the compiled LEAN_PATH.

There are no failed attempts in this component. The selected counts are two public pairs and zero constructed pairs. The root owns the source-built native Mu integration separately. This manifest uses an explicit file allowlist. It does not pin root working fixtures or other mutable component manifests.
