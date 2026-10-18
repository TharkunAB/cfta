# Semantic entry transport in the actual outer worker

Final source review on 2026-10-18 at 05:45 CEST. The current restart sections, existing proof bodies, and both new final endpoint adapters are reviewed. This audit runs no Lean build and changes no production source.

## First actual gap

The first summary missing semantic facts from the existing physical `Reached` induction is `rows_edge`. The new checked `ActualEdgeCallSemanticReads.edge_call` now supplies those facts from the stated initial semantic context and reservation. The literal rows worker executes an entire `edgeCall`, then enters descendants at that call's returned caller. `OuterPrefixInvariants.step_good` obtains only physical Good, operation effects, and a resident returned edge. It does not obtain the semantic Context, generated-query Frame, updated Fits, or global bundle needed by the next semantic stage. `rows_tail` and `walk_tail` repeat this issue for completed earlier work.

This is a missing proof of semantic transport, not evidence that the implementation destroys a valid context. The underlying individual Parent and local numeric producers already retain that context under their stated initial resource support.

The first cold Parent entry itself does not require a new class-entry theorem. The path is node demand, ordinary row selection, edge demand, then the captured edge owner's Parent call. The demands change only the outer protocol tables. `PartialCallSteps.node_start` and `edge_start` derive the captured owner's ready inputs and retain Context. `beginNode_components` and `beginEdge_components` keep Checked, Merge and fourth tables exact, so Frame and Fits at that entry remain exact too. The captured owner must be used for its field, children, and reservation. A candidate with the same key must not replace that owner without the existing key-transport argument.

## Existing producers already cover the internal class entry

`ParentNumeric.resident_complete` at `SourceCurrentParentNumeric.lean:203` needs initial Context, Frame/Fits, the live resident edge and inherited readiness, and the initial pure resident reservation. It derives the actual loaded field and original child availability. Raw rejection skips those live inputs and needs no local Room.

Its call to `LocalNumeric.complete` at `SourceCurrentLocalNumeric.lean:88` handles the actual precheck. Allocation changes only equality operations. The proof constructs the precheck Frame and retains the same numeric profile explicitly. The classes branch extracts proper, coherent, active records from that actual precheck.

`ClassesNumeric.complete` at `SourceCurrentClassesNumeric.lean:74` constructs Scan and Required preparation. The prepared receipt supplies selected domains at the actual prepared forest. It then invokes the class caller producer, whose initial Frame and full semantic Context are the prepared return. It returns the complete old graph and strict Reads, semantic receipt, same-inventory Frame/Post, and final Fits.

Thus Parent and local numeric completion already produce every internal class-entry context, selected ForestClosed domain, and historical target receipt. They need no caller-supplied future Reads, prepared forest, whole-forest closure, or finite Cap. The initial reservation is a pure function of the actual entry state and original request. It remains an explicit resource premise.

## Mu is not this transport gap

`MuReconstructionEffects.complete`, `physical`, and `node_body` prove that a resident stored Mu reconstructs to its exact smart cleanup at the unchanged heap and complete caller, from the initial probe invariant and availability. `NodeTerminalNumeric.complete` constructs its strict source graph, NodeLaw, Post, unchanged Frame/Fits, and literal return at every fuel. `NodeCallNumeric.terminal_evaluated` finishes its exact captured owner with that law.

`PartialCallSteps.node_binder` at `SourceCurrentAllocatedPartialCallSteps.lean:172` already derives the inherited-conditioned node law from the actual rebuild and initial probe facts. No new full stored-body/ordinary reconstruction theorem is needed to retain Context through this outer terminal branch. General retained native Mu correspondence remains a separate open problem.

## Warm outer returns

`PartialCallSteps.node_hit` and `edge_hit` leave the complete caller unchanged. They recover the captured winner and transport its existing immutable result law to the queried request through resident key identity. `NodeCallNumeric.ready` and `EdgeCallNumeric.ready` additionally retain Frame/Fits and construct exact strict read receipts at all applicable fuels.

These results require initial `PartialMemoSound.Sound`. `OuterPrefixInvariants.Good` checks ready captured inputs, exact physical request keys, and resident returned values. It contains no NodeLaw or EdgeLaw for those values. Physical residency cannot supply the missing law. Warm hits do not create this gap; a prior cold completion must install its semantic law when it finishes the owner. `PartialCallSteps.node_finish` and `edge_finish` perform that installation once the actual body Post and law have been proved.

## Ordinary constructors and descent

The raw node and edge rebuilds add ordinary records and leave native result tables exact. `PartialStepEffects.raw_edge` and `modify` already derive Context/Post from actual constructor receipts. `inherited_prefix` and `descent` derive the corresponding actual allocation Context/Post. Their native tables and constructor heap stay exact during equality-only allocation.

The full Frame can use `ConstrainedCapOperandFrame.advance` with the actual Ready, Extension, unchanged native node/edge tables, and causal GuardHeap. Raw ordinary constructors create no Mu records. `GuardHeap.preserve` and the existing actual outer guard-retention theorem cover that guard component. Initial Frame guard observations are not assertions that every row is plain. Updated numeric profiles must still account for any new ordinary constructors; heap growth alone does not retain the same Fits bound.

## Concrete next step and residual

The new adapters implement the first bounded step: align Parent numeric completion with a literal completed Parent call. `AllocatedParentWorkerStability.edge_done_unique` at line 78 identifies all four returned components: full edge Value, full Checked state, fourth memo, and Merge memo. The observed nine fuels need no comparison with the forecast. The companion Graph-indexed EdgeBody consumer retains its exact observed graph. The root EdgeCall consumer constructs its own completed graph directly from the literal successful worker equation. It needs no supplied EdgeBody graph. Apply its receipt, Frame and Post to the first edge return in `rows_edge`. A separate rows wrapper is unnecessary. This is a substantive endpoint composition, not a new lower semantic oracle.

The new adapters close that first summary under its initial Context/Frame/Fits/reservation. They do not establish those resource facts at every later recursive entry. `walk_tail` still needs the semantic result/Post/Frame of a completed earlier ordinary node, including its own nested rows. The old `AllocatedPartialWorkerActual` mutual induction derives Context and strict Reads from a successful actual worker, but its reached range predicates remain inputs. Its `edgeBody_step` delegates to the old range-dependent Parent verifier. A renamed reached-range or per-future-parent reservation callback would not discharge this remaining initial-resource obligation.

The next general invariant must combine actual semantic Post/Frame transport with a genuinely initial resource schedule for those recursive summaries. It must also retain returned outer result laws when publishing cold owners. No all-active owner exclusion, termination, or fresh-request bound follows from this audit.

## New adapter review

No material issue is found in the two final source modules.

`SourceCurrentActualParentSemanticReads` has SHA `090e49d4636d01152a3145ba42f91a0f976a5f0b34b1841174ddbda669e5060f`. `parent` constructs ParentNumeric completion and aligns all four returned components through `edge_done_unique`. Its returned Receipt includes the original graph, strict Reads, full semantic receipt, same-inventory Frame/Post, forecast Fits, and stable literal run. No inequality compares the observed nine fuels with the forecast.

Its `edge_body` accepts an already completed source EdgeBody graph as an explicit observation. Graph completion derives a literal successful Parent equation. Numeric EdgeBody completion and result/full-caller uniqueness identify the same return. Proof irrelevance puts the strict Reads on the supplied graph. This method is a graph-indexed semantic consumer. It does not claim to derive that observed graph from a raw worker equation without other support. It supplies no future Reads, law, or final invariant as an input.

`SourceCurrentActualEdgeCallSemanticReads` has SHA `f6dcf3255402b85795cc91b5dca9381ce046e8fd59d4e22ac66929840e17b6ae`. Its one public `edge_call` method takes the literal successful outer EdgeCall equation. `EdgeCallNumeric.finite_or_busy` constructs the candidate complete receipt or the exact initial busy failure. The observed successful equation rules out that failure. The full result and entire returned Caller align through `edgeCall_done_unique`, including both outer tables, Checked, fourth, and Merge. This proof constructs its own actual graph. It assumes neither a notBusy proof nor a future completed body graph.

The initial EdgeCall reservation inspects only initial `beginEdge`, its captured owner, and its exact post-demand state. Ready and busy branches reserve True. Evaluation reserves that owner's actual initial Parent profile. It does not assume that the queried candidate's source row equals an older captured owner merely because their keys match. The existing sound key transport and captured-owner protocol supply the corresponding laws.

A `Reached.Step.rows_edge` already contains the completed earlier literal EdgeCall equation. It does not require the pending descendant call or later rows to complete. Therefore the new EdgeCall theorem supplies exactly that step's destination Frame and Post under its initial support. This is the new positive bridge. General semantic induction through `rows_tail` and `walk_tail` remains open.

Selected production runs are parent-semantic-direct-1/canonical-1/public-1 and edge-call-semantic-direct-1/canonical-1/public-1. Each strict log has exactly zero bytes. Each canonical run passes with the unchanged older dependency warning. The two public groups cover two and one declarations with full signatures, proof terms, and axiom reports. Every required option is explicit. No omitted term, warning, error, or nonstandard axiom is selected. Effective memory maximum/high are 4294967296, with swap maximum 0.

This independent component selects no new public or constructed declaration and performs no Lean build. The separate initial live-class fixture belongs to its own component and is not counted or used as a premise here.
