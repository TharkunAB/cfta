# Plain node induction: independent draft review

Reviewed on 2026-10-16 15:45 CEST. This review reads the new node induction and its child and row helpers. No build was run. These are reviewed draft snapshots, not a claim that the draft elaborates. Final compilation and final source digests are separate evidence.

No mathematical circularity or owner-state mismatch was found.

`PlainNode.finite` proves `completed : ∀ rank, Below rank` by natural-number strong induction. For a candidate with `nodeRank candidate < rank`, it gives `step` exactly `ih (nodeRank candidate) lower`. This is `Below (nodeRank candidate)`, which permits only strict children. It is not a universal recursive completion assumption. The final call uses ceiling `nodeRank request + 1`.

`step` first derives actual begin safety from current physical coherence, initial semantic memo soundness, residency, and `ActiveAbove` at the candidate rank. A hit uses the actual returned owner law from initial `Context.sound`. That is an explicit legitimate warm-cache invariant. It is not a supplied result law for a new evaluation. It also preserves the structural edge-table `Stored` invariant.

An evaluate branch starts the exact captured owner and derives its inherited readiness, availability, current Context, value equality, and Region. Value equality gives literal rank equality. `node_push` proves the running caller is active above candidate rank minus one, including the new owner. The body uses that same owner, its ready inherited payload, its current resident input, and the transported strict Below hypothesis.

The body handles empty/union/Mu through `PlainTerminal.complete`. Mu completion follows actual resident rebuild probes and can return cleanup rather than the input binder. The ordinary branch derives resident original rows, invokes `PlainRows.rows` with strict original edge ranks, then constructs the actual ordinary graph, strict Reads, and Checks before `PartialActual.node_body` derives its Post and NodeLaw. This is verification of an already constructed graph, not construction by assuming its result law.

`PlainChildren.walk` follows literal descent at the current index. The recursive node call starts at that returned caller and payload. The suffix starts at the head's exact returned caller, with increased index, grown inherited readiness, old-tail residency, returned structural Stored, and the SAME ceiling restored by the head's actual NoNewActive theorem. The live and contradiction branches preserve source behavior. Contradiction performs no node call.

`PlainRows.rows` calls the independent finite parent edge worker, then descends through the RETURNED edge, then visits the original row suffix. Its Shape proof gives Region and rank for narrowed children, including singleton Empty. It restores the fixed active ceiling after both prefixes. The new structural Stored follows the actual prefix state and is not replaced by semantic EdgeLaw.

The final `CallSteps.node_finish` derives forward survival of the exact evaluating owner from the actual body graph and its initial Protocol. The body Post alone is not used as an owner-survival claim. Literal finish installs the derived local law, and `Stored.finishNode` retains the unchanged edge table. Candidate-law transport uses actual request-key provenance and current physical coherence.

The public finite endpoint has only initial Context, inherited readiness, available Region input, structural Stored, and active-owner order. There is no public success, range, future graph, output invariant, result-language law, or completion callback. Context contains initial physical and memo invariants; those remain explicit warm-state requirements. The endpoint covers one Region pass. It does not establish general constrained or repeated-pass termination, host GHC evaluation, concurrent publication, or host-container identity correspondence.
