SOURCE-ONLY PLAN. No new control, theorem, implementation or check is supplied. The frozen relational graph inventory remains unchanged.
The three proposed phases are sufficient for one same-symbol cluster: cluster, scan and comparison with a retained H7 control [PairControl:22–106].
The scanner reuses the full H7 State directly. It needs its own list-valued Outcome, but no new cache or native state record.
The comparison phase stores the original pivot/candidate and all scan accumulators while it advances exactly one H7.step.
The FIRST identity test is common==candidate. The SECOND is common==pivot and is reached only when the first fails [HaskellScan:365–370; HaskellEdgeEq:209–213].
Incomparable rows accumulate in reverse order. Promotion resumes cluster(candidate :: (reverse incomparable ++ tail), keptReversed).
Without promotion, scan-end resumes cluster(reverse incomparable, pivot :: keptReversed). Cluster-end returns reverse keptReversed.
These equations retain literal Haskell reconstruction order. For [pivot,a,b,c], an incomparable a followed by b promotion resumes [b,a,c]; a final Sublist claim would be wrong.
The common result controls only the two identity tests. It is never inserted as a later scan operand. No equality or self-comparison fast path bypasses H7.call.
Yield and blocked outcomes preserve the entire outer frame, the exact reported inner H7 residual and the actual full state. Failure and constraint error preserve the original reason and state; H7 provides no resumable failure continuation.
The fuel runner follows H7: zero yields the exact control/state; a successor advances one step. Even an empty cluster needs one positive step to return.
The outer macro rank is lexicographic: cluster has (candidates.length,candidates.length); scan has (1+remaining.length+incomparable.length,remaining.length).
Cluster-start and the incomparable branch reduce the second coordinate; dropping a candidate, promotion and scan-end reduce the first. The kept accumulator does not affect this rank.
This rank does not decrease on every H7 microstep. Derive each actual comparison completion from H15, then lift that finite run through the comparison frame before the next outer rank step.
H7.execute can stop before it consumes all supplied fuel. The local lift must choose a consumed prefix 0<used≤fuel; using the entire supplied fuel can overrun the desired resumed boundary.
H15's returned global Trace and initial reserve derive the next-call Room. Keep source/model/ranks/holds, width, initialDomains, inventory and the actual evolving caches fixed [H15:55–187; DomainHistory:74–75; Room:104–115].
Membership in the initial symbol group is preserved for every outer operand and retained row. H15 then supplies each comparison without a future callback or successful-run premise.
The next completion statement must conclude an actual fuel-indexed scan execute equation, not merely existence of RuleOutRun/ClusterRun. A local step trace can support that proof but is not a replacement result.
The minimum coherent first slice is the operational Control/Outcome/step/execute and exact H7 forwarding/lifting laws. The conditional cluster-completion contract is a further proof obligation.
H7.step and H7.execute are explicitly noncomputable definitions. The new runner inherits that status; this is a functional operational interpreter, not a claim of a newly compiled runnable Lean program or Haskell refinement.
The first theorem is for one exact original-row symbol group. Hash-group order, mapNodesStep reconstruction, generated Mu parents and unfolding/body filtering remain separate [HaskellScan:744–770,790–798].
Current canonical EdgeLaw is conditional. Neither this control nor a completion/provenance theorem supplies the physical pruning iff or language-preservation bridge.
The H15 saved strict1/FULL1 receipts and readback are successful at this cut. This plan does not assert an Audit or publication result; the old graph's earlier unchecked status remains historical.
I authored the scan plan and H15 checkpoint templates and source/readback audits. Arity authored H15 and the graph inventory. No foundation is independently re-proved here.
