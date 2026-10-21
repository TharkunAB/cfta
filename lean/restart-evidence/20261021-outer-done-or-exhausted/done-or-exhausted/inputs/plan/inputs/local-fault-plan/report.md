# Remaining local outer faults: source audit

The next useful producer is the proposed `SourceCurrentOuterLocalFaults.failed_cases`.
It has not been implemented, elaborated, or checked. This package contains 37 plan lines, an exact 21-line proposed header, 11 complete source snapshots, and 17 cited ranges.

The worker has eight Fault constructors. The exhausted constructor has three phase tags. Memo and binder payload types admit observations that the actual worker does not emit [S1:26–55].

| Fault | Existing result or exact gap |
| --- | --- |
| exhausted | Remains an allowed result at the chosen outer fuel. |
| nodeMemo busy | OlderOwnerBusy.no_node_busy excludes it under its genuine initial packet and initialNodeIdle [S10:26–69]. |
| nodeMemo absent | Pending ReferenceAbsent targets it. No checked result is claimed here. |
| nodeMemo ready/evaluate | Actual nodeCall never emits these payloads. A recursive failure-provenance proof is still required [S1:60–71]. |
| edgeMemo | InitialEdgeMemoFailure.no_edge_memo_failure already excludes every observation, with Context/Frame/Fits/known/Inputs/Room and EdgeIdle [S8:43–89]. |
| unexpectedReference | Pending ReferenceAbsent requires the genuine conditional NodeStored and phase InputsClosed laws. |
| binder | resident_rebuild completes the SAME available Mu at the same heap, using current Ready and probes. No new local completion theorem is needed [S6:142–159]. |
| parent | InitialParentFailure.no_parent_failure already excludes every Parent fault, with all nine explicit phaseNeed inequalities [S9:36–68]. |
| inherited/missingInherited | resident_finite supplies the SAME actual ok(some combined) prefix from current Ready/admission, returned-edge residency, and inherited Ready [S7:175–184]. |

No public binder/inherited/missing failure-to-cut inverse was found in the narrow outer-module search. Existing Parent and edgeMemo inverses address their own fault families. ExecutionAncestry.Step.failed and Reached.failed propagate a supplied cut forward to its enclosing run; they do not extract these cuts [S2:500–542].
The proposed private six-phase induction retains an actual Reached cut from one fixed initial phase. It obtains semantic resources at that same cut from InitialPrefix.reached. Actual binds supply each completed earlier call and preserve the final fault caller [S2:325–382,S3:263–286].
At a Mu body, actual resident completion removes every binder payload. At descendants, actual inherited completion removes both error and missing. Node demand restricts actual memo fault payloads to busy/absent. Other fault classes remain explicit.
The proposed public theorem needs no additional closed-input, idle-cache, Cap, native Support, causal History, or lower-fuel premise. The initial scheduled Room is still a genuine input. The theorem does not derive Room from failure or growth.

After the new producer and pending ReferenceAbsent are checked, a separate composition can retain all existing stronger assumptions and classify an actual run as done or exhausted. That result would not prove that some adequate outer fuel or initial capacity exists.

The original plan and header are unchanged. The separate scope-stop erratum imposes a 250-total-line implementation stop before any compiler or further implementation. It authorizes no implementation.
The separate dependency addendum records only root's later ReferenceAbsent strict1 authorization. It claims no command launch or successful check.

Owned activity: zero Lean, Lake, canonical, runtime, public proof pairs, constructed fixtures, and official-source edits. All source snapshots and excerpts are read-only inputs. No frozen prior package was changed.
