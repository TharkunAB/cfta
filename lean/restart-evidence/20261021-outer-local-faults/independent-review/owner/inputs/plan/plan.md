# Remaining outer local faults

This is a source-only proposal. It contains no checked new declaration or execution claim.
The pending ReferenceAbsent component remains unproved at this plan cue. Its author reported source-only 254/67b68404 and compiler hold.

## Exact fault inventory

1. Worker.Fault has exhausted, nodeMemo, edgeMemo, unexpectedReference, binder, parent, inherited, and missingInherited constructors [S1:32–41].
2. nodeCall emits nodeMemo only with busy or absent. Ready returns done. Evaluate forwards an actual body fault [S1:60–71]. The datatype alone does not exclude ready/evaluate fault payloads.
3. edgeCall emits edgeMemo only with busy/absent or forwards Parent failure [S1:98–117]. Existing no_edge_memo_failure already excludes EVERY edgeMemo observation under its genuine initial packet and EdgeIdle [S8:43–89].
4. Existing no_parent_failure excludes EVERY Parent fault, but requires all nine explicit phaseNeed lower-fuel inequalities as well as its initial packet [S9:36–68].
5. Existing no_node_busy excludes busy only and needs initialNodeIdle plus its stronger initial resource packet [S10:26–69]. Pending ReferenceAbsent targets reference and absent, not arbitrary nodeMemo payloads.
6. Binder faults can arise only from actual rebuild.pending at a Mu body. Inherited/error and missing arise only at the actual descendants prefix [S1:74–95,134–147].

## Smallest useful next producer

Propose SourceCurrentOuterLocalFaults.failed_cases with the exact accompanying header.
It takes the existing InitialPrefix resource packet and one literal failed run. It returns only exhausted, nodeMemo busy/absent, edgeMemo, reference, or Parent alternatives.
It removes binder/inherited/missing and proves nodeMemo provenance in one local six-phase induction. It does not require closed inputs, idle caches, native positive Support, causal History, or additional lower-fuel bounds.
No public fault predicate, graph framework, postcondition callback, or new cache invariant is needed.

## Actual proof route

Keep the fixed initial phase and packet. Each local induction argument retains a literal Reached prefix from that phase to the current phase.
Node evaluation uses Step.node_evaluate. Ordinary bodies, row heads/tails, descendants, live children and indexed walks use the existing eight Step constructors with SAME completed equations [S2:325–382].
At a Mu body, call InitialPrefix.reached at THAT prefix. Use its post.context.ready/probes and Inputs.available with resident_rebuild. The actual rebuild is done at the SAME heap; it cannot emit any binder fault [S3:263–286,S4:481–489,S5:24–35,S6:142–159].
At descendants, the SAME prefix supplies current ready/admitted, inherited Ready and returned-edge residency. resident_finite returns an actual ok(some combined) equation. This excludes error and none at THAT entry, before following children [S7:93–110,175–184].
The failure caller in these branches may contain actual updated operations. Retain the entry cut and literal prefixState; do not identify the failure caller with that entry.
Local nodeCall ready/busy/absent cases and bind inversion establish the restricted nodeMemo alternatives. No arbitrary observation is accepted from a datatype case alone.
The initial run erases successful output only. On failure that erasure retains the same fault and full caller [S11:245–252,S1:48–55].
Expected source size is about 220–280 lines. Stop at 250 for full scope review if implementation is later authorized. No source implementation is authorized by this plan.

## Subsequent composition and boundary

After this producer AND ReferenceAbsent are checked, case analysis can combine existing Parent/edgeMemo/busy/reference/absent exclusions. Keep every required initial assumption, EdgeIdle/NodeIdle, conditional closure store, and nine lower-fuel bounds explicit.
That composition would classify an actual run as done or exhausted. It would not provide SOME adequate outer fuel, a fuel-independent initial Room producer, or arbitrary capacity. Those remain separate obligations.
No Lean, Lake, runtime, canonical, official-source, or proof jobs were run for this proposal.
