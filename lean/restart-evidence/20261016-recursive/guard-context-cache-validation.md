# Contextual completed native cache validation

Date: 2026-10-16 04:45 CEST.

## Artifact preservation

The execution environment changed during the first probe attempt. The earlier /tmp probe sources, logs, review notes, and marked drafts are not visible in the refreshed environment. A read of /tmp found only current root-owned source build/test/ClosedReceipts logs and system directories. No missing earlier evidence is claimed as recovered. The repository source and compiled modules survived. This directory contains a new source copy and fresh post-refresh validation evidence.

Owned source: lean/MicroCFTA/SourceCurrentAllocatedNativeContextCache.lean.
Source SHA256: eef24f799571d5900e746fd9f7b4207a533763b1ed50522857f196296cc7274b.
The source is frozen. No earlier proof file, Haskell source, Audit, documentation, or Git metadata was changed by this task.

## Contracts

NodeLaw and EdgeLaw use a fixed independent InputMeaning, RankedInput, and guard interpretation. Node operands use their actual inputOf values. Edge languages retain literal symbols, full guards, and ordered child inputOf values. Soundness ranges over actual request.domain.key SoundPairs contexts. Completeness ranges over the corresponding CompletePairs contexts, with the sum of the two original ranks at most the specified bound.

NodeInputs explicitly restricts applications to Original operands in the fixed model's valid domain. EdgeInputs gives the same restriction for each actual ordered child. A returned-cell law is conditional on this input scope. It is not an assertion of semantic correctness for arbitrary generated operands outside that domain.

Contextual checks only returned node/edge phases. It does not duplicate physical availability, word-key safety, table linkage, or closed NodeProduced provenance. The existing physical Valid remains a separate warm-cache invariant. Contextual is therefore strictly additional context-sensitive information, not a replacement for physical validity.

initial_contextual has no completed-answer premise. lookupNode_contextual, lookupEdge_contextual, demandNode_contextual, and demandEdge_contextual follow the actual native operations and retain the laws. advance_contextual keeps the same independent model and memo cells while the machine changes. It proves contextual retention only; physical machine growth/validity must be supplied by the separate physical invariant.

finishNode_contextual and finishEdge_contextual require the exact currently evaluating original cell and a local result law for that request. Derivation of these new laws, especially the recursive Mu case, remains the main semantic obligation. The lemmas do not assume a desired root answer or final cache correctness.

node_ready_contextual and edge_ready_contextual recover the candidate request's law from a current published returned cell. Physical key injectivity identifies the complete captured original request. node_observed_ready and edge_observed_ready instead consume the actual lookup and ready-demand equations, derive the stored original receipt, and return the requested law plus unchanged demand state. They do not replay a completed body or assume a future invariant.

## Focused validation

Fresh command:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextCache

Terminal exit 0, 1061 jobs. Only the preexisting InternedFreshOrdinaryClosedCompletion unused-input warning appears. Log: guard-context-cache-build.log.

Fresh probe command:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-recursive/guard-context-cache-probe.lean

Terminal exit 0. The probe checks all 12 public lifecycle/hit theorems and seven public signatures. Only propext, Classical.choice, and Quot.sound occur. Twelve examples check a genuine open repeated-reference contextual law, the inclusive rank-sum bound, and literal publication/suspended/evaluating/returned/late-hit/busy/finish-retention behavior. Source and output: guard-context-cache-probe.lean and guard-context-cache-probe.log.

The first fresh probe needed an explicit rewrite of InternedGuardedLanguage.meaning for the open reference example. That change was only in the probe. The production source needed no post-refresh edits.

## Remaining obligations

The module does not derive local NodeLaw/EdgeLaw for all new actual completions. It does not complete the Mu/rank induction, general checked native execution, semantic finish checks, or contextual warm-cache initialization from runtime histories. It does not transfer logical publication to GHC forcing, concurrency, machine-word identity capacity, or native table implementations. Root and the MuMeaning component own those next compositions.
