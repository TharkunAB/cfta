# Actual checked contextual cache execution

Date: 2026-10-16 04:51 CEST.
Owned new module: lean/MicroCFTA/SourceCurrentAllocatedNativeContextExecution.lean.
SHA256: 5e16fab8c4391e03e55b6d367d17b44d66fa198fd360cf0e0af9528b7b970dd6.
The module and evidence are frozen. Earlier proof files were not edited.

## Exported contracts

All results keep fixed `view`, `model : InputMeaning view`, `ranked : RankedInput view model.valid`, and `holds` from ContextCache.

- `FinishLaw view model ranked holds control state` is True for all controls except finishNode and finishEdge. At a finish it requires a NodeLaw/EdgeLaw for each literal request whose cell is currently evaluating at that exact handle. If the cell is absent or already suspended/returned, no new law is needed because actual finish performs no new publication.
- `FinishThrough view model ranked holds fuel control state` follows only the actual checked step/yield sequence. At fuel zero it is True, since no instruction executes. At a positive fuel it requires the current FinishLaw and recursively follows the actual yielded control/state. Other outcomes stop the requirement.
- `body_contextual ... request next state context` derives Contextual at `(SourceEqualityNativeDemand.body request next state).state.native` unconditionally. Actual body outcomes include arity mismatch, load error, missing original field, checked conjunction error, rejected constructor, and ready continuation. The complete native state is unchanged by this body, although its literal operation state can change.
- `step_contextual ... control state context localLaw` derives Contextual at the exact actual checked step outcome state.
- `execute_contextual ... fuel control state context localLaws` derives Contextual at every actual finite checked outcome state, including yielded, done, failed, constraintError, and blocked.
- `done_contextual` specializes the finite result using an actual checked `.done value after` equation. It takes no final validity or result availability premise.

## Proof mechanism

Actual native lookup and demand use ContextCache lifecycle lemmas. Work, enter, and optionalBinder advance the machine while retaining the same completed cells and immutable independent model. OptionalBinder covers actual done and pending results. Actual checked edge publication uses its real lookup/demand branch, then its edgeBody control; it does not run the old eager compiled edge body.

Non-edge checked code delegates to the existing primitive native step by definition. The proof unfolds that actual dispatch. It supplies no old eager execution, old completed body receipt, or execution erasure premise.

Only an actual finish of an evaluating cell introduces a new returned law. The current handle's original request is read from the current cell, and the local FinishLaw supplies exactly that request/result law. No desired root answer, completed callback, future Contextual, NodeProduced, final Valid, Ready, or whole-trace semantic oracle occurs in the premises.

Contextual is only the added semantic cache invariant. These theorems do not prove physical heap validity, availability, equality-cache validity, or word-key safety. Those existing physical invariants remain separate. The operation cache is the actual interpreter's returned cache; it is never replaced with an initial or synthetic state.

## Validation

Focused command:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceCurrentAllocatedNativeContextExecution

Terminal exit 0, 1062 jobs. Only the preexisting unused-input warning appears. Log: guard-context-execution-build.log.

Probe command:

    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean env /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean lean/restart-evidence/20261016-recursive/guard-context-execution-probe.lean

Terminal exit 0. Four public axiom checks use only propext, Classical.choice, and Quot.sound. Six public signatures and twelve proof/kernel examples pass. Examples include zero-fuel finish-law absence, nonfinish/edgeBody checks, exact pure/failure outcomes, actual absent-cell node and edge finish behavior, and contextual retention without an output-language premise. Probe source and log are preserved alongside this note. The module source copy is guard-context-execution-source.lean.txt.

## Remaining obligations

This module does not derive local NodeLaw/EdgeLaw at all new actual completions. The recursive Mu/body rank induction and the construction of FinishThrough for a general checked program remain the main semantic obligations. General checked native completion, source runtime lazy forcing/publication, machine identity capacity, and whole class-query composition are not claimed.
