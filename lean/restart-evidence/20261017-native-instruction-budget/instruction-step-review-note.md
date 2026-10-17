# Independent checked instruction review

No material defect was found in the final two modules.
The reviewed Step source is `a15ffcb49a0550d4d7515bee165abba48acf28f254387379db09946d2a756cd4`.
The reviewed Trace source is `ee353f43dfb7318a923933a406eecd175563c0fa4e20e1703b01d0a7a33c5acd`.
This review changed no production file.

## Exact step costs

`SourceCurrentAllocatedNativeInstructionStep.ControlAt` at lines 29–39 reserves the actual checked edge body and its continuation.
`yielded` at lines 53–160 consumes at least one credit at every actual yielded instruction.
It derives current Good and Extension from the physical input and field checks.
It does not assume a later result law.

The edge-body case at lines 67–79 extracts the literal pure-body code from the same yielded checked result.
The operation cache can change in this step.
The emitted code starts at the same complete returned checked state.
The accepted code pays each original child pair and one makeEdge instruction.
The sentinel code pays one makeEdge instruction.
The initial `2 + L*T + rest` pays the current body effect before `1 + L*T + rest` remains.

The node cases at lines 109–138 use physical current words to identify the captured request.
The direct branch compiles that same request.
The ready branch resumes with the physically available result at the actual returned machine.
The cold branch reserves compiled credit `2 + L*T` and continuation credit `rest + 1`.
The extra one pays the protected finishNode frame.
The sum is at most the original `4 + L*T + rest` minus one.
The edge cases at lines 139–156 use the same arithmetic and retain the captured finishEdge frame.
The raw effect, enter, read, optional binder, and finish cases each consume one credit.
An actual pending optional binder cannot be a yielded step.

## Exact prefix boundary

`SourceCurrentAllocatedNativeInstructionTrace.nodeBudget` and `edgeBudget` at lines 27–42 use the fixed initial source and independent semantic requiredFuel.
These are noncomputable mathematical budgets.
They do not use the measured length of the physical trace.
The `Completes` proof supplies the semantic least successful rank.
It is separate from the current checked executor.
The budget is zero in the incomplete semantic branch.
The public node and edge prefix theorems require the independent semantic completeness proof.

`prefix_bound` at lines 65–88 follows the same admitted physical Trace.
It adds the one-step consumption and transports Fields, source record growth, and issued-key history through the actual returned state.
`node_prefix` and `edge_prefix` retain original source NodeScope or EdgeScope, physical readiness, and source growth.
The native tables and equality operation cache remain the fields of the actual checked trace state.
There is no replacement executor or reconstructed final state.

The conclusions bound yielded instructions.
The terminal pure observation is separate and needs one additional execute fuel unit.
A failure code has vacuous credit, so credit alone does not prove successful completion.
Raw-prefix physical admission, word bounds, successful completion, and constructor allocation charges remain separate proof obligations or later compositions.
No whole-library Haskell correspondence follows from these two modules alone.

## Independent imported evidence

Both final production strict logs are empty and exited zero.
Their canonical builds completed 1200 and 1202 jobs.
Each canonical log contains only the existing ClosedCompletion warning.
All ten public axiom and explicit signature pairs passed imported strict checks.
The integration pair passed with no diagnostics and uses only standard axioms.

The integration builds a literal source with two different ordinary roots.
It constructs its own cold checked receipt from initial physical facts and numeric headroom.
It derives semantic completeness from the original closed operands.
It then applies the new yielded theorem at the exact cold evaluating owner.
It applies both prefix_bound and node_prefix to that same produced physical trace.
Literal evaluations expose edgeBody at fuel 2, finishEdge at fuel 6, and finishNode at fuel 8.
The edge owner is evaluating at the same reached state.
The actual completed memo supplies a literal exact-state warm replay.
The new prefix theorem bounds that replay using the same original source budget.
There is no caller-supplied completed receipt, trace, desired output, or future credit certificate.

The first two failed kernel drafts remain separate snapshots and logs.
They had missing namespace opens and one nested existential tuple error.
The third successful kernel remains preserved before the extra literal body and finish checks.
