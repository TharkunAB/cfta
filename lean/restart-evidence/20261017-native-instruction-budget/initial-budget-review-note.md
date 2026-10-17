# Independent initial instruction-budget review

Reviewed on 2026-10-17 at 07:40 CEST. No material defect found. No production source changed.

`SourceCurrentAllocatedNativeInitialInstructionBudget.initial` constructs its own complete checked physical receipt from initial Good, SemanticReady, Idle, closed Original available operands, and explicit initial node, edge, and domain headroom. It takes no physical Trace, WordRanges, instruction count, intermediate heap bound, or desired output law. `complete` is the lower adapter. Its explicit semantic completeness, active-owner bound, and WordRanges premises remain visible. `initial` derives these premises from its initial facts.

The initial heap fixes `InstructionProfile.sourceBranching`. Actual source readback bounds the row hash join, union members, and ordered child zip. `InstructionTrace.nodeBudget` applies T(0)=0 and T(h+1)=4+L*T(h) to the source semantic requiredFuel. Completeness makes that rank positive. `CompileInstructionCredit` proves the smaller child charges for every literal node branch, including Mu, union, reference, reset, and swap. Checked edge code derives its charge from the actual accepted or sentinel choice.

`InstructionStep.yielded` spends at least one credit on each actual yielded step. A node miss retains its captured finish continuation. An edge miss pays publication, the checked body, final constructor, and finish. Warm hits spend one instruction and preserve the actual returned payload. The physical trace still supplies exact current input and owner checks. Credit is not used as a substitute for these checks. `InstructionTrace.prefix_bound` follows that same trace and fixes its initial amount before execution. It does not define the amount from the trace length.

The endpoint obtains its own old physical completion receipt, applies the prefix bound to that same trace, and uses exact interpreter stability at nodeBudget+1. `WidthTrace.node_return` supplies the actual returned heap bounds. MassMonotone lifts those bounds from the actual trace length to the initial instruction budget. Result, native tables, domain cache, and equality operations all refer to the same complete checked return. Idle restoration uses that same completed execution.

## Imported integration evidence

`initial-budget-review-public-1.log` checks the full signatures and axioms of complete and initial. `initial-budget-review-kernels-3.log` checks two constructed theorems. Both kernels have no initial theorem premises.

1. `initial_ordinary_cold_warm` builds a closed source from the empty constructor heap. Its two ordinary roots differ. The literal cold request publishes an evaluating node owner and reaches a checked edge body. The initial endpoint constructs its own receipt, trace, exact budgeted execute, final store, result mass, and all counter bounds. The same receipt then derives the root returned cell and an exact two-step warm replay. The warm result retains the entire returned checked state, including populated native tables and equality operations.
2. `initial_mixed_recursive` builds a productive raw Mu and an ordinary constant inside a two-member union. The queried operands are the Mu and that union, which differ. Initial numeric headroom and source facts construct its own finite checked receipt and all resource bounds. No pre-completed query is supplied. The large payload ceilings remain symbolic.

Attempt 1 used equality reflexivity for Idle. Lean rejected that term. Its exact source and failed log remain diagnostic evidence. Attempt 2 passed the ordinary kernel with the actual initial-idle theorem. Attempt 3 adds the mixed recursive kernel and passes both pairs. Only attempt 3 is final integration validation.

## Scope

The instruction budget is a mathematical, noncomputable function of semantic requiredFuel. This is not an executable syntax-only fuel calculation. The initial counters and conservative domain-inventory headroom are explicit; the theorem does not prove that any fixed host width is sufficient for every input. Idle is required for completion, although the separate initial-range theorem admits populated tables without Idle. Busy-owner states are not silently included.

The endpoint returns physical correctness, availability, exact interpreter completion, and mass/allocation bounds. It does not itself return NodeLaw or a contextual language-equivalence receipt. Those semantic composition results remain separate. New result-fed queries need their own initial admission and source transport. Final constructor counter bounds do not imply later word capacity. These claims concern the checked Lean executor; they do not establish an all-instruction host timing bound or complete Haskell correspondence. This review found no new Haskell behavior defect.
