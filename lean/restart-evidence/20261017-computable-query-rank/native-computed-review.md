# Computed checked native-query budgets

Frozen on 2026-10-17 at 07:59 CEST. Source: SourceCurrentAllocatedNativeComputedBudget.lean, SHA256 82d4affc8d0e587504f9f8cdfaf37dc34e946d4de7e7d5f8a7a690b60e8983b8.

The module exports instructionBound, instructionBound_mono, nodeBudget_le, and initial. Let N and E be the initial node and edge counters. Let Stored S hold on the actual initial constructor heap. The computed instruction bound is InstructionProfile.budget (NumericSourceProfile.branching N E S) (ComputedFuel.ceiling N S). Both numeric functions are independent of a completed trace and of a selected least successful semantic fuel.

nodeBudget_le first derives semantic completeness from the closed Original available roots. ComputedFuel.initial_requiredFuel_le bounds the least semantic fuel from those same initial facts and Stored S. NumericSourceProfile.source_branching bounds the fixed source branching. Parameter monotonicity then bounds the older semantic instruction budget by the computed one. No successful physical execution, future instruction count, or desired result law is supplied.

initial accepts the same initial Good, SemanticReady, Idle, Original, availability, closedness, and numeric word/domain headroom as NativeInitialInstructionBudget.initial. It adds causal Stored S. It uses the older endpoint to construct its own physical receipt. It retains that exact receipt, Idle, and count. It does not use the older recomputed-initialBound resource outputs. The new module contains no initialBound term.

The proof applies WidthTrace.prefix_bound to the SAME receipt.trace, with initial Fields, the supplied Stored S, and the initial CodeMass.request_node certificate. It obtains resources at the actual trace length from S. Count monotonicity widens that same store and both counter credits to the computed instruction bound T. Receipt.result and the derived store bound the actual returned payload. Interpreter stability gives exact execute(T+1) on the same control, input, result, and complete checked output. Native tables, equality operations, and the domain cache stay joined through that receipt.

## Imported validation

Production strict attempt 2 passes with an empty log. Single-target canonical build native-computed-canonical-1.log passes 1282 jobs. Its only warning is the existing replayed InternedFreshOrdinaryClosedCompletion inputs warning. Public validation checks all four full explicit signatures and axiom reports in native-computed-public-1.log. Final integration native-computed-kernels-5.log passes two full explicit signature/axiom pairs. Both public integration theorems have no supplied initial or completed-query premises. Only standard axioms occur.

computed_ordinary_cold_warm constructs a closed source from empty with distinct ordinary roots. It observes actual cold owner publication and a checked edge-body prefix. The computed endpoint then constructs its own finite receipt, exact execute at T+1, final store, result mass, and all supplies. The SAME trace derives the final returned cell and exact warm replay with the whole populated checked state unchanged. No OutputFinite result or future trace is a premise.

computed_causal_mass constructs an ordinary constant through actual edge and node Work. It derives Stored 3 and proves that recomputed initialBound is 5. Its own initial query returns Stored(massAfter T 3), result mass at that bound, and counter credits credit(T,3). This tests the causal-mass argument directly. A private proof takes that initial mass parameter before instantiation. A literal let retains the computed instruction bound in the final public signature. The proof does not evaluate the enormous payload ceiling.

Production attempt 1 retains its request-inference error. Kernel attempts 1 through 4 retain numeric evaluation diagnostics: Lean refused a Nat.pow exponent outside its evaluator's 32-bit limit during closed-term checking. These logs are failed validation, not false bound counterexamples. Each exact attempted source and raw log is retained. The final proof uses symbolic numeric bounds and passes without a production change.

## Scope

The new T is computed from N, E, and S. The proof no longer leaves semantic requiredFuel as the public instruction budget. These are mathematical natural-number bounds. They do not establish practical cost, byte usage, a fixed host word width for every input, or a host runtime bound.

Original closed requests can contain Mu, explicit unions, and supported references inside their source. Guard annotations are not restricted. Existing Good, semantic readiness, Idle, and explicit initial capacity premises remain necessary. The endpoint returns physical availability and resources. A NodeLaw or contextual language-equivalence receipt remains a separate semantic composition. Generated-result serial queries need preserved causal stores, source rebase, and next-entry numeric headroom; this module does not assume or prove those later entry conditions. No older source, Haskell file, Audit file, or restart document changed. No new Haskell behavior defect was found.
