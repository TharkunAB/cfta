# Independent review of ClosedReceipts

Date: 2026-10-16 04:45 CEST. Read-only review. No root-owned source edits or builds.
Reviewed: lean/MicroCFTA/SourceCurrentAllocatedNativeClosedReceipts.lean, lines1-116.

No concrete defect or scope overclaim found.

1. input_finite at lines24-31 handles the tagged empty input explicitly, rather than incorrectly reading an identity language for Empty. Other tags use the independent supplied rank-erasure equation. The source-model constructor later derives that equation from original finite input derivations.

2. node_closed_exact at lines34-55 uses the explicit NodeInputs scope and local NodeLaw. Actual empty-domain equality makes SoundPairs and CompletePairs vacuous for every output environment. Each accepted original operand term obtains its own original derivation rank. The completeness call uses their sum as the bound, with equality permitted. No output closedness, result acceptance, or desired root equation is supplied as a premise. NodeLaw itself is the explicit local semantic component obligation; this theorem does not purport to derive it.

3. node_meaning at lines58-72 is a generic adapter. Its physical input readback premises concern only each original operand, conditional on that operand being closed. These are independent input correspondence laws, not output semantics. Its conclusion is the existing NodeMeaning predicate, which is conditional on empty domain and closed operands. It is not an open-domain contextual correctness theorem.

4. node_produced at lines75-94 uses literal actual checked execute fuel (.code (compileNode request)) before = .done value after. It stores precisely that before, after, fuel, ready input, Extension, and returned availability in the new NodeProduced receipt. It uses reflexive growth only from the actual after machine to itself. There is no final native Valid assumption, no old eager-body execution, and no replay or invented intermediate state. Actual completion, physical effects, availability, input readback, and local contextual semantics remain explicit component premises, as the header states.

5. source_models at lines97-114 supplies the real source instantiation of the generic input premises: source Facts, Original syntax, actual source availability, and both original free fields empty. PairContexts.source_input_models constructs the fixed InputMeaning and RankedInput from original input derivations and proves each physical language readback. No output value or output environment is used to select the models. The returned implication NodeLaw -> NodeMeaning is a useful derived adapter, not a proof of NodeLaw.

6. The statement does not claim every actual native query completes, every reached finish already has its semantic law, or arbitrary warm open cells satisfy the new contextual cache invariant. General recursive Mu/rank induction and contextual cache preservation through whole checked execution remain explicit. The initial source readback/domain premises must still be discharged by a construction/caller endpoint when this component is used.

A minor scope detail to retain in future summaries: the generic node_produced can be instantiated for a nonempty domain because closed NodeMeaning is then conditional. The component's substantive exact-language result is node_closed_exact at the actual empty domain. It does not replace the stronger open-context NodeLaw.
