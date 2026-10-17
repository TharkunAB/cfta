# Exact native decision support

KernelJointDecision is frozen at 1a6fa78e783fab70735b51a6aab2be5bd2bbb0134d229553395bf401ba8ce700. It adds two public lemmas without a completion, result law, numeric headroom, or future trace premise.

`repeated_weight` follows the literal decision order. Empty, reset, self, and swap cannot select a repeated result. It obtains the actual two numeric identities from the remaining match, and obtains the sorted pair from the selected constructor. A payload branch cannot return a repeated constructor. Existing NativePairWeight.pair_weight then uses actual immutable source Facts, OriginalBindings, NodeInputs, availability, and interned coverage. The result does not assume that constructor tags determine numeric identity order.

`reset_inputs` follows the same decision order and obtains both actual free fields as empty from the selected reset condition. It retains the original syntax and availability components. Empty-domain interned coverage is then derived from those empty free fields, rather than copied from the nonempty old domain. No source binding law is required merely to derive the reset input tuple.

The constructive kernel builds one closed source with two distinct false-guard nullary children. It obtains the actual source Facts and both available children. A nonempty-domain call on the same first child selects reset before self and produces empty-domain NodeInputs. An empty-binding domain with the actual sorted pair in seen selects repeated for the two different children and produces their exact source-weight equation. The source execution is constructed inside the kernel.

The production strict attempt 2 has an empty log. Attempt 1 and its exact source remain. Both public axiom/signature pairs and the constructive kernel pair pass with full explicit printing and standard Lean axioms. The designated combined canonical build passed 1163 jobs. This module supplies actual branch facts for a separate joint source execution induction; it does not itself assert recursive completion.
