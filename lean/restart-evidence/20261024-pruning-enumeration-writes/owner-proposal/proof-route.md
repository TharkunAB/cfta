# Proof route only

Both statements derive the handle and exact readback from existing available_readback. Neither accepts a decoder, desired returned node, final realization, or output law as a premise.

Allocation uses allocate_exact for actual Success and allocated_slot with the explicit alignment for the returned UVar. For final realization, convert an actual post-write indexed read into payload membership. Split append membership into an old payload or the one new payload. Recover an old index with getElem?_of_mem and apply the incoming realization, or eliminate constructor equality and use the actual value/decoded/available/closed packet.

Raw write chooses the literal record update as its existential final state. modify_success supplies actual setValue success after unfolding that definition. getElem?_set_self uses the explicit inside bound to derive the new raw-slot readback. For final realization, mem_or_eq_of_mem_set gives an old payload or the new payload. Use the same old-index recovery or constructor-equality elimination.

This route has no helper, have, let, induction, by_cases, case equation, or typed show. The old/fresh split is an obtain/rcases disjunction. All named and anonymous binder types are recorded in scoped-types.json. The literal change statements expose only definitionally equal list views; they are review metadata, not proof bodies.

The native heap stays the same. These theorems preserve the complete existing enumeration state returned by the actual modeled actions. Allocation retains its inherited ancestry. Raw replacement changes only values. The raw slot need not be a union-find representative; the operation intentionally writes the supplied raw slot.
