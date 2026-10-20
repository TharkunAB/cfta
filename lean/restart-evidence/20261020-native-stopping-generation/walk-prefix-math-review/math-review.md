# Native walk prefix: independent mathematical review

Reviewed on 2026-10-20 at 18:32 CEST. No material mathematical issue was found. The candidate SourceCurrentNativeWalkPrefix.lean has SHA256 139bf66a4700193394d03843c01fed696b6d4a930fa0815107432cebd24762ee. The complete statement and proof were read against the live dependencies. No Lean job or new proof pair was run.

## Exact contract

walk_prefix_cases takes one actual physically checked yielded Trace of the original ordered walk with its appended continuation. The final control is arbitrary. The theorem derives either an exact original input index whose call remains nonpure, or the actual completed walk and a reached continuation prefix. It assumes no future walk completion, selected split, desired child answer, semantic law, or owner receipt.

The unfinished branch retains inputs[index]? = some input. It retains Walk over inputs.take index, from the original checked state to the exact selected call entry, with the actual completed values in source order. It retains the actual call Trace to the final checked state and an inner control that differs from every pure return. prefixFuel + currentFuel is the original fuel.

The continuation keeps walk call (inputs.drop (index + 1)) and passes values ++ (value :: tail) to the original next. These are occurrence indices. Equal input values at different positions do not identify their indices. No uniqueness is asserted.

The completed branch retains Walk over all original inputs, its exact middle state and values, and the actual Trace from next values at that same middle to the final control and state. walkFuel + outerFuel is the original fuel. The completed walk is derived, not supplied.

## Proof review

For empty inputs, walk is pure []. Binding it starts next [] immediately. The existing actual Trace therefore supplies the continuation prefix. Walk.nil takes zero fuel and preserves the whole original checked state.

For a nonempty list, Code.bind_assoc rewrites the actual bound walk to the first original call with the actual rest continuation. bind_prefix_cases supplies either an unfinished nonpure first call or the actual first return and tail Trace. It retains physical checks through inputs_before_bind.

An unfinished first call uses index zero, an empty completed prefix, and the unchanged rest. If the first call returns, induction processes the actual tail at that exact returned middle. A tail index becomes index + 1 in the original list. List.getElem?_cons_succ preserves the original selected input. Walk.cons prepends the first actual call to the completed take prefix. The original tail is recovered by List.drop_succ_cons. List.cons_append preserves the accumulation order. The first value is not reversed or duplicated. Natural-number count equalities combine only the two actual decompositions.

If induction completes the tail walk, Walk.cons constructs the actual whole walk before the derived continuation Trace. The proof never introduces a completed enclosing query or chooses a later source result.

## Source foundations and limits

Walk in AllocatedNativeSemanticTraceReadback records actual child return traces in order. Physical Trace records each reached current input check and yielded checked step. NativeTracePrefixBind is the previously checked exact partial bind splitter. Its first alternative is nonpure; its second derives an actual return. Pure returns add no inner instruction.

The new theorem is a physical prefix statement. It does not classify a terminal failed or blocked step as yielded. A consumer must derive the actual yielded prefix to which it applies. It does not by itself recover a captured compileMu owner, original source ancestry, a publication history, memo retention at a later reader, or any semantic equivalence or termination law.

## Existing validation and preservation

The selected existing strict run is walk-prefix-direct-2. Its source equals the reviewed candidate and its log is empty. The existing walk-prefix-public-1 readback prints the sole public declaration with all eight required options, complete proof and axiom report. Only propext, Classical.choice and Quot.sound occur. Both reused jobs have effective memory.max and memory.high 4294967296, memory.swap.max 0, a five-minute cap and a fresh usage gate. The owner's earlier failed attempt stays in its original frozen package; it is not a selected review run.

This package adds zero Lean jobs and zero proof pairs. It reuses one checked public pair. Candidate and receipt snapshots are local to this package. ROOT foundation snapshots retain the exact live dependency bytes. The default verifier checks frozen data. --live-root also checks those dependencies against the current repository. The previous stopping-prefix review and all current checkpoint evidence remain unchanged.
