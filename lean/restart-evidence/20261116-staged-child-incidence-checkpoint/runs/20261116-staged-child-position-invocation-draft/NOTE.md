# Note [Staged child invocation position]

Status: COMPLETE CANDIDATE. UNCOMPILED. Both public headers were frozen first.

The theorem fixes the specified original position as priorInputs.length in the
literal input list priorInputs ++ (incoming, bucket) :: rest. The prefix is an
input parameter. The proof does not choose it from output equality. A caller
with staged[position] first uses the original list's exact take/drop split.
This is a pure list operation. It introduces no runtime or semantic premise.

The head inversion first classifies the concrete tuple constructor. The done
tag excludes cons_stopped and a stopped tail. It retains the actual child
invocation, its successful callback index, and the exact tail derivation.
It also recovers the original fragment head and SAME final native/cache/query
endpoint. The private generalized cases lemma avoids dependent elimination
through the computed TupleExit.prepend index.

The general theorem uses genuine induction on the supplied input prefix.
Each cons removes one actual completed child from the original tuple trace.
The remaining derivation runs at that child's actual returned caller/cache/
queries and callback-local index. The induction adds its fragment to the
completed prefix and accumulates that prefix into BOTH actual continuations.
The selected child retains its actual root and callback-local indices. Its
tail reaches the SAME original final fragments, native caller, queries, cache,
and terminal localIndex. The recovered prefix length equals the input prefix
length. All child occurrences and duplicate values remain in their original
staged order.

The boundary is an actual TupleExit.done. A stopped tuple does not establish
that a later staged child ran. The theorem makes no such claim. It does not
export a separate prefix execution trace or a new whole-output block witness.
All recovered child and tail traces come from the SAME constructor induction.
It does not assume an output equality, future invocation, policy law, source
resource, semantic model, or independent existential completion witness.

The ordinary source Note [Indexed invocation ancestry] owns the shared rationale.
The raw module adds Note [Staged child invocation position] next to its proofs.
Arbitrary width/Output/Reason, actual policy, checkEmpty and all r/n/p/h/k values
retain their original scope. Default checker limits and autoImplicit false
apply. No compiler or Source/Git/board/tmp command was run.
Historical raw-alias transport, target typing/compatibility, native/guard laws,
and the full original-root joint finite completion remain separate obligations.
