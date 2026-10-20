# Proposed unbound request induction

Status: proposed proof design. The owner theorem remains unproved.
The root and required_memos checked this route against the current controls.
This check adds no Lean job, declaration or proof pair.

Use strong induction on the actual prefix fuel of an unbound requestNode
or requestEdge. A compiler prefix has already consumed the enclosing query
step. A nested callback prefix can use the same fuel as its compiler prefix
and still use less fuel than the enclosing request. Do not assert a strict
decrease at a zero-cost pure boundary.

Split a protected compiler body with bind_prefix_cases. A completed body
leaves only finishNode or finishEdge followed by pure. That suffix cannot
reach an optional instruction. A ready memo hit also yields pure. Therefore
an optional site in an unbound request prefix is inside its actual compiler
body. No arbitrary continuation-stack relation is needed for this case.

Checked edgeBody does not add a later optional continuation. Errors and
blocked outcomes cannot be crossed by a yielded Trace. Its sentinel branch
is Work followed by pure. Its accepted child branch uses the indexed walk
splitter, then makeEdge followed by pure. The actual allocated conjunction
must remain; do not replace the checked branch with the older eager compiler.

For an unbound compileMu, split its body request. An unfinished body prefix
can contain a nested query owner. A completed body reaches the current
owner's optional instruction only when the remaining suffix uses zero
steps. Crossing that optional instruction yields pure or stops blocked.
It cannot reach a later optional instruction in this unbound body.

Two small structural helpers remain to be proved. First invert equality
between inner.bind continuation and the selected optional control under
the existing nonpure-inner condition. Retain the exact pair, body and full
continuation equation. Second lift a recovered owner receipt through
Trace.bind and compose its full continuations. Retain the same query prefix,
capture, child return, selected site state and exact count equation.

A private compiler classifier can return either its own entered Mu site or
a nested query owner. The enclosing actual memoized query supplies the
captured owner handle in the first case. The nested case keeps the actual
earlier query. A direct final Mu owner is excluded by sourceKey_complete;
direct non-Mu calls can still contain a nested owner and must be traversed.

Keep queried and captured requests distinct. Their equality still needs
physical cache validity. The proposed syntactic producer supplies no
original program binding ancestry, global renewal or general completion.
This supplement does not change the checked four public declarations.
