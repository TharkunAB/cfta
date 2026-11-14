# Exact remaining nonempty eager connection

The ordinary eagerChild branch is not CapturedEdge.run. It scans edgesOf and
calls each completed child's tuple continuation before it visits the next
ordinary edge. CapturedEdge.run uses the shallow ChildDispatch singleton
traversal. That worker does not execute this eager ordinary recursion.

The public eagerChild_fallback equality applies when ordinaryNonterminal is
false. An empty child list also executes no visitor. Neither fact supplies an
ordinary nonempty-tuple equality. A shallow receipt must not replace that tuple.

The existing EagerChildCompleteWithOutputs and EagerTupleCompleteWithOutputs
interfaces produce a stable result only after a derived adequate bound. Their
consumer interfaces quantify over later successful continuation resources.
They cannot be used as pointwise same-budget induction hypotheses.

The first missing nonempty step must derive the resource certificate of each
actual eager child at its actual callback endpoint. It must preserve the
current ChildInputs fields: Post, exact query, Packet, counter growth, old
enumerated origin, protected roots, permitted references, fragment bound,
pending fragment and fragment separation. It must also derive the actual
Fits and Heap for the next tail and every emitted child output. The tail then
uses the exact returned caller, full memos and cache at the same workFuel.

This step requires genuine induction on the smaller ordinary child height.
The checked prepared_child_lt law supplies that decrease. The remaining tail
requires genuine induction on its shorter list. Completed top-level callbacks
use the smaller worker-depth hypothesis. No universal future callback packet
can replace these inductions.

The candidate closes the empty child-list case. It derives TupleInputs through
tuple_inputs_nil and derives ChildInputs through own_tuple_child_inputs. It
does not assume either resource certificate. Nonempty eager tuples, the
prepared scan, the full worker and the common finite witness remain OPEN.
