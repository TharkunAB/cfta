# Source and instance context

The runtime section fixes Typing to Unit and native width to bits + 2. It uses
Symbol, EdgeKey and Node DecidableEq for the actual eager visitor and worker.
The frame datatype stores raw source data and mathematical tail parameters.
It stores no resource certificate and no abstract native callback function.

The parent-tail helper takes a pair of SOURCE callback functions only. The
frame evaluator supplies that pair by structural evaluation of its parent.
No external caller supplies a resource contract for those functions. The root
hook is the literal continueWith/resumeWithNarrow identity/noStop worker.

The mathematical frame plan and reserved functions omit all three equality
instances. Their selected case is the original tuplePlan/tupleReserved for
the parent tail. Their captured case is the original eagerFinal/eagerReserved.
The plan growth proof also omits those instances. No new guard alphabet or
future heap size hypothesis appears in these definitions.

The handoff's current resource inputs are exact inner IH fields. Its current
mathematical reserved premise is capacity, not a native postcondition. The
first-callback lemma derives the exact reserved tail. The source current own
receipt and full inner tuple certificate derive the node ChildInputs. The
existing current-head extension then derives the outer prefix. The source
Packet is extracted in a scoped proof to preserve the original prefix proof.
The returned native Post supplies Keeps. All returned native arguments refer
to the actual reached caller. The residual cache's suspended mass is unchanged.

The runtime generation proof and callback equation retain workFuel exactly.
No larger worker or different child backend is evaluated. The old 29-proof
prefix and all archived original target headers remain byte for byte.
