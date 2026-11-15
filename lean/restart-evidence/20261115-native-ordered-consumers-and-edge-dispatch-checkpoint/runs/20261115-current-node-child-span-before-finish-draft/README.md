# Completed node child before the observed parent finish

Status: UNCOMPILED. This packet has no proof credit.

The public header was frozen before the proof. The byte comparison passes.
The packet adds one theorem in a new module. Existing sources stay unchanged.

The actual checked root trace ends before the selected parent finish.
Its count is exactly queryUsed + 1 + bodyCount.
The input retains the original isolated dispatch and body return.
It also retains the positive child prefix and completed raw child trace.
The captured owner and Shape are past facts at beforeBody.
The original bound remains bodyCount < parentFuel.
No child span bound is an input.

The proof splits the child prefix after the actual parent dispatch.
It then splits the compiled body through its captured finish continuation.
A child node head cannot occur after the isolated parent finish.
That finish resumes pure code, which cannot yield another child request.
The child continuation therefore retains the parent finish frame.
Its completed endpoint cannot be pure.

The proof constructs the raw isolated parent completion from the dispatch,
observed body return, and one real finish step.
Steps.length_le_complete bounds the completed child prefix.
Steps.execute determinism excludes equality at the parent's pure endpoint.
The result is childUsed + childCount <= 1 + bodyCount.
This also derives the bound at the original parentFuel.
The temporary finish step does not enlarge an induction hypothesis.
It is not claimed to be a step of the observed root prefix.
No observation step is added to the child count.

The public PhysicalSplit.split theorem selects the checked child prefixes
and suffix from the actual root trace.
PhysicalSplit.unbind recovers the isolated checked child return.
The existing node_body_owner theorem supplies the exact evaluating and
returned owner receipts at the observed parent endpoint.
All six Checked states remain literal full states.

Scope: a completed NODE child with a positive isolated-parent prefix.
The theorem can support the existing Mu and union callbacks.
The ordinary-node proof has a separate direct Walk decomposition.
This packet proves no Profile clause, global C/M closure, source-worker
admission, Haskell correspondence, or full finite joint witness.

Check: compile the candidate with the two appendable commands in
PROBES.lean.txt. The probe file has no import declaration.
The parent owns compilation and publication.
