# Actual selected Mu body validation

The source is frozen at SHA256 b24e1661cde32eb9e35fe40aa87a8fb5b90caf41323f053b8205cd7d7e7041d5.

The canonical focused build passes 1097 jobs. One public axiom report and
one signature check pass, with three additional kernel examples for the
both-Mu, left-Mu, and right-Mu compiler selections. Only standard Lean
foundations occur. No new warning occurs.

mu_body consumes the exact entered child physical Trace and that child's
local NodeLaw, Keeps, and Available. It derives the reached heap checks from
Trace.plan, then derives middle SemanticReady from the initial semantic heap
through actual checked execution. It does not assume a final guarded heap.
Available child output derives actual optionalBinder completion. The existing
rank-sum Mu proof and literal source bindings derive the parent NodeLaw.
The selected source branch rewrites the endpoint to actual compileNode.

The actual trace consists of enter, the complete child trace, optionalBinder,
and the terminal pure observation. Its execution bound is child fuel plus three.
The output keeps the actual middle operation cache and both native memo tables;
only the constructor heap advances. The theorem returns Keeps, Available,
and SemanticReady at that literal returned state.

Initial fixed original InputMeaning, RankedInput, source Facts, NodeInputs,
source operand availability, domain Cache.Valid, semantic readiness, actual
Mu selection, physical identity codecs, nonempty inputs, and fresh pair remain
explicit. The recursive proof must derive the child's physical trace/effects
and contextual NodeLaw and then preserve Contextual across actual finishes.
The general physical completion theorem derives physical returns separately;
this component does not claim complete root language correctness.

Independent read-only review found no defect in the semantic argument, state
retention, or fuel accounting. The review records the earlier proof shape;
subsequent edits supply explicit intermediate states and compiler branch rewriting.
No Haskell source, old proof source, or runtime contract is changed.
