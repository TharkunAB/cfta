# Physical row selection after smart Mu finish

Date: 2026-10-18 08:44 CEST.

## Exact result

SourceCurrentNativeOrdinaryMuFinish.lean has SHA256
`d5429844173c98edf1b1087d6fcf00e0cffc07375b067e5182b15e6bd6418076`.
It adds one public theorem, selected. Symbol and Guard are arbitrary types.
No decidable equality instance is a theorem premise.

Inputs are an exact Mu entry, stored body, Depth and ordinary probes,
InternedFreshOrdinaryDepthHeap.Correct for those same fields, the literal
finish true result equation and an indexed physical nodeEdges row of that
result. The conclusion gives usesLocal=false, exact result=storedBody,
absence of the interned self name from storedBody.free and the same row
at the same physical index in storedBody. Full guards and ordered children
remain in the exact EdgeValue. Nested binders have no syntax restriction.

## Proof and necessary invariant

The proof follows cleanup. If cleanup retains the Mu, nodeEdges is empty.
If it removes a bare self-cycle, the result is Empty and nodeEdges is again
empty. A selected physical row therefore forces the first cleanup branch,
which returns the self-free stored body.

Correct false equates storedBody.depth with the stored Depth probe's depth.
Correct true equates the actual smart result depth with decodedDepth.
The selected body branch has the former depth. A true usesLocal would add
one to that same depth. The two actual depth equations therefore force
usesLocal=false. This uses no binder comparison or output-origin law.

The implication without Correct is false for arbitrary unrelated fields.
cleanup reads only the stored body and its interned self name. usesLocal
reads the separate ordinary probe's deep names. One can select a self-free
ordinary leaf body while choosing an unrelated ordinary probe that contains
the local marker below a node. finish returns the leaf body, but usesLocal
is true. This is a raw-value model boundary. It does not describe a
source-built causal cache, and it is not a Haskell defect.

An actual stored-record consumer must derive Correct. SemanticHeap includes
the required DepthHeap.Heap. Its exact present Mu record yields Correct for
these fields. The actual repaired construction preserves that heap. The
separate readback producer can therefore discharge this premise from the
actual returned construction. This helper assumes no History and does not
infer a new history between optional-binder states.

## Validation

ordinary-finish-direct-3 checks the immutable final source with all linters.
Its raw log has zero bytes. ordinary-finish-canonical-1 completes the single
canonical target. ordinary-finish-public-1 prints the full declaration,
proof and axiom list with all eight required settings. The verifier rejects
diagnostics, omissions, sorry and printer failures. Only propext,
Classical.choice and Quot.sound are allowed.

Each selected run uses a five-minute cap. Effective memory.max and
memory.high are 4294967296. Effective memory.swap.max is zero. The owned
runner, worker, limit readbacks and unique peak log are retained. No queue
setting changed. This component has one public pair and no constructed
pair. It does not pin or count any root-owned mutable fixture.

Attempt one used a Boolean lemma name absent from Lean. Attempt two checked
the proof but emitted one unused-simp-argument warning. Attempt three
removed that argument and has a genuinely empty log. All previous immutable
sources, logs, metadata and limit readbacks remain unchanged.

## Boundary

This is a local cleanup and probe-depth result. It does not establish the
stored probe invariant for arbitrary values, a stored body/ordinary
reconstruction equality, initial-source row descent, native or outer
completion, or termination. No Haskell source or runtime correspondence
result changes here.
