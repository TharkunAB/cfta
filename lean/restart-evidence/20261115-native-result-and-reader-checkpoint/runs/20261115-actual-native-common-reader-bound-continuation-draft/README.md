# Common reader with the actual outer continuation

Status: UNCOMPILED CANDIDATE. No new proof credit.

This variant retains the real producer continuation. It changes the new
unpublished leaf's suffix types to generic `{Output : Type}`. The entry
continuation has type `Domain -> Code Symbol Guard Output`. The common rest
control has type `Control Output`. The producer continuation has type
`Node -> Code Symbol Guard Output`.

The actual producer suffix now starts at

```
.code ((compileNode query).bind next)
```

It can therefore include the real finish/parent continuation after the body
returns. The actual entry suffix still begins at the literal original full
U/pattern entry. Both suffixes end at the SAME rest control and SAME complete
observed reader state. Their original supplied fuel counts stay unchanged.

The entire public PROOF BODY is BYTE-IDENTICAL to the raw producer draft.
Only its new header's control types and actual producer expression change.
The proof still derives extension from `checked_trace_extension`. The entry
receipt still derives full P availability at that same observed reader.
No raw future availability, future extension, model, compatibility, or callback
provider is added. `next` is the literal code continuation of the observed
producer suffix; it is not a property of future calls.

All original accepted-source, build, full stored U, exact literal entered
domain, closed pattern/identity/shape, strict height, current operand
availability, physical checks, and PAST source growth conditions stay exact.
The native control conclusions remain the same. The original stronger public
MixedReferenceControl header stays byte-identical. The earlier raw candidate
and original stronger module remain untouched.

This is a local TWO-suffix common-reader leaf. The global proof must still
show their place in the SAME original execution and source branch. It does
not prove whole Returned history, arbitrary supplied-fuel completion, or ONE
compatible finite accepted completion of the original emitted root and every
retained/historical removed obligation. Earlier outputs after a later stop
retain their original obligations. No Haskell defect or fix was established.

`PROBES.lean.txt` is import-free for appended private probes.
`STANDALONE-PROBE.lean` is a SEPARATE import file after the module builds.
Do not append its import. Root owns all compilation and publication.
No compiler, live source, Git, board, or `/tmp` operation was used.
