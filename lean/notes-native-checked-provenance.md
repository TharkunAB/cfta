# Checked native receipts and actual heap preservation

The [running and field checkpoint](notes-native-field-running-invariants.md),
`b03d0d1f`, derives actual original running-cell survival and normalized-field
closure. Native input checks, semantic finish receipts, sidecar coverage, and
general contextual Mu correctness remain open. Its audit passes 1,975 jobs
and 50,686 dependency checks. Sized and Haskell sources remain unchanged.
Older next targets below are historical.

The [accepted child checkpoint](notes-native-accepted-child-demand.md),
`970ef848`, derives actual child traces and accepted edge receipts. General
node/Mu correctness and reached-child checks remain open. Its audit passes
1,965 jobs and 50,512 dependency checks. All Sized contracts and Haskell
sources remain unchanged. Older next targets below are historical.

Source: `TharkunAB/cfta`, main `1eb4ab05`, merged at `271284df`.
Initial receipt proof: `af1c9d19`. Heap and outer-memo proof: `59c41d3a`.
Actual rejection and stopped outer-call proof: `20982f98`.
This extends [checked native demand](notes-native-checked-demand.md).
Production Haskell and earlier proof definitions remain unchanged.

## Completed execution receipts

`SourceEqualityNativeDemandProvenance.NodeProduced` records an actual finite
execution of the compiled node body through the checked interpreter.
`EdgeProduced` records an actual finite execution of `edgeBody`. Both retain
the complete checked states, original available inputs, physical and domain
growth, and available or resident output. Both retain a separate independent
record-language law. Neither uses the eager kernel's Produced relation.

The language law applies to closed inputs in the exact empty domain. For
other domains or open inputs, the implication can be vacuous. The definitions
do not prove an open-context language law or the public PCS guard bridge.
The generic `holds` parameter is an arbitrary guard evaluator.

The execution witnesses are existential. They do not require initial native
semantic validity, operation validity, internal request bounds, or a causal
link between the witness history and the cell's publication history. They
are actual checked-body execution witnesses with an independent language
law. They are not complete global execution-history correspondence.

`Valid` retains physical machine validity and both typed cell families.
Suspended and evaluating cells retain their original available inputs.
Returned cells retain a checked execution receipt. Published keys retain
explicit source KeySafe bounds. This does not bound orphan allocated cells,
all internal requests, logical counters, or the whole lifetime of the cache.
The weaker structural Shape projection discards these semantic and range
facts. Shape alone is not a semantic substitute.

`SourceEqualityNativeDemandCellValidity` derives publication, demand, machine
growth, and completion laws for this invariant. Ready hits recover the exact
original request, actual checked receipt, available result, and independent
language law without effect replay. Key injectivity uses current physical
coherence and the explicit source word bounds. Generic completion requires
a separately proved receipt for the request at the actual running handle.
These laws do not prove preservation for every recursive source branch.

## Derived primitive and finite heap effects

`SourceEqualityNativeDemandHeapPrimitives` derives heap Keeps and available
results for ordinary node and union construction from current resident edges
or available operands. These lemmas need no closedness premise. An available
optional-binder body completes in a ready heap, including when the body is
open. Its actual result retains heap readiness and both physical histories.

`WorkInputs` classifies pure work and the emitted makeEdge, makeNode, and
makeUnion jobs. It checks their arguments in the current heap. It does not
classify arbitrary jobs by a supplied future result.

`SourceEqualityNativeDemandHeap.Inputs` checks only actual work arguments
and available optional-binder bodies. Other controls, including edgeBody,
need no heap input check. Memo publication, demand, completion, domain entry,
and original-field checks leave the constructor heap unchanged.

`step_keeps` derives complete heap preservation for every actual outcome.
`InputsThrough` records these current checks on the actual reached path.
`execute_keeps` derives the final ready heap and both histories by induction
on fuel. It has no future Ready, Keeps, Sound, or eager Produced premise.
Deriving the reached checks from general compiled calls remains open.

`SourceEqualityPartialNativeHeap.execute_sound` combines this derived heap
receipt with actual operation allocation receipts. Every finite observation
preserves current outer result-cell Sound. `execute_receipts` also retains
operation validity and growth, native Shape, earlier returned native cells,
published handles, and outer keys. Its current input and normalized-field
plans remain explicit. These are current input requirements, not future
heap or semantic conclusions.

## Actual stopped completion

`SourceEqualityNativeDemandMismatchReceipt` derives the actual standalone
three-instruction mismatch body and five-instruction native completion.
Primitive constructor facts derive the resident sentinel and heap Keeps.
Independent forest arity proves the exact empty intersection language for
every guard evaluator. No original field lookup, cached equality premise,
child callback, or eager result predicate is needed for this language law.
Actual publication and demand retain the real completion handle. The new
checked Valid invariant survives in both memo families. A fresh key absence
derives the complete receipt without a supplied demand observation.

`SourceEqualityNativeDemandRejectedReceipt` handles matching arities and
actual checked prefix rejection. The standalone body retains the actual
raw-conjunction and accessor effects before empty-field allocation and
sentinel construction. Independent PCS guard meaning proves empty common
language. Actual original field loads, current normalized source fields,
and current operation validity derive the receipt. Five native instructions
complete the original returned cell and preserve the new checked Valid
invariant. The completed operation state retains all reached allocations.
No child code exists in this branch. The eager effect sequence is not used.

`SourceEqualityPartialNativeStopped` connects actual stopped completion to
the surrounding recursive memo. It derives outer Frame and current Sound
from actual branch allocations and heap effects. It supplies no future
soundness, heap receipt, or reached-path plan for these stopped calls.

`SourceEqualityNativeDemandNodeShortcut` derives actual one-instruction node
body receipts for literal empty operands and the physical self branch.
Physical coherence and original operand availability derive literal self
record equality. The independent language proof uses that equality. The
generic four-instruction pure wrapper is conditional on actual publication,
demand, and the compiled pure body. It does not prove fresh-miss totality.

## Next target and full scope

Prove completed checked provenance through accepted recursive edge and node
bodies. Derive actual child availability and residency through continuations.
Derive InputsThrough from those original arguments. Derive FieldsThrough
from actual original constructor receipts and dynamic constraint closure.
Preserve matched-symbol facts from the actual row join. Matching arity alone
does not establish that two original edge symbols agree. Retain real handles,
source errors, incomplete observations, and explicit range checks.

Connect the checked interpreter to selected class folds, reconstruction,
both gate memo families, complete guarded passes, recursive reduction, and
original graph construction. Do not assume replayed physical effects or the
old eager Produced relation. General caller completion, open contexts,
repeated fixed points, getAllAtPath, global unrelated prehistory, pending
equality-operation thunks, cache/hash/IntMap adequacy, signed indexes, lifetime
capacity, unsafe IO, GHC execution, decision-model, named measures, parser
and decoder bridges, and extraction remain open. Whole-library scope is
incomplete. Exact Sized classes, finite execution, canonical sequence,
distinct size order, and both signed inverse implications remain separate.

## Validation

Use the pinned toolchain:

```sh
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build MicroCFTA.SourceEqualityPartialNativeStopped MicroCFTA.SourceEqualityNativeDemandNodeShortcut
/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake -d lean build
```

Focused endpoints pass 1,093 jobs. The full audit passes 1,955 jobs and
checks 50,413 theorem dependencies. Logs:
`/tmp/mcfta-native-provenance-focused-20261015.log` and
`/tmp/mcfta-native-provenance-complete-audit-20261015.log`.
The old unused-input warning remains. The ten new modules have no warnings.
The aggregate audit permits only propext, Classical.choice, and Quot.sound.
No Haskell file changed. Prior Nix, six-suite, format, metadata, and 205-rank
checks retain their previous source evidence and were not repeated.
