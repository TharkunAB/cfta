# Current library proof status, full class caller, and selected Required

This checkpoint starts at published b3651b49. Proof commits are fc6a3d4b
and 4a01d59c. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of contracts. Specify the intended behavior first. Then
prove that the current Haskell implementation has that behavior. Initial
support and resources must not assume a later successful call or result.
Documented errors and validation order are observable results.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not give a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and rank/unrank inverses. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, including nested Mu and unions, with physical stores and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed recursive collection and row exposure with exact heaps, literal row widths, and stable replay. | Remaining callers and public correspondence. |
| Comparison and selection | Initial counters and causal mass construct repaired worker success with exact histories, heaps, and stable replay. | Remaining callers and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Full allocated replay retains equality state, heap, memo, and winner. | Remaining callers and Haskell runtime correspondence. |
| Recursive intersection | Supported closed operands construct stable semantic execution at initial computable fuel. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with language, stores, origins, globals, and resources. | Adaptive caller control flow and concrete capacity. |
| Selected Operand | Initial forest, signed path, counters, and causal mass construct projection then Merge, with exact full worker return, receipts, Profile, and Frame. | Remaining caller composition and concrete capacity. |
| Interleaved Target | Initial profiles and reservations construct the actual head Operand, recursive tail, and query sequence with complete receipts, states, and common-fuel worker result. | All-root cap and selected-domain assumptions remain explicit. Runtime correspondence remains open. |
| Shared Force and Leaf | Initial class facts, valid slot laws, and numeric reservations construct miss or hit Force, then Leaf's checked query at its actual return. Both preserve full shared state, receipts, Frames, profiles, caps, inventories, and global memos. | Outer caller composition and runtime correspondence. |
| Mixed editor | Initial finite trie, selected Safe domains, caps, Frame, stores, and numeric reservation construct complete node, forest, and compiled signed edits. Exact worker results retain every shared state field. | Outer caller composition and source runtime correspondence. |
| Class pass and caller | Initial selected domains, caps, Frame, stores, and one tail-first forecast construct the pass and full caller Post. Both outer result tables and the fourth memo remain exact. | Earlier Scan and Required numeric forecasts, outer recursion, and Haskell runtime correspondence. |
| Selected Required | Initial false primary certificates construct its stable worker, actual global reads, full query Frame, finite output caps, and caller Post. Open unselected siblings remain permitted. | Initial numeric Required forecast and Fits; construction of earlier Scan certificates. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. The Lean
definitions are handwritten. These component proofs do not yet establish
complete correspondence with compiled Haskell.

## Initial numeric class pass in the full caller

ClassCallerNumeric.complete starts from the actual caller Context and a
query Frame at the same inventory. It also takes initial Fits, selected
path domains, finite input caps, semantic Merge laws, and the pure class
forecast reservation. The existing initial class-pass producer constructs
its own actual Pass graph and reads.

Those reads derive the retained probe heap. The same full receipt derives
the caller Post, including stored node and edge result laws, physical Merge
residency, language coverage, fourth-memo correctness, and global validity.
The Post and returned query Frame use the same computed next inventory.
The complete result retains final Fits, semantic Merge laws, output caps,
forest length, and exact common-six-fuel worker success. Existing stability
derives the same return at six independently enlarged fuels.

Both outer result tables and the fourth memo remain exactly equal to their
input values. The class pass does not run the outer publication or demand
protocol. It only advances the actual checked state and Merge memo. Existing
returned cells retain their full original requests and language laws.
No future class graph, successful worker, range callback, reached bound,
or result law is an input.

## Open successful row exposure and Required caps

The old cap verifier for Required assumes whole-forest closedness. The
actual selected Required producer permits unrelated open siblings. Applying
the old verifier at that point would add a stronger support premise.
The old theorem remains preserved as a restricted result.

OpenExposure.collect, nodeEdges, and head verify actual successful row
exposure without a closed-input premise. The cold collector follows its
actual worklist. An unresolved reference cannot be a successful collector
branch. Mu unfolding uses the stored decoded body, its physical context,
and causal annotation store. Those existing constructor laws need no
whole-value closedness. Canonicalized fallback retains only actual rows.
The helper proves caps and causal stores for the same successful return.
It does not assume or construct arbitrary future read completion.

SelectedRequired follows the actual node, child, and row graphs. Empty
requirements preserve their input without inspecting references. Ordinary
rows can contain open unselected children. Selected calls preserve their
own caps before the original suffix executes. Rejected rows disappear.
Kept rows retain their original raw guard and position-wise child caps.
Recursive Head uses OpenExposure and the existing causal guard proof.
The final requireAll adapter retains the guard heap, all output caps, and
exact forest length. Verification needs no global closedness or new
selected-support premise. Its actual graph remains an explicit input.

## Initial selected Required with full Frames and caller state

SelectedRequiredComplete.complete takes the initial false primary class
certificates at its actual entry heap, proper selected paths, availability,
full query Frame, finite root caps, and valid global memos. The existing
selected-domain producer constructs its own finite Required execution.
The same stable return supplies a successful literal requireAll call and
its actual global memo reads. SelectedRequired verifies these new reads.
It derives output caps and guard observations from the original input.

OperandFrame.advance uses the same physical extension and unchanged native
cell tables to retain every part of the full query Frame. Required changes
no equality operations. The global Effect retains semantic and cost laws,
valid memos, the unfolding history, and exact query tables on that same
returned heap. The old full Required receipt retains selected returned
path domains and exact required forest language.

The caller variant derives probes from its own newly constructed Required
success. It retains the full caller Post at the same inventory as the Frame.
Both outer result tables, fourth memo, and Merge table remain exact.
Their correctness laws follow through the actual heap growth.
No Required graph, successful future worker, reached bound, output cap,
or future domain law is an input to either completion endpoint.

These Required endpoints construct existential sufficient worker and read
bounds. They do not compute an initial numeric resource forecast or prove
Fits at a forecasted Required return. The initial numeric Required forecast
remains open. Do not use an observed output heap or successful graph as
that missing initial forecast.

## Constructed integration and source comparison

The concrete caller fixture has an open parent with a nonempty equality
guard. It is outside Cap 0. Paths [[0,0],[0,1]] select closed siblings.
A third recursion reference stays open and unselected. The fixture derives
its original query Frame, Profile Fits, and finite root caps.

The fixture publishes and demands a legitimate parent node request and
leaves its cell evaluating. It publishes and demands a resident edge
request, then records the same edge with its proved reflexive language law.
Both result tables are nonempty and phase-sound. A current conjunction
memo miss on the open parent returns false and warms the fourth table.
This is an actual current call. It adds no assumed warm entry.

The initial complete caller then constructs two classes from its own
cumulative reservation. The same return retains both actual class graphs,
the intermediate forest, checked state, Merge memo, global bundle, and
literal final propagation. Both outer tables and the fourth memo remain
exact. The concrete cells and original valid equality descent entry survive.
The returned-edge seed verifies the memo protocol and its identity law.
It does not claim to execute an outer body.

The generic caller integration derives exact warm hits for pre-existing
returned node and edge cells after its own initial pass. The generic
Required integration derives selected returned domains, exact required
forest language, and stable replay from its own initial completion.
Two selected-Required checks construct an ordinary constrained parent with
an open unselected sibling and an empty requirement on an open reference.
The latter returns the same heap and memos without a closedness premise.

Read caller-guard-inventory.md and caller-guard-headers.md in
lean/restart-evidence/20261017-initial-caller-required/ for pinned source
anchors, exact remaining callback ranges, and the distinction between
current source execution and the handwritten logical workers.
No Haskell patch or new behavior defect is added.

## Exact support and remaining work

Selected domains permit unrelated open ordinary roots and siblings. Finite
caps still bound every original root. This premise remains stronger than
the source refusal gate and can exclude an unrelated nonhereditary Mu.
The new open-read verification removes closedness; it does not remove the
initial cap or causal-store conditions.

Target retains one-way inclusion for nonempty proper selected paths. Merge
can overapproximate its input. Native checked queries retain their exact
intersection laws. Class and pass receipts retain narrowing and conditional
preservation for class-satisfying terms. Required retains exact filtering
by its compiled path requirements. These are different language contracts.

1. Construct an initial numeric profile and fuel forecast for selected
   Required. Preserve the same output Frame, caps, reads, and open support.
2. Construct initial primary and secondary gate resources, seeded queries,
   and the full current Scan. Replace reached Scan and SeededRanges.
3. Compose the full source gate, required preparation, and numeric class
   caller in their actual order. Retain every memo family and owner law.
4. Complete active and stored outer descent, arbitrary constrained Mu,
   and repeated reduction convergence.
5. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank adapters.
6. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
7. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling correctness.

ClassScanCompletion.Ranges still quantifies reached primary and secondary
returns. The secondary-false branch still requires SeededRanges and the
suffix after an actual false fourth decision. ParentWorkerActual.ResidentRanges
and PartialWorkerRanges still supply outer reached checks. Busy calls are
not complete calls. Extracting fuel from a supplied local graph does not
establish an initial active or stored termination certificate.

Size-based levels and fuels remain logical definitions. Equality-table
size and instruction counts, concrete bytes, solver work, wall time,
concurrency, Haskell lazy demand, and memo publication remain separate.
The complete library goal stays active.

## Haskell repair handoff

Root FINDINGS keeps the external repair registry first. Repair b9219b9e
is merged in source c0cc8a05. Derivation validation rejects a field pool
for the datatype itself. The retained Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds still treats pool
descendants as opaque. Reuse the unchanged strict Nix build, 798 examples
plus golden, Fourmolu, and Cabal-gild evidence. Record each later repair in
FINDINGS with its failure, executable reproducer, affected paths, commit,
checks, and upstream status. This checkpoint adds no Haskell change.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2952 jobs and 65208 dependency checks.
All four final production strict logs are empty. Every canonical target
passes. All 16 full signature and axiom pairs pass in eight groups.
They check 10 distinct public declarations, one repeated public declaration,
and five constructed integrations. Four component manifests retain
126 entries and 128 hash references. The two extra references repeat the
selected-Required production hashes in manifest metadata. Every reference
is verified. Read checkpoint-validation.json in
lean/restart-evidence/20261017-initial-caller-required/ for hashes and
exact successful logs.
Only propext, Classical.choice, and Quot.sound occur.

Preservation retains 14784 starting files, 2947 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, two stashes, and three
other worktrees. All 91 frozen module manifests retain 709 entries.
Older proofs, counterexamples, repairs, and marked drafts retain their bytes.
The prior editor evidence gap remains documented and unchanged. New checked
sources execute directly from unique immutable snapshots. A preflight
source-generation failure attempted a missing exposure snapshot; its raw
invocation log and explicit provenance remain separate from checked sources.
