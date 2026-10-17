# Current library proof and initial numeric Required completion

This checkpoint starts at published 415b2c9c. Proof commits are cb79c288
and 8c0d36b4. Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of public contracts. First specify the intended behavior.
Then prove correspondence with the current Haskell implementation. Initial
support and resources cannot assume a later successful call or its result.
Documented errors and validation order form part of each contract.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not establish a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and both rank/unrank inverse laws. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, nested Mu and unions, physical stores, and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed collection and supported open WarmHead exposure with exact heaps, literal widths, and stable replay. | Arbitrary open recursion and remaining callers. |
| Comparison, selection, and Merge | Initial counters and causal mass construct modeled workers with full histories, heap effects, memo state, and sufficient fuel. | Remaining callers, separate language-law hypotheses, and runtime correspondence. |
| Recursive intersection | Supported closed operands construct stable semantic execution from initial fuel. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with language, stores, origins, globals, and resources. | Adaptive caller control flow and concrete capacity. |
| Operand, Target, Force, and Leaf | Initial selected paths, domains, caps, Frames, and reservations construct complete shared-state returns. | Outer caller composition and runtime correspondence. |
| Mixed edits and class passes | Initial finite tries and selected domains construct edits, a complete tail-first class pass, and its full caller Post. | Earlier source gates, Scan, outer recursion, and runtime correspondence. |
| Selected Required | Original false primary certificates construct the full return at a forecast and both fuel bounds computed from the initial trie, literal forest count, and profile. | Initial production of the primary certificates, earlier Scan, and outer recursion. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver results remain preserved. These Lean
definitions are handwritten. They do not yet establish full correspondence
with compiled Haskell. Read lean/notes-current-caller-required.md for the
preceding detailed component map.

## Complete initial Required resources

SourceCurrentConstrainedCapRequiredInitialNumeric.complete and caller
construct their own Required call. Inputs are the original query Frame,
Fits, available values, proper selected paths, false primary class
certificates, finite caps on all roots, and valid memos. The caller also
takes its original Context at the same inventory as the Frame.

The worker bound is 2 * sizeOf the original compiled Needed trie + 1.
The complete forecast is scan (planProfile (sizeOf needed)) originalCount
initialProfile. The reader bound is RequiredResources.readFuel of that
forecast. The literal initial forest count is separate from heap scalar.
Duplicate roots are permitted. The noncomputable sizeOf bound is a logical
majorant. It is not an extracted Haskell API budget or host instruction
count.

The same return retains the complete Required receipt, actual global
reads, full query Frame, memo effect, output caps, and equal forest length.
The receipt gives exact required forest language and selected returned
path domains. The complete caller Post also retains both outer result
tables, the fourth memo, and Merge exactly. Fits uses the initial forecast,
not counters observed after execution. Both computed fuels give the exact
worker result. Independent increases of either fuel retain that return.

The initial endpoints do not accept a future graph, successful worker,
reached resource callback, desired output profile, cap, or domain law.
The generic at_requireAll verifier has an explicit completed-worker
premise. The initial producers discharge it through their own completion.

## Actual profile composition

RequiredResources bounds only the three constructor-heap components.
Node and edge widths follow from available resident causal payloads at
entry. Constructor transfer keeps the literal original width. The actual
Head uses WarmHead support and the preceding open-reader envelope. Required
leaves the native domain supply unchanged, so the checked-state adapter
retains full Fits.

RequiredNumericReplay records exact equations on the existing node, child,
and row graphs. The ordinary phase costs one less worker layer. All
equations use one final reader ceiling. This adds no recursive graph type.

RequiredScanResources follows original child offsets and source row order.
A selected child returns before the suffix starts. Unselected children
remain present. Rejected rows execute no child work or reconstruction.
Kept rows retain the complete raw guard and run the actual edge constructor.
Pure padding reserves rejected positions without executing extra work.
Each scan fixes its original count before its first step.

RequiredNumeric discharges the child callback by induction on an initial
level at least sizeOf needed. Each selected requirement is strictly smaller.
An ordinary phase fixes original row and child widths at its entry stage.
A recursive Head derives WarmHead from the original anchored NodeSupport.
Its exposed ordinary phase uses that same stage. It does not reserve a
second whole plan. The final node constructor completes the plan bound.

Whole-forest closedness is not added. Open unselected siblings remain
permitted. Empty selection returns an unresolved reference unchanged.
Arbitrary open Mu remains outside the explicit WarmHead support. All-root
caps remain stronger than the live source refusal gate.

## Missing composition

1. Construct initial primary and secondary gate resources, seeded query
   resources, and the complete Scan. ClassScanCompletion.Ranges and
   SeededRanges still supply reached resource laws. Then compose the full
   source gate, Required preparation, and numeric class caller in source
   order.
2. Complete active and stored outer descent, arbitrary constrained Mu,
   and convergence. ParentWorkerActual.ResidentRanges and
   PartialWorkerRanges still supply reached outer checks. Busy cells do
   not establish completed execution.
3. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank source adapters.
   Exact ranks require original sorted explicit rows. They cannot be
   inferred from language equality alone.
4. Prove Haskell lazy demand, memo publication, solver, runtime, IO,
   randomness, and concrete capacity correspondence. Finally compose all
   public construction, transformation, graph-conversion, query,
   generation, and sampling contracts.

Target inclusion remains one-way for nonempty proper paths. Merge
overapproximation, native exact intersection, class-satisfying preservation,
and exact Required filtering are separate language laws. Do not replace
their distinct contracts with a single language-equality claim.

## Validation and external Haskell handoff

The pinned Audit passes 2961 jobs and 65367 dependency checks. All five
final strict production logs are empty. All five canonical targets pass.
Nine groups contain 52 full signature and axiom pairs: 44 distinct public
declarations, two repeated public declarations, and six integrations.
Five component manifests retain 122 entries and 123 verified hash references.
The extra reference repeats the main node production hash in metadata.
Only propext, Classical.choice, and Quot.sound occur.

The integrations include a constructed open constrained caller with two
selected closed children and an unselected depth reference. It retains an
evaluating node cell, returned edge cell, warm fourth entry, and valid
equality descent. A second initial caller checks empty-selection identity.
Helper integrations check rejected rows, actual edge construction,
original offsets, selected children, and the exact Required language law.
Earlier supported recursive fixtures remain unchanged.

Preservation checks 15021 starting files, 2955 older non-Audit sources,
239 Haskell files, 206 active-package files, two stashes, three other
worktrees, and 93 frozen module manifests with 718 entries. Audit adds
five imports. Earlier proofs, counterexamples, repairs, marked drafts,
evidence, and the optimized interned core retain their bytes.

This checkpoint adds no Haskell patch or new behavior defect. FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged and validated in source c0cc8a05. The Chain reproducer returns
Left (FieldAtomOnDatatype "Next" 0). Standalone holds retains opaque-pool
evaluation. Reuse the unchanged strict Nix build, 798 examples plus golden,
Fourmolu, and Cabal-gild checks. Record every later Haskell repair in
FINDINGS with its failure, executable reproducer, affected paths, commit,
checks, and upstream status.

Read lean/restart-evidence/20261017-required-numeric/checkpoint-validation.json
for exact hashes, successful logs, complete signatures, axiom reports,
and component manifests. Every failed source and raw log remains distinct.
The complete library goal stays active.
