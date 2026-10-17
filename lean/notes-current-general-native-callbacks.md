# Current library proof status and general native callbacks

Checked on 2026-10-17 at proof commit e5dd8505.
This checkpoint starts at published 91ea29d3.
The proof commits are 443106e4, 5912ff25, and e5dd8505.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of target theorems. The complete implementation theorem
does not exist yet. Support must describe initial inputs and explicit
resources. It must not assume future successful execution or the desired
result. Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, counts, original explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual histories derive physical, semantic, and causal Mu facts. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | Finite exact closed cold intersection from initial resource conditions. Supplied warm traces retain causal stores and hereditary laws. | General mixed finite-cap closure and finite warm execution from initial inputs. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables with other constrained owners. | General constrained node completion and initial production of active and stored certificates. |
| Rich editor and successive classes | Actual editor/class executions retain causal stores, original signed masks, caps, and physical/language receipts. Required execution constructs its own finite return. | Current closed captured hereditary-leaf support is smaller than the source gate. General class existence remains open. |
| General native callbacks | Arbitrary stored substitution retains cap depth and marked free/deep bounds. Complete initial caches produce finite callbacks. Pending-cache certificates retain actual return laws and physical effects. Warm Mu hits derive occurrence bounds from exact probes. | Guard-cap readback for earlier outer Mu winners, causal native result-cell classification, and joint recursive production. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct finite execution. Other theorems verify supplied
actual reads or prove local continuation laws. These results have different
premises. The new local laws do not establish general recursive completion.

## New general callback components

Construction defines Typed over literal syntax and the actual lexical
values. Ordinary children consume one finite cap depth. Unions keep the
depth. Binder subplans use depth zero. Unused constrained captures remain
permitted. Actual execution retains the conditional Mu store and checks
all actual returned values. The certificate does not assume completion.

StoredSubstitution derives this selective syntax certificate from the
original available body's cap and hereditary replacements. It covers all
ordinary, union, reference, and nested Mu cases. A source Mu has a hereditary
body because its original cap permits Mu only through annotation. Actual
open Mu reconstruction can change identity and cached depth. The theorem
retains the same finite cap. Its complete endpoint constructs its own
actual return from initial Ready and retains full Ready at that return.

MarkerTransport handles the same general stored executor. Initial free/deep
bounds, the old pair's weight, and a fresh available marker derive the
returned bounds under the explicit marker weight. The proof does not assume
that reconstruction leaves old-absent records unchanged. Existing semantic
readback covers nested smart cleanup and earlier Mu winners. The result
also applies to the actual normalized native callback.

WarmOccurrences derives an earlier Mu winner's free and deep bounds from
its exact current probes. Their marked classification excludes a deep
local at a positive bound. The current repaired semantic heap then rules
out a retained wrapper. A populated request constructs its actual return
at the same heap without calling its arbitrary body continuation. This
proves occurrence readback. It does not prove a cap for the chosen old body.

NativeCallbacks combines the cap and marker producers. From initial Ready,
body laws, a fresh marker, and the causal Mu store, it constructs the exact
finite callback and retains its cap, marked classification, store, readiness,
availability, and both physical histories. Literal smart candidate cleanup
removes a positive maximal local and yields an unmarked classified value.
Independent integration constructs two successive general callbacks from
the original inputs and each actual preceding cache.

CallbackCertificates covers the actual unfinished outer reservation.
Its local checked theorem needs semantic heaps and available inputs, with
no complete-cache coverage or successful-callback premise. Each actual
return has its cap, marked classification, and local normal form. The actual
stopping cache retains semantic and causal stores. A returned body receipt
retains any supplied Covered pending permission list and both histories.
The derived cleanup law applies to the concrete candidate.

These interfaces have different scopes. Ready contains Covered [] and
therefore describes complete initial caches. A freshly reserved outer key
normally has Covered [key]. The local certificate applies there, but its
conditional result law alone does not construct that callback execution.
Neither candidate cleanup nor occurrence readback proves guard-cap
preservation for an earlier keep-first outer Mu winner.

## Remaining work

1. Prove general guard-cap readback for earlier outer Mu winners from
   actual causal construction and marked probe laws. The chosen old body's
   cap must be a conclusion. Install ranked occurrence laws in actual native
   memo cells at their captured owners. Produce cap and occurrence laws
   jointly through the native trace. General stored substitution and callback
   marker transport are now proved. Do not repeat the direct-union family.
2. Construct finite warm Target, Leaf, editor, and class execution from each
   full caller's initial supported inputs and resources. Supplied traces
   and local continuation laws do not prove this existence result.
3. Prove general constrained recursive descent. Produce active-owner bounds
   and causal stores from initial callers and actual past prefixes. Retain
   the full source gate, which permits nonhereditary ordinary endpoints.
4. Prove repeated reduction convergence. Complete remaining recursive
   pruning and compilation callers. One pass does not prove a fixed point
   or bound intermediate structure.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete runtime, solver, IO, and randomness adapters. Keep
   capacity, primitive, and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include serial
   warm calls and discharge each remaining adapter.

The current cap and captured closedness restrictions define an intermediate
supported family. The final theorem must cover the full source contract.
The complete library goal stays active. A proof count does not give a
meaningful completion percentage.

## Haskell handoff and validation

No Haskell change or new Haskell defect occurs in this checkpoint.
PR #65 already merges recursive field-pool repair b9219b9e in c0cc8a05.
Current derivation validation rejects the reported Chain pool with
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pool
evaluation. The repair rejects the invalid configuration. Root FINDINGS
keeps the external repair handoff first, with executable reproducers,
affected files, commits, checks, upstream status, and historical failures.

The pinned full Audit passes 2791 jobs and 62515 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All six production
sources pass absolute-path strict checks without diagnostics. Exact imported
signatures, axiom checks, hashes, and component manifests are recorded in
restart-evidence/20261017-general-marker-transport/checkpoint-validation.json.
All 61 imported axiom/signature pairs pass in 16 groups. Seven manifests
verify 155 entries. Integration includes an actual unfinished outer key.
The canonical replay retains one older unused-input warning.

Preservation retains 10871 starting files, 2784 older non-Audit proof sources,
all 239 Haskell files, and 65 frozen production manifests with 548 entries.
Stashes and three other worktrees remain unchanged. Failed sources and raw
logs remain preserved. Reuse unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence for c0cc8a05.
Preserve the optimized interned core and every earlier proof, counterexample,
repair, and marked draft.
