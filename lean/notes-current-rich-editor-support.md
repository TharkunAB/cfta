# Current library proof status and rich editor support

Checked on 2026-10-17 at proof commit ef663832.
This checkpoint starts at published be6a0dc1.
The proof commits are 92df4c9c, 6e65aeca, and ef663832.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Support must describe initial inputs and explicit resource limits.
It must not assume future successful execution or the desired result.
The specification includes documented errors and validation order.
No complete whole-library implementation theorem exists yet.

The observable contracts include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverses, transformation
language relations, generation coverage, and sampling laws. Distinct terms,
accepting runs, and generated members remain separate. Exact transformations
require language equality. Over-approximations require inclusion.
Representative selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, counts, retained row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys provide the finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual construction histories derive physical, semantic, and causal Mu facts. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | Finite exact closed intersection from initial resource conditions. The same cold contextual receipt derives causal stores and local hereditary laws. Actual warm traces retain hereditary laws. | General positive-cap closure, finite warm callers, explicit machine capacity, and complete constrained outer progress. |
| Finite ordinary constrained reduction | Input profiles and constructor headroom derive the raw-Reach resource Plan. The modeled complete pass retains the full guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Whole plain nodes and descendant walks construct finite execution in certified tables that can contain other constrained owners. Full Post, memos, checks, and semantic laws are retained. | General constrained node completion and initial production of filtered active/store certificates for each full caller. |
| Actual rich editor and classes | The whole editor derives its leaf laws from actual Target/Leaf receipts. Actual successive classes retain causal stores, all original masks, caps, and full physical/language receipts. | The initial closed captured hereditary-leaf family is smaller than the source gate. General class existence remains separate. |
| Required prefix | Arbitrary signed paths and initial closed local facts construct finite stable Required execution, actual global reads, checked readiness, and all rich returned laws. | Remaining initial callers and complete source-selected/public composition. |
| Other library components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

The earlier native range gap remains closed by RecursiveInitialRanges.
The same-return cold laws remain in HereditaryNativeCold.cold_complete.
Do not replace those initial-only completion results with supplied traces.
The new editor/class results verify supplied executions. They do not prove
general finite warm native or constrained class execution.

## New closed connection between actual leaf producers and editors

RichStoreEffects derives rich store retention through actual node, raw edge,
and recursive head work. The exact returned state retains universal native
source laws, causal Merge entries, and the original captured target-slot laws.
Head exposure also derives all-path and finite-cap retention.

RichEditSupport performs the actual NodeReads, ChildrenReads, and RowsReads
induction. It supplies the store returned by each earlier child or row to
the next literal leaf receipt. It derives each leaf annotation from the
captured original masks and current rich store. No LeafCertificate,
NodeLeaves, or future recursive callback law is a public premise.
The public node, children, rows, and list results retain the rich store,
the ordered all-path relation, and the same finite cap.

RichClassSupport applies these results to the literal compiled class.
Coherent nontrivial record paths derive placement and edit safety.
Only fresh local slots are empty. Native and Merge tables remain warm.
The old complete physical and language receipt is retained at the same result.

RichClassPassSupport follows the actual right fold. Each head captures the
literal tail result. The tail all-path relation derives the head masks from
the original initial forest. Different classes can overlap in either prefix
direction. Final source empty propagation retains the same all-path relation,
cap, closedness, and warm-store laws. The class schedule does not change.

RichRequiredSupport retains these laws through actual Required reads.
RichRequiredCompletion constructs its own finite stable prefix for arbitrary
signed paths and a closed captured forest. Initial checked readiness,
availability, closedness, causal native/Merge stores, caps, and global validity
derive the actual reads and returned checked readiness. The same result
retains exact length, closedness, availability, all masks, and its cap.

RichRequiredClassPass retains the full original Required/class language
receipt. It also derives all-path, cap, and causal-store laws from the original
pre-Required forest through the supplied actual whole pass. It consumes the
actual past Required receipt, reads, and prepared global validity. An
independent integration kernel derives that prepared validity from the
constructed Required prefix. This is verification of the later supplied pass.
It does not assume a desired leaf result or prove general class completion.

## Explicit domain and remaining proof work

These results require a cap on the visited values, hereditary endpoints for
retained class paths, and closed captured originals. Whole captured closedness
is stronger than selected-only closedness. The complete source gate also
admits nonhereditary ordinary endpoints and paths that avoid other recursive
regions. Do not replace the final source scope with this intermediate family.

1. Prove native intersection support for the general mixed positive-cap
   operands. Account for actual pair cutoff, source bindings, normalized
   optional-binder callbacks, smart cleanup, and causal warm mixed entries.
   A blanket no-recurrence claim is too strong. A cutoff recurrence alone
   does not refute cap closure or implementation correctness.
2. Derive finite warm Target, Leaf, editor, and class execution from each full
   caller's initial supported inputs and resources. Supplied actual reads and
   actual-prefix range interfaces are useful components, not that theorem.
3. Prove decreasing constrained recursive descent. Produce the filtered active
   owner bounds and causal certificates from initial callers and actual past
   prefixes. The finite plain Region result does not close this gap.
4. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compilation callers. One exact pass and language narrowing do not
   establish a fixed point or bound intermediate structure.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete concrete runtime, solver, IO, and randomness adapters.
   Keep capacity, primitive, and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include serial
   warm calls and discharge every remaining adapter.

Read next-general-native-cap.md and general-native-cap-boundary.md in the new
evidence directory before the next proof. The full-library goal stays active.

## Haskell handoff and validation

No Haskell change or new Haskell defect occurs in this checkpoint.
The recursive field-pool repair b9219b9e is already merged in PR #65.
The retained Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds still treats supplied pools as opaque. Root FINDINGS keeps
the external handoff first, with failures, reproducers, paths, commits,
checks, and upstream status. Historical repair bytes remain preserved.

The final pinned Audit passes 2770 jobs and 62228 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eight final
production sources pass absolute-path strict checks without diagnostics.
checkpoint-validation.json records the exact final imported probe totals,
source hashes, canonical logs, and frozen component manifests.

The earlier ForestSupport review input remains preserved. Final review and
imported checks use the revised helper without its unnecessary equality
instance. Historical manifest input resolution records the exact old source.
No frozen review or old proof file is overwritten.

Preservation retains 10360 starting files, 2761 older non-Audit proof sources,
and all 239 Haskell files. Sixty-two frozen production manifests retain
527 entries. Stashes and three other worktrees remain unchanged.
Reuse unchanged strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild evidence for source c0cc8a05.

Read restart-evidence/20261017-rich-editor-support/ for exact evidence.
Preserve the optimized interned core and every older proof, counterexample,
repair, and marked draft. Passing components do not establish whole-library
correspondence or a meaningful completion percentage.
