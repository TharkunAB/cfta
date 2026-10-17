# Current library proof status and native occurrence support

Checked on 2026-10-17 at proof commit 2d828a42.
This checkpoint starts at published 4e4f59e9.
The proof commits are c68841ef, 9787e349, and 2d828a42.
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
| Native occurrence components | Closed input scope yields entered source bindings. Strict ordinary child descent changes the actual numeric pair. Local constructors and a direct-union callback retain occurrence bounds. Exact completed bodies publish laws at their captured cache owner. | General stored substitution and callback transport, joint recursive production, and arbitrary populated-cache completion. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct finite execution. Other theorems verify supplied
actual reads or prove local continuation laws. These results have different
premises. The new local laws do not establish general recursive completion.

## New native occurrence components

A cap bounds how many ordinary child steps can precede hereditary guards.
At depth zero it is exactly hereditary annotation. Positive depths permit
constrained ordinary rows. Mu records remain hereditary at every cap depth.

NativeIdentity and NativeCoverage derive scoped reference coverage from
closed roots and an empty source domain. Literal domain entry retains
coverage for both exposed bodies and the annotated source Mu bindings.
Later exact reads retain these facts after legitimate heap growth.
The same actual numeric identity implies equality or hereditary operands.
No future result law is a premise of these scope results.

NonplainRank assigns zero to hereditary operands and structural size to
other operands. Pair rank is the sum. An ordinary child request decreases
this measure strictly when a parent is not hereditary. Source Mu bodies,
unions, and legitimate reads have the separate nonincrease laws they need.
NativePairRank connects the measure to the actual sorted numeric pair.
NativePairWeight derives the pair's weight from exact source-table reads.
Strict ordinary descent therefore excludes the ancestor's actual pair.
This does not assert that every recursive request has a smaller measure.

PairOccurrences separates free occurrences from occurrences below an
ordinary or Mu boundary. At a positive owner bound, the owner's maximal
weight cannot occur below such a boundary. Actual ordinary construction,
normalized union construction, and root filtering retain local bounds.
PairOccurrenceCallbacks replaces the old pair by the actual fresh marker
in a specific union of a pair reference and a closed ordinary record.
The marker receives the old pair's weight explicitly. The actual callback
and candidate cleanup return that original ordinary record at the same heap.
The integration derives a positive weight from actual source reads and uses
a constrained ordinary guard. It supplies no desired callback result law.
This is a restricted producer. General nested callback transport is open.

NativeTraceGlue retains source cap stores and the causal Mu store through
literal native execution prefixes. A completed smaller body receipt carries
its derived node or edge law for all source depths. A protected prefix
identifies the same captured evaluating owner. The actual finish installs
that law at this owner and retains the physical return and effects.
The local continuation can then use the produced law at that exact return.
The receipt is an induction interface. It does not derive every body's law.

## Remaining work

1. Prove general occurrence and cap transport through actual stored
   substitution and normalized Mu callbacks. Include existing Mu-cache
   winners. Produce the native return laws jointly through the actual trace.
   Existing semantic readiness supplies repaired free/deep occurrence
   observations. General marker observations and cap transport still need
   proofs. Another direct-union instance does not close this boundary.
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

The pinned full Audit passes 2785 jobs and 62415 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eight production
sources pass absolute-path strict checks without diagnostics. Exact imported
signatures, axiom checks, hashes, and component manifests are recorded in
restart-evidence/20261017-native-cap-producer/checkpoint-validation.json.
All 91 imported axiom/signature pairs pass in 11 groups. These include the
evidence-only warm-cell consequence. Four manifests verify 133 entries.
The canonical replay retains one older unused-input warning.

Preservation retains 10705 starting files, 2776 older non-Audit proof sources,
all 239 Haskell files, and 64 frozen production manifests with 542 entries.
Stashes and three other worktrees remain unchanged. Failed sources and raw
logs remain preserved. Reuse unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence for c0cc8a05.
Preserve the optimized interned core and every earlier proof, counterexample,
repair, and marked draft.
