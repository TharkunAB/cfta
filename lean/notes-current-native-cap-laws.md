# Current library proof status and native cap laws

Checked on 2026-10-17 at proof commit e3b4c09d.
This checkpoint starts at published 6428bd23.
The proof commits are d60a4fbd, 70401f89, and e3b4c09d.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. For each public
operation P, the schematic target is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a target family. No complete whole-library implementation theorem
exists yet. Support must describe initial inputs and explicit resources.
It must not assume future successful execution or the desired result.
Documented errors and validation order are observable results.

The contracts include exact distinct accepted terms per node-count size,
counts, enumeration order, both rank/unrank inverses, transformation language
relations, generation coverage, and sampling laws. Distinct terms, accepting
runs, and generated members remain separate. Exact transformations require
language equality. Over-approximations require inclusion. Representative
selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, counts, retained explicit row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys supply a finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including Mu and unions. Actual histories derive physical, semantic, and causal Mu facts. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | Finite exact closed cold intersection from initial resource conditions. The same return supplies causal stores and hereditary laws. Supplied warm traces retain hereditary laws. | General mixed finite-cap closure and finite warm execution from initial inputs. |
| Ordinary constrained reduction | Initial profiles and constructor headroom derive a raw-Reach resource Plan. A complete modeled pass retains guarded language and stores. | The ordinary domain excludes Mu, references, and unions in every descendant. |
| Mixed outer tables | Plain whole nodes and descendant walks construct finite execution in certified tables that can contain other constrained owners. | General constrained node completion and initial production of filtered active/store certificates. |
| Rich editor and successive classes | Actual editor/class executions retain causal stores, original signed masks, caps, and complete physical/language receipts. | Current closed captured hereditary-leaf support is smaller than the source gate. General class existence remains open. |
| Required prefix | Arbitrary signed paths and closed initial local facts construct finite stable execution and rich returned laws. | Remaining initial callers and complete source-selected/public composition. |
| Native cap components | Actual source bindings, memo lifecycle, rows, unions, and checked edge code have finite-cap laws. A fresh normalized self-union binder constructs its own return and later replay. | General recurrent Mu occurrence invariant and joint production through the complete native trace. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct their own finite execution. Other theorems verify
supplied actual reads or give local code certificates. These are distinct
results. The new certificates do not establish general mixed-query completion.

## New native cap components

A cap bounds how many ordinary child steps can precede hereditary guards.
At depth zero it is exactly hereditary annotation. Positive depths permit
constrained ordinary rows. Mu records remain hereditary at every cap depth.

NativeLaws states conditional node and edge laws for every common operand
depth. NativeCache retains these laws through actual lookup, demand, and
finish operations. A finish installs the law at its exact evaluating owner.
Physical validity identifies the complete original request at a warm hit.
Empty native tables have these laws without a supplied completed result.
The memo lemmas do not derive arbitrary producer laws.

NativeScope derives actual entered Mu annotations from capped operands.
Later reads return the same annotated source Mu after legitimate growth.
No annotation condition applies to unrelated constructor-heap records.

NativeCode follows literal source continuations, sequencing, ordered walks,
and primitive construction. NativeCompile covers actual row and union code.
NativeEdge covers literal accepted-child code, sentinel construction, and
the actual checked body yield. Ordinary children use depth minus one.
Unions keep the depth. The concrete conjunction must preserve plainness
only at depth zero. Positive depths permit arbitrary root guards.
These are local certificates with conditional laws for recursive subcalls.
They do not construct a whole recursive execution or arbitrary Mu result.

NormalizedBinder handles a specific actual incoming union: the current pair
reference and one closed ordinary alternative. Actual stored substitution
and root filtering return that ordinary alternative before each probe and
before the final body. An initially absent canonical Mu key suffices for
finite construction. Both probes retain that absence until reservation.
The same actual result retains Facts, growth, issued history, availability,
and the original cap. Replay after the produced return uses the exact later
heap. This theorem does not cover arbitrary initially populated Mu keys.

Independent integration derives the old hereditary memo law at depth zero.
Another integration constructs a self-query from initial empty native tables.
It installs the derived cap law and constructs the next exact warm query.
The constrained-leaf instance has a guard that fails hereditary annotation.
It supplies no future trace, completed cell, or desired output-cap premise.
This is a bounded serial family, not arbitrary serial warm completion.

## Remaining work

1. Prove general mixed native cap closure. Classify actual pair occurrences
   through normalized Mu callbacks and smart cleanup. Produce all causal
   return laws jointly through the actual trace. Pair recurrence alone is
   permitted. The source-built recurrence examples remain constraints on
   the invariant, not counterexamples to cap closure.
2. Construct finite warm Target, Leaf, editor, and class execution from each
   full caller's initial supported inputs and resources. Supplied traces,
   code certificates, and future-prefix range interfaces do not prove this.
3. Prove constrained recursive descent. Produce filtered active-owner bounds
   and causal stores from initial callers and actual past prefixes. Keep
   the full source gate, which admits nonhereditary ordinary endpoints.
4. Prove repeated reduction convergence. Complete remaining recursive pruning
   and compilation callers. One exact pass does not establish a fixed point
   or bound intermediate structure.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and generator
   rank order. Complete concrete runtime, solver, IO, and randomness adapters.
   Keep capacity, primitive, and user-code assumptions explicit.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include serial
   warm calls and discharge each remaining adapter.

The current cap and whole captured closedness restrictions define an
intermediate supported family. Do not reduce the final source scope to it.
The complete library goal stays active. The proof count does not give a
meaningful completion percentage.

## Haskell handoff and validation

No Haskell change or new Haskell defect occurs in this checkpoint.
PR #65 already merges recursive field-pool repair b9219b9e in c0cc8a05.
Current derivation validation rejects the reported Chain pool with
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains opaque pool
evaluation. The repair rejects the invalid configuration. Root FINDINGS
keeps the external repair handoff first, including historical failures,
executable reproducers, affected files, commits, checks, and upstream status.

The pinned full Audit passes 2777 jobs and 62293 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All seven production
sources pass absolute-path strict checks without diagnostics. Exact imported
signatures, axiom checks, source hashes, and component manifests are recorded
in restart-evidence/20261017-native-cap-laws/checkpoint-validation.json.
The canonical build retains one older unused-input warning.

Preservation retains 10557 starting files, 2769 older non-Audit proof sources,
all 239 Haskell files, and 63 frozen production manifests with 534 entries.
Stashes and three other worktrees remain unchanged. Failed sources and raw
logs remain separate. Reuse unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence for c0cc8a05.
Preserve the optimized interned core and every older proof, counterexample,
repair, and marked draft.
