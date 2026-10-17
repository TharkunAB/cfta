# Current library proof status, guard profiles, and ranked native laws

Checked on 2026-10-17 at proof commit 88be2ba6.
This checkpoint starts at published 58262ba5.
The proof commits are 445f33d7, 26dd76ec, and 88be2ba6.
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
| General native callbacks | Arbitrary stored substitution retains cap depth and marked free/deep bounds. Complete initial caches produce finite callbacks. Pending-cache certificates retain actual return laws and physical effects. Warm Mu hits derive occurrence bounds from exact probes. | Causal guard-profile production for earlier outer Mu winners and joint recursive native production. Ranked cache lifecycle and local row/child/union certificates are now proved. |
| Other components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

Some theorems construct finite execution. Other theorems verify supplied
actual reads or prove local continuation laws. These results have different
premises. The new local laws do not establish general recursive completion.

## New guard and ranked components

GuardDepth computes the least finite guard-cap bound from actual payload
syntax. Empty and reference values have bound zero. Unions retain the
maximum member requirement. Ordinary rows inspect their literal guards
and child profiles. A nonhereditary Mu has no finite profile. Within is
equivalent to the existing Cap predicate. The observer does not assume a
cap witness. Constructor theorems retain the profile through actual work.
It does not yet prove reflection across arbitrary fresh source callbacks.

OriginalSupport derives original syntax from closed available inputs.
It retains input availability and source-name coverage. Literal domain
extension stores one available, annotated, covered, original Mu witness
for each name. Later source reads recover that same record after actual
heap and issued-map growth. Ordinary children and union members retain
source support. Original source names have zero numeric pair weight.

NativeOccurrenceCache retains the old conditional cap store and fixed-source
ranked laws for complete node and edge requests. The input boundary includes
original syntax, availability in the immutable source, and domain coverage.
Bindings retain those facts for their actual Mu witnesses. Cap alone does
not imply them. Node results use the exact original pair rank. Row results
bound every returned child's free names by the maximum actual zipped child
rank. Empty tables need no result law. Lookup and demand retain prior laws.
A finish installs already-derived local laws at its exact evaluating owner.

NativeOccurrenceCode and NativeOccurrenceCompile retain both local laws at
the same actual returned machine. Literal work derives cap and occurrence
bounds through actual constructor readback. Joined rows use strict child
budgets at positive parent ranks and explicit zero bounds at rank zero.
Child walks preserve the exact ordered zip. Both union directions retain
the original enclosing rank through normalized union work. These theorems
still take smaller recursive request laws in their continuation interfaces.
They do not prove arbitrary request execution or joint recursive induction.

NativeOccurrenceTrace uses the same actual smaller checked body receipt
for cap and occurrence laws. Protected-prefix facts identify the captured
owner. The actual node or row finish installs both laws there. The theorem
retains the returned store and complete receipt. It does not produce the
smaller receipt or the general recursive law as an initial input theorem.

The independent guard audit constructs raw Mu x.bad(x) through actual
source construction from empty. The result has no finite cap. Its guarded
budget language is empty for every guard interpretation, reference
environment, budget, and term. This disproves language-only cap reflection.
Its own probes also fail the needed cap. It does not refute the intended
exact-probe causal law, and it does not identify a Haskell defect.

## Remaining work

1. Produce a causal guard-profile cell invariant through the same actual
   source callbacks and first-writer publication. Use literal root/deep
   observations for empty-child deletion, root filtering, and smart cleanup.
   Derive an earlier stored body's cap from its exact probe laws. Current
   semantic origins do not retain every historical depth/profile fact.
   Then complete the joint recursive native cap and occurrence induction.
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

The pinned full Audit passes 2797 jobs and 62661 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All six production
sources pass absolute-path strict checks without diagnostics. Imported
signatures, axiom checks, hashes, component manifests, and failed attempts
are recorded in restart-evidence/20261017-mu-cap-readback/. All 96 imported
pairs pass in eight groups. Five component manifests verify 147 entries.
Canonical replay retains one older unused-input warning.

Preservation retains 11053 starting files, 2790 older non-Audit proof sources,
all 239 Haskell files, and 66 frozen production manifests with 554 entries.
Stashes and three other worktrees remain unchanged. Reuse unchanged strict
Nix all-component build, 798 examples plus golden, Fourmolu, and Cabal-gild
evidence for c0cc8a05. Preserve the optimized interned core and every earlier
proof, counterexample, repair, and marked draft.
