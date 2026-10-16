# Proof status at 2026-10-17

Checked at published proof checkpoint `e0c1929e`. Source main is `c0cc8a05`,
merged into `formalize` at `896b0a1c`. This note reports the current theorem
boundaries. It adds no theorem and no Haskell behavior change.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. The target is
a family of theorems, with this schematic form for each operation P:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

The support predicate must describe initial inputs and resource limits.
It must not assume successful completion. The specification must include
the documented errors and validation order where the API returns errors.
There is no completed single whole-library theorem.

The main observable contracts are:

- Exact listing returns all distinct accepted terms at a node-count size.
  It returns no duplicates. Counting gives the cardinality of that class.
- Rank and unrank follow the specified order and satisfy both inverse laws.
- Each transformation has its own language relation. Exact transformations
  preserve language. Over-approximations prove inclusion. Representative
  selection has a separate restriction contract.
- Generation covers the specified members. Sampling has the specified
  weights and probabilities. Members, accepting runs, and distinct accepted
  terms require separate statements.
- Current Haskell execution agrees with the specified algorithm and errors.
  This includes memo effects, machine bounds, and representation limits.

Exact queries use the explicit graph, including cyclic graphs. The optimized
interned core remains the construction and transformation path. Read
[ADR 0004](../docs/adr/0004-explicit-graph-boundary.md).

## Established results and their limits

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, finite class evaluation, counts, size-major enumeration, retained row order, and both distinct-term rank/unrank inverses. The finite carrier comes from validated raw graph keys. | Concrete host and solver adapters and complete public pipeline composition. See [Sized contracts](notes-sized-finite-keys.md). |
| Interned construction | Repaired closed syntax has a finite constructor execution. Syntax includes binders and unions. Actual construction and field histories derive physical and semantic entry facts. | Concrete lazy Haskell publication, interning, and runtime correspondence. The word Ordinary in older module names does not by itself exclude binders. |
| Recursive native intersection | Current checked cold execution returns the exact intersection language for closed Original resident operands. The same return has scoped caches, idle native state, and a closed output. Mu and union operands are included. | The public theorem still assumes WordRanges over reached checked prefixes. Initial resource conditions must derive these ranges for the general recursive family. |
| Finite ordinary constrained reduction | Initial profiles and constructor headroom derive the original universal raw Reach numeric Plan. The complete modeled outer pass has stable execution, exact full guarded-language preservation, retained stores, and constructor request bounds. | The domain excludes Mu, references, and explicit unions in every descendant. The theorem does not bound total Haskell runtime or memory. |
| Other library components | Checked language, equality, enumeration, arithmetic, union-find, memo, ranking, generation, and sampling results exist. Some source drivers and restricted adapters are complete. | Their remaining adapters and recursive callers do not yet form a complete current-library implementation theorem. See [API coverage](API-COVERAGE.md). |

The finite ordinary result is in
`SourceCurrentAllocatedFiniteOrdinaryOuterResourceEntryRoot.finite`,
`constructed_root`, and `prepared_root`. The caller no longer supplies the
reached numeric Plan. Read [the resource result](notes-current-raw-reach-capacity.md).

The recursive native result is
`SourceCurrentAllocatedNativeColdClosedExact.cold_complete`.
`SourceRecursiveIntersectionRequestProgress.initial_complete` already derives
semantic completion for closed Original inputs. The current native theorem
does not require the caller to supply semantic Completes.
`SourceCurrentAllocatedNativeConstructedHistory.query_complete` also derives
entry facts from actual generic construction and a covered field history.
It retains the actual build and WordRanges premises.

WordRanges is defined in `SourceCurrentAllocatedNativeRequestBounds`.
It requires machine-key safety at every reached checked node and edge
instruction. It assumes no completed result, but still quantifies over
execution prefixes. Deriving it from initial syntax, histories, and headroom
is a remaining proof obligation. Do not report general recursive native
semantic completion as wholly absent.

## Remaining work

1. Derive general recursive native machine ranges from initial resources.
   Account for domain identities, Mu entry, references, unions, original
   operands, constructor requests, and actual memo schedules.
2. Extend the constrained reduction progress argument to recursive selected
   paths. The outer worker stops at Mu and union roots. Selected path lookup,
   required paths, edits, and target intersection can still enter them.
   Preserve the actual refusal policy and inherited equality payloads.
   Ordinary height does not supply a general decreasing measure here.
3. Prove convergence for repeated reduction passes and complete the remaining
   recursive pruning and compilation callers. One exact completed pass does
   not establish a fixed point. Semantic narrowing alone does not bound
   intermediate structural growth.
4. Complete current frontend correspondence. This includes typing and
   refinement derivation, drawn fields, symbolic measures, new errors,
   validation order, and generator-specific order.
5. Complete concrete runtime and external adapters. These include maps and
   arrays, signed indexes and counters, lazy memo publication and forcing,
   process-global state, interning, codecs, solver answers, IO, and random
   draws. Keep explicit primitive and user-code assumptions visible.
6. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Abstract
   composition does not discharge a missing implementation adapter.

The older PlainRegion theorem permits opaque Mu and union leaves. It requires
empty physical equality payloads on traversed ordinary edges. It does not
prove general recursive selected narrowing.

## Haskell repairs and evidence

The recursive field-pool defect is repaired by `b9219b9e`, merged in PR 65.
The current derivation rejects a pool for a field of the datatype itself.
The retained Chain example returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds still treats supplied pools as opaque. The repair rejects
the invalid derivation input; it does not change that standalone evaluator.
Root [FINDINGS](../FINDINGS.md) keeps the repair handoff first. It records
the failure, reproducer, affected paths, commit, validation, and merge status.
It also records the earlier negative-bound and named-measure repairs.
The historical failure reports retain their original bytes and source dates.

The last completed full pinned Audit passes 2693 jobs and 61393 dependency
checks. Only propext, Classical.choice, and Quot.sound occur. The unchanged
Haskell source has a strict Nix all-component build, 798 examples plus golden,
Fourmolu, and Cabal-gild validation. These checks are component evidence.
They do not provide a meaningful percentage of whole-library completion.
This status audit reuses that evidence after source hash checks. It does not
claim a new full build or a new mathematical result.

The current audit evidence is in
`restart-evidence/20261017-recursive-source-progress/`. Imported public
signature and axiom checks inspect the recursive completion premises.
Four focused Nix source checks exercise selected recursive endpoints,
unequal-depth paths, a failed ordinary min-height bound, and inherited
path-depth growth. Their finite observations do not prove general progress.
No new Haskell defect was established. Earlier failed probe expectations
and raw logs remain in that directory.
