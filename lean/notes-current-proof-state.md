# Current proof state

Updated: 2026-10-16. Source main is `c0cc8a05`. The proof branch is `formalize`.
The preceding published checkpoint is `b3801702`. Proof commits are
`f1c23cf2`, `a125732a`, and `be7b86da`.

## Top-level target

Prove the complete library design, then establish correspondence to the public
Haskell algorithms. There is no completed single whole-library theorem.
The intended theorem has this schematic form for each public operation P:

`Valid(input) ∧ Supported(input) ⇒ Terminates(P, input) ∧ Contract(P, input, output)`.

`Supported` must name the input domain. It must not assume that the operation
has completed. Each operation has its own contract:

- Exact listing at node-count size n returns all distinct accepted terms of
  size n, with no duplicates. Counting returns that set's cardinality.
- Rank and unrank follow the specified order and satisfy both inverse laws.
- Each transformation satisfies its stated language relation. Exact
  transformations preserve the language. Over-approximations provide inclusion.
  Representative selection has its separate restriction contract.
- Generator operations cover their specified members. Sampling follows the
  stated weights and probabilities. Generator members, accepting runs, and
  distinct accepted terms have separate contracts.
- The actual implementation agrees with these algorithms, including errors,
  validation order, memo effects, identity bounds, and representation limits.

Exact queries use the explicit FTA graph. The optimized interned core remains
the construction and transformation path. ADR 0004 defines that boundary.

## What is proved

The model has checked language, equality normalization, lattice counting,
union-find, memo, weighted sampling, and ranking components. The Sized model
has exact accepted size classes, finite class evaluation, counts, size-major
enumeration, and both distinct-term rank/unrank inverse laws. Exact ranks
depend on the retained explicit row order. Concrete host correspondence is
still a separate obligation.

The current reduction work follows literal source execution and its returned
state. Native intersection, Merge, Target, shared Force/Leaf, edits, class
passes, local reduction, and parent calls have finite-ordinary component
results. Their resource theorems derive constructor request bounds from
initial profiles and cumulative headroom at those component boundaries.
They do not give a total Haskell runtime or memory bound.

The outer root theorem constructs its own finite-ordinary constrained pass.
It proves stable literal execution and exact full-language preservation,
conditional on the numeric Plan at all reached parent entries.
The new OuterProfileRoot retains native output and Merge certificates at
that same constructed return. It keeps the Plan premise explicit.

The new six-module checkpoint closes certificate retention through actual
Edit, Class/Pass, Stage/Local/Parent, and all eight outer families. Each
public outer endpoint derives its own reached Checks from its actual reads.
These supplied-read retention results do not assert graph existence.
The root supplies existence through the earlier conditional root theorem.

The guard component derives raw and effective conjunction bounds from
initial stored path occurrences, stored path depth, raw guard stages, and
exposed Same path depth. It follows actual staged normalization. It constructs
the literal allocated conjunction and its returned bounds. This local result
does not yet supply a hereditary native or outer guard invariant.

## What is missing

1. **An initial-only outer resource theorem.** Derive guard bounds at every
   nested result through native conjunction, Merge winners, Required, edits,
   and class passes. Produce quantitative row and arity certificates for warm
   outer returns. Derive the traversal recurrence in actual source order.
   Account for every reached prefix and raw rebuild. Use initial headroom
   to derive ParentCapacity and the root Plan before each parent executes.
   Retaining existing lower certificates does not discharge these producers.
2. **General recursive progress.** Extend the supported termination domain
   beyond finite ordinary inputs to Mu, references, unions, and constrained
   recursive selected narrowing. Keep preserved constructor counterexamples
   and repaired protocol obligations explicit.
3. **Repeated-pass convergence and other recursive callers.** A correct
   completed pass does not prove that repeated passes reach a fixed point.
   Semantic narrowing alone does not bound intermediate structural growth.
   Recursive pruning and remaining compilation callbacks need their own
   completion arguments. Some finite fragments already have convergence
   theorems; those results do not establish the general case.
4. **Current frontend correspondence.** Connect current typing and refinement
   derivation interfaces, drawn fields, errors, validation order, symbolic
   measures, and generator-specific order to their models. Preserve separate
   contracts for distinct terms, accepting runs, and generator members.
5. **Concrete Haskell and external boundaries.** Connect pure models to host
   maps and arrays, signed machine indexes and counters, lazy memo publication
   and forcing, interning identities, IO, codecs, external solvers, and random
   draws. Keep logical cold initialization separate from process-global state.
6. **Complete public pipeline composition.** Connect the current source
   adapters and execution theorems through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Abstract pipeline
   composition already exists. Unproved runtime adapters prevent a complete
   implementation verification claim.

## Evidence and Haskell handoff

The pinned full Audit passes 2630 jobs and checks dependencies of 60745
theorems. It permits only propext, Classical.choice, and Quot.sound.
The count measures checked proof dependencies. It does not measure the
fraction of the library that has complete implementation correspondence.
All 38 public axiom/full-signature pairs and 15 integration pairs pass.
The verifier checks 138 entries in seven component manifests. Preservation
checks retain 8020 starting files, 2623 older non-Audit proof files, all
234 Haskell files, 50 frozen production manifests with 387 module entries,
stashes, and the three other worktrees. Only the seven restart authorities
and the six additive Audit imports change older tracked files.
Current evidence is in
`lean/restart-evidence/20261016-constrained-outer-profiles/`.

The recursive field-pool issue is repaired by `b9219b9e`, merged in PR #65.
For `data Chain = End Bool | Next Chain`, the invalid recursive child pool
now returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` still
treats supplied subtrees as opaque. The derivation rejects that configuration.
Root FINDINGS records the reproducer, affected files, commit, tests, and
upstream status before the historical failure reports. No new Haskell patch
is part of this proof checkpoint. The unchanged source has strict Nix build
validation, 798 passing examples plus golden, Fourmolu, and Cabal-gild checks.
