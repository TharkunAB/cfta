# Hereditary laws through actual recursive execution

## Top-level objective

Prove the intended contracts of the complete cfta library. Then prove that
the current Haskell implementation satisfies those contracts. The theorem
family must derive finite execution from explicit initial support and resource
conditions. Each actual public result must have the specified language,
errors, order, cardinality, or rank behavior. Preserve the optimized interned
core. Keep exact graph queries at the explicit graph boundary in ADR0004.

This is a theorem family. A generic statement is:

`Valid input + supported initial resources -> finite actual execution + specified result`.

The specification must state the supported domain. A preservation theorem
for a supplied completed call does not establish that call's termination.
A language theorem does not establish the exact row order used for ranks.
Passing tests and theorem counts do not establish full Haskell correspondence.

## Current result

This checkpoint starts at published `883467c8`. Source main remains
`c0cc8a05`. The fresh remote readback confirms both starting heads.
The proof commits are `bc981cd2`, `cf5262d1`, and `e52570f5`.
Eleven additive proof modules close the two execution gaps from the previous
local hereditary endpoint checkpoint.

`Annotated P value` checks ordinary guards and children, union members,
and a stored Mu body. `MuStored P heap` relates each exact stored Mu body
to its exact depth and ordinary probes. Physical Facts alone do not imply
this relationship. Actual allowed construction produces it. Other constrained
records remain permitted. The literal plain predicate also requires the
source guard syntax test. Semantic guard truth alone is insufficient.

Actual bounded comparison and its ordered children, cover, and row helpers
now retain MuStored. Actual selection and current memo-aware Merge retain
that store at their exact returned heaps. The Merge theorem retains its
existing physical effects, conditional memo laws, and local annotations.
It does not add a closed-input assumption to all Merge calls.

Actual native primitive producers retain the store. The code certificate
records local queried operand annotations. The compiler supplies that
certificate for every node branch and actual checked edge body. Checked
edge bodies use current loaded fields and allocated conjunction readback.
Optional binding derives its new stored body law before its continuation.

Strong induction over an actual completed checked trace proves both the
local result annotation and the two causal stores. Strictly smaller body
traces supply each captured finish law. The proof retains the exact evaluating
owner at that finish. Physical word safety and canonical readback recover
the law for the original requested operands at a warm hit. Initial resource
admission supplies physical checks at each reached instruction.

`SourceCurrentHereditaryNativeCold.cold_complete` applies this induction to
the actual trace of the existing finite recursive cold-intersection theorem.
It retains the SAME contextual receipt, value, fuel, and checked after state.
It supplies the exact closed intersection language, physical availability,
idle and scoped caches, local annotation, MuStored, native returned-cell
laws, and the literal unconstrained gate. The caller supplies initial facts,
local operand annotations, the initial causal store, and initial capacity.
The caller supplies no completed query or future prefix checks.

## Existing proved areas and remaining boundaries

The existing explicit graph development proves finite accepted-term size
classes, counts, enumeration, and rank/unrank laws under its stated graph
conditions. Source Sized contracts require the actual original sorted rows
for exact order and ranks. Language equality alone does not supply them.

The interned development covers constructor protocols, substantial equality
semantics, native recursive intersection, Required and Merge preservation,
and the current finite ordinary constrained outer pass. The new native cold
result includes Mu, references, and explicit unions under its initial capacity
conditions. The coarse domain inventory can exceed a fixed machine word.
Output allocation and concrete runtime bounds remain separate obligations.

The next proof is positional constrained-cap closure through actual selected
recursive paths. Then derive active-owner descent from initial conditions.
Ordinary minimum height and fixed original path depth are invalid general
measures. Retained counterexamples show height and inherited depth growth.
Those examples do not establish a new Haskell defect or divergence.
A finite cap over plain recursive subtrees is an intermediate family.
Its proof must not replace the general recursive selected-path obligation.

General recursive selected termination, repeated-pass convergence, remaining
recursive pruning and compilation callers, and complete public pipelines
remain open. Warm public query sequences need certificate producers and
history composition. Current frontend errors and validation order need source
adapters. Concrete lazy Haskell evaluation, containers, interning, machine
limits, solver boundaries, random adapters, and external integrations also
need their stated correspondence. The whole-library goal remains active.

## Verification and Haskell handoff

The full pinned Lean 4.34.1 Audit passes 2734 jobs and 61966 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All eleven final proof
sources pass strict checks without diagnostics. Canonical replay retains one
older unused-variable warning. Earlier failed drafts and warning logs remain.
Imported public signatures, axiom checks, and substantive integration kernels
are recorded in restart-evidence/20261017-hereditary-execution/.

The kernels construct their own allowed recursive inputs and stores. They
cover actual comparison, actual cold Merge followed by exact warm replay,
an unrelated constrained cap, captured native owners, warm original requests,
and actual finite native queries followed by a later Head read. The raw self
syntax kernel supplies its own completed query; only initial numeric capacity
remains an input. Independent reviews find no material defect.

Preservation retains 9659 starting tracked files, 2722 older non-Audit proof
modules, all 239 Haskell files, 59 frozen production manifests with 491 entries,
stashes, and three other worktrees. Older constructor and equality work,
repairs, counterexamples, and marked drafts retain their bytes.

No Haskell change or new Haskell defect occurs. Root FINDINGS keeps the
external repair handoff first. Repair b9219b9e is already merged by PR65 at
c0cc8a05. The original Chain derivation returns FieldAtomOnDatatype.
Standalone holds retains its opaque-pool behavior. The repair rejects the
invalid derivation configuration. Reuse unchanged strict Nix validation:
798 examples plus golden, Fourmolu, and Cabal-gild. Record each later repair
in FINDINGS with its failure, reproducer, paths, commit, checks, and status.
