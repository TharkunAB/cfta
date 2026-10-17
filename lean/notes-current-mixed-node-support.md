# Current library proof status and mixed-node support

Checked on 2026-10-17 at proof commit 6cb08c47.
This checkpoint starts at published 6458c610.
The proof commits are 5ba18097, a2626e12, 741a40dd, and 6cb08c47.
Source main remains c0cc8a05, merged locally at 896b0a1c.

## Top-level target

Prove the intended contracts of the complete library. Then prove that the
current public Haskell operations implement those contracts. This is a
family of theorems. For each public operation P, its schematic form is:

`Valid(input) ∧ Supported_P(input) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

Support must describe initial inputs and explicit resource limits.
It must not assume successful completion or the desired future result.
The specification includes documented errors and validation order.
No complete whole-library implementation theorem exists yet.

The observable contracts include exact distinct accepted terms at each
node-count size, counts, enumeration order, both rank/unrank inverses,
transformation language relations, generation coverage, and sampling laws.
Distinct terms, accepting runs, and generated members remain separate.
Exact transformations require language equality. Over-approximations require
inclusion. Representative selection has its own restriction contract.

## Current proof map

| Area | Established result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact accepted size classes, counts, retained row order, size-major enumeration, and both rank/unrank inverses. Validated graph keys provide the finite carrier. | Concrete host and solver adapters and complete public composition. |
| Interned construction | Finite modeled repaired closed construction, including binders and unions. Actual construction histories derive physical, semantic, and causal Mu facts. | Concrete lazy publication, interning, and runtime correspondence. |
| Recursive native intersection | Finite exact closed intersection from initial resource conditions. The same cold contextual receipt derives causal stores and local hereditary laws. Mu, references, and unions are included. | Explicit machine capacity and general constrained outer callers. |
| Finite ordinary constrained reduction | Input profiles and constructor headroom derive the raw-Reach resource Plan. The modeled complete pass retains the full guarded language and stores. | This domain excludes Mu, references, and unions in every descendant. Total host memory and runtime are not bounded. |
| Mixed outer tables | Whole plain nodes and descendant walks construct their own finite execution in certified tables that can contain other constrained owners. Full Post, actual memos, checks, and semantic laws are retained. | General constrained node completion and production of the initial filtered active/store certificates by each full caller. |
| Actual Target and edits | Actual warm native queries retain hereditary laws. Captured Target, Force, and Leaf reads derive local laws. Conditional edits retain every original path and cap. | Richer stores through the whole editor and successive classes; general nonhereditary ordinary endpoints. |
| Other library components | Language, equality, arithmetic, union-find, memo, ranking, generation, sampling, and restricted source-driver proofs remain preserved. | Remaining current adapters and complete public pipelines. |

The earlier native range gap is closed by
SourceCurrentAllocatedRecursiveInitialRanges.initial_ranges and cold_complete.
The same-return local laws are in SourceCurrentHereditaryNativeCold.cold_complete.
Their callers do not supply future prefix checks or a completed cold query.
The present actual warm-query results verify supplied execution. They do not
establish arbitrary future warm-query existence.

## New mixed-node completion

ConditionalParentShape derives the returned ordinary parent shape from the
actual completed body. ConditionalStoreTrace retains conditional owner laws
through all eight actual outer families. These two results consume actual
completed graphs. They impose no plain Region restriction on those graphs.

ConditionalPlainSupport, Children, Rows, and Node discharge the whole plain
node recursion by strict node-rank induction. The active bound filters plain
owners. Other constrained owners need no such bound. The public finite node
and descendant theorems construct their own stable worker run and graph.
The same return retains strict reads, checks, full Post, availability,
conditional stores, and the node or edge semantic law.

The hereditary node wrapper derives its input Region from local annotation,
closedness, and actual residency. It permits unrelated constrained records.
It does not assert a hereditary output annotation for arbitrary warm node
cells. That stronger claim needs another returned-node certificate.

ConditionalContinuation constructs a new plain call after a completed actual
prefix. The prefix can be constrained. Its completion remains a premise.
The root serial kernel independently constructs both calls from two initial
requests and composes them through the exact returned state and global memos.

## New native and positional support

NativeUniversalStore retains a native returned-cell law for every source heap.
Empty native tables establish this law from the causal Mu store. Actual
finish installs a derived result law at the exact evaluating owner.
NativePhysicalSplit, Induction, and Trace jointly retain physical facts,
semantic facts, local annotations, and stores through admitted actual traces.
TargetQuery applies those laws to the actual entry source and returned state.
It supports arbitrary machine width. It adds no future range or capacity
premise to an already supplied query trace.

ConstrainedCapEditSupport describes the literal compiled edit positions.
Its actual read induction retains every original supported signed path.
This relation includes disjoint paths, equal paths, and both prefix directions.
The four public editor results require certificates only for literal reached
leaf calls. Those certificates remain explicit conditional premises.

ConstrainedCapSharedSupport derives local laws from actual Operand, Target,
Force, and Leaf reads. Its causal stores cover native tables, Merge entries,
and target slots for the exact captured original forest. A miss derives the
target law before slot storage. A hit reads that causal law. Each native fold
query uses the annotations derived at the actual earlier tail return.
The initial captured forest must be closed. This is stronger than closedness
only for selected values. Richer store retention through the entire editor
and across classes remains open.

MaskCharacterization proves that cap depth d is equivalent to support at every
path of length d. Thus the all-path relation retains the original cap at the
same edited result. The integration kernel derives a cap from initial masks,
constructs its own Required call, retains that cap through the all-path
relation, and constructs its next signed projection at the returned heap.
No future completed call or output annotation is an initial premise.

## Remaining proof work

1. Retain the richer native, Merge, and captured-slot stores through actual
   whole-editor reads. Derive each reached-leaf certificate at its actual
   input state. Retain all masks and the cap through Required, editing, and
   the complete tail-first class schedule. Do not assume a future callback law.
2. Cover the full current source gate. It also admits finite ordinary
   nonhereditary endpoints. The current hereditary leaf-placement family is
   an intermediate domain. General native cap closure and the actual
   optional-binder/reference behavior still need proofs for mixed operands.
3. Prove decreasing constrained recursive descent. Derive filtered owner
   bounds and causal certificates from each full caller's initial state and
   actual past prefixes. Whole plain-node completion does not close this gap.
4. Prove convergence of repeated reduction. Complete remaining recursive
   pruning and compilation callers. A single exact pass and language
   narrowing do not bound intermediate structure or establish a fixed point.
5. Complete current typing and refinement frontend correspondence. Include
   drawn fields, symbolic measures, errors, validation order, and
   generator-specific rank order.
6. Complete concrete runtime and external adapters. Include maps and arrays,
   signed indexes and counters, lazy memo publication and forcing, global
   state, interning, codecs, solver answers, IO, and random draws. Keep
   machine-capacity, primitive, and user-code assumptions explicit.
7. Compose complete public pipelines through construction, transformations,
   graph conversion, exact queries, generation, and sampling. Include actual
   serial warm public calls and discharge each remaining adapter.

Read source-support-boundary.md and next-rich-editor-support.md in the new
evidence directory before the next proof. The proposed pair-occurrence and
optional-binder argument is a proposal. It is not a completed theorem.

## Haskell repair handoff

The recursive field-pool defect is already repaired by b9219b9e in PR #65.
Current source rejects a pool for a field of the datatype itself. The retained
Chain reproducer returns `Left (FieldAtomOnDatatype "Next" 0)`.
Standalone holds still treats supplied pools as opaque. The repair rejects
the invalid derivation configuration. It does not change that evaluator.

Root FINDINGS keeps the external repair handoff first. It records failures,
reproducers, affected paths, commits, checks, and upstream status. Historical
counterexamples retain their original bytes and source dates. No Haskell
change or new Haskell defect occurs in this checkpoint.

## Validation

The final pinned Audit passes 2762 jobs and 62204 dependency checks.
Only propext, Classical.choice, and Quot.sound occur. All fifteen current
production sources pass strict checks without diagnostics. The frozen
checkpoint-validation.json records all imported declaration and integration
checks, final source hashes, canonical logs, and component manifests.
Earlier failed sources and raw logs remain preserved. Canonical replay
retains one older unused-input warning.

Preservation retains 10098 starting files, 2746 older non-Audit proof sources,
and all 239 Haskell files. Sixty-one frozen production manifests retain
519 entries. Stashes and three other worktrees remain unchanged.
The unchanged Haskell source retains its strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence.

Read restart-evidence/20261017-mixed-node-support/ for exact evidence.
These checks verify components. They do not give a meaningful percentage
of whole-library completion. Preserve the optimized interned core and every
older proof, counterexample, repair, and marked draft. The full-library
goal remains active.
