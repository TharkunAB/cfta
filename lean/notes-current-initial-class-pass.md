# Current library proof status and complete initial class pass

This checkpoint starts at published 9c614fe4. Proof commit is e60bbec0.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove this contract:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of contracts. Specify the intended behavior first. Then
prove that the current Haskell implementation has that behavior. Initial
support and resources must not assume a later successful call or result.
Documented errors and validation order are observable results.

The specifications include exact distinct accepted terms per node-count
size, counts, enumeration order, both rank/unrank inverse laws,
transformation language relations, generation coverage, and sampling laws.
Terms, accepting runs, and generator members have different definitions.
Language equality, inclusion, and representative restriction have different
contracts. Passing builds do not give a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, original explicit row order, size-major enumeration, and rank/unrank inverses. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, including nested Mu and unions, with physical stores and causal payload bounds. | Haskell forcing, lazy publication, and runtime correspondence. |
| Recursive reads | Initial resources construct closed recursive collection and row exposure with exact heaps, literal row widths, and stable replay. | Remaining callers and public correspondence. |
| Comparison and selection | Initial counters and causal mass construct repaired worker success with exact histories, heaps, and stable replay. | Remaining callers and independent language-law hypotheses. |
| General memo-aware Merge | Initial resources compute sufficient work and selection fuel. Full allocated replay retains equality state, heap, memo, and winner. | Remaining callers and Haskell runtime correspondence. |
| Recursive intersection | Supported closed operands construct stable semantic execution at initial computable fuel. | General constrained callers and public correspondence. |
| Native query programs | Initial forecasts construct supported finite indexed query sequences with language, stores, origins, globals, and resources. | Adaptive caller control flow and concrete capacity. |
| Selected Operand | Initial forest, signed path, counters, and causal mass construct projection then Merge, with exact full worker return, receipts, Profile, and Frame. | Remaining caller composition and concrete capacity. |
| Interleaved Target | Initial profiles and reservations construct the actual head Operand, recursive tail, and query sequence with complete receipts, states, and common-fuel worker result. | All-root cap and selected-domain assumptions remain explicit. Runtime correspondence remains open. |
| Shared Force and Leaf | Initial class facts, valid slot laws, and numeric reservations construct miss or hit Force, then Leaf's checked query at its actual return. Both preserve full shared state, receipts, Frames, profiles, caps, inventories, and global memos. | Outer caller composition and runtime correspondence. |
| Mixed editor | Initial finite trie, selected Safe domains, caps, Frame, stores, and numeric reservation construct complete node, forest, and compiled signed edits. Exact worker results retain every shared state field. | Outer caller composition and source runtime correspondence. |
| Class pass | Initial selected domains, caps, Frame, stores, and one tail-first forecast construct complete classes, the right fold, and final empty propagation. Full receipts retain the same Frame inventory and exact common-fuel worker return. | Outer callers, the complete source gate, and Haskell runtime correspondence. |
| Ordinary constrained reduction | Initial profiles construct one complete supported modeled pass with guarded language and stores. | General recursive values, outer descent, and convergence. |

Earlier equality, arithmetic, union-find, memo, generation, ranking,
sampling, and restricted-driver proofs remain preserved. The Lean
definitions are handwritten. These component proofs do not yet establish
complete correspondence with compiled Haskell.

## Complete initial class and class pass

ClassForecast.classProfile uses the literal compiled class editor. The same
forest length supplies the captured and current list counts. classFuel is
the compiled editor's common-six ceiling. Profile growth and monotonicity
retain the initial profile. class_reserved derives the exact editor room
condition from the initial class return forecast.

foldProfile follows the source right fold. The tail profile enters the head
class unchanged. foldFuel takes the maximum of tail fuel and head class
fuel at that exact profile. Append laws preserve this order. The schedule
does not commute classes. Reserved is True for an empty record list. A
nonempty list reserves its whole return profile. Profile growth derives
every tail reservation. The head uses its exact tail-return profile.

ClassNumeric.complete starts the actual class-local slots empty. It keeps
the native tables, equality operations, and Merge memo warm. Its initial
Frame derives the current native laws. Physical and semantic Merge laws
construct the initial shared store. Compiler coherence and the selected
original path domains derive safety for the literal compiled trie. The
complete editor then constructs its own actual graph and reads.

The class wrapper retains the actual lower edit inside its Class graph.
ClassReads contains the same lower reads. The old class verifier derives
physical, language, and arbitrary path-domain transport laws from those
new reads. Receipt alignment replaces only admission with the returned
Frame admission. The complete receipt and Frame have the same computed
inventory. The same return retains forecast Fits, semantic Merge laws,
output caps at classDepth, equal forest length, and exact runClass with
six equal computed fuels.

ClassPassNumeric.fold constructs the tail first. Its full receipt transports
the original selected domains to the actual returned forest. The head
captures that forest and current native and equality state. It receives
the tail's Frame, Fits, Merge tables, global memos, and produced depth caps.
Forest transport proves equal length. This equality justifies the fixed
original count in the pure schedule. The proof lifts both actual worker
returns to the shared fold ceiling and constructs their literal bind.

The same returned fold contains its actual graph, exact reads, complete
receipt, matching-inventory Frame, Fits at foldProfile, semantic Merge
store, caps at foldDepth, equal length, and exact common-six worker result.
ClassPassNumeric.pass performs literal final empty propagation after that
fold. It changes no checked state or Merge table. Both propagation branches
preserve forest length and the output caps.

No supplied class graph, future completed editor or fold, successful future
worker, ClassRanges, ClassPass.Ranges, reached bound, or callback resource
law is an input. Size-based fuels and cap depths remain noncomputable
logical definitions. They do not establish executable Haskell budgets.
The numeric ceilings do not count cumulative host instructions.

## Constructed integration and source comparison

The concrete fixture uses a singleton forest whose parent carries a
nonempty equality guard. It proves the parent open and outside Cap 0.
The selected class paths are [[0,0],[0,1]]. They reach closed left and right
children. A third open recursion reference remains unselected. A valid
stored equality descent operation is present at entry.

The single-class integration chooses its own finite width from its initial
class profile. It constructs actual Class reads, the full returned receipt,
Frame, Fits, caps, equal forest length, and exact worker result. The original
equality descent record remains present and valid. The separate generic
class integration derives class-satisfying forest language equivalence
and exact replay under six independently enlarged worker fuels.

The two-class integration uses two repeated records. It derives its own
initial width from the cumulative fold profile. It exposes both actual
Class graphs and their shared intermediate forest, checked state, Merge
memo, and global bundle. The second class captures that complete first
return. The final Pass graph has exactly those two calls. Its result is
literal propagation of the raw final class forest. The valid equality
descent record remains present.

The empty-pass integration calls the new initial producer with no records.
It assumes no numeric room. Its exact worker equation identifies the
returned forest with literal propagation and the returned checked state
and Merge memo with the supplied input. Every fuel tuple has that same
empty-pass return.

The source comparison checks Equality/Operations.hs against the retained
right fold, actual class capture, selected other-path targets, ascending
path edits, and final empty propagation. It does not establish Haskell
lazy callback demand or host table publication. Read source-class-comparison.md
in lean/restart-evidence/20261017-initial-class-resources/.

## Exact support and contract boundaries

Selected ForestClosed domains permit unrelated open ordinary roots and
siblings. A separate cap premise bounds every original input root. Each
class captures its actual current forest. The prior class output caps
supply the next class input caps. The cap premise can exclude an unrelated
nonhereditary Mu body. General source support must discharge or replace
that stronger premise separately.

The Target receipt retains one-way inclusion for nonempty proper selected
paths. Merge can overapproximate its input. The whole Target language is
not proved equal to the intersection. Each checked native query retains
its exact intersection law. A class and a class pass narrow their forest
and preserve original terms that satisfy their class or every class,
respectively. No unconditional whole-editor language equality is claimed.

Full native and equality state, physical and semantic Merge tables, and
global memo receipts follow each actual class return. Each next class
starts its own local target table empty. Historical target receipts in
one class remain tied to that class's immutable captured base and forest.
They are separate from the current returned Frame inventory.

Numeric bounds control constructor counters, domain counters, and causal
constructor payload mass. Equality-table size and instruction counts,
concrete bytes, solver work, wall time, concurrency, Haskell lazy demand,
and memo publication remain separate obligations.

## Next caller: outer constrained reduction

Compose the initial class pass into the current caller context. Retain its
fourth memo, probes, actual inventory, query Frame, numeric Fits, and all
global tables. Existing actual-read and physical-effect theorems can derive
caller invariants from the same newly constructed return. They must not
replace initial execution with a supplied successful pass.

Then construct required-child preparation, refused-class checks, active
and stored outer descent, and the complete source gate from initial
resources. Each caller must reserve its actual reached sequence and
transport selected domains and caps through preceding returns. General
constrained Mu support and repeated reduction convergence remain open.

## Remaining library work

1. Complete outer caller composition, required-child preparation, refused
   checks, active and stored descent, arbitrary constrained Mu, and the
   full source gate. Separate selected domains from all-root caps.
2. Prove repeated reduction convergence and remaining recursive callers.
3. Complete current typing, refinement, drawn-field, symbolic-measure,
   observable-error, validation-order, and generator-rank adapters.
4. Complete solver, runtime, IO, randomness, capacity, and user-code adapters.
5. Compose complete public construction, transformation, graph conversion,
   exact query, generation, and sampling correctness.

The complete library goal stays active.

## Haskell repair handoff

No Haskell patch or new behavior defect is added. Root FINDINGS keeps the
external repair registry first. Repair b9219b9e is merged in source
c0cc8a05. Derivation validation rejects a field pool for the datatype itself.
The retained Chain reproducer returns
`Left (FieldAtomOnDatatype "Next" 0)`. Standalone `holds` still treats pool
descendants as opaque. Reuse the unchanged strict Nix all-component build,
798 examples plus golden, Fourmolu, and Cabal-gild evidence. Record each
later repair in FINDINGS with its failure, executable reproducer, affected
paths, commit, checks, and upstream status.

## Validation and preservation

The pinned Lean 4.34.1 Audit passes 2948 jobs and 65194 dependency checks.
All three final production strict logs are empty. Every canonical target
passes. All 36 full signature and axiom pairs pass in seven groups: 30 public
declarations and six constructed checks. Four component manifests verify
98 entries. Only propext, Classical.choice, and Quot.sound occur. Read
checkpoint-validation.json in
lean/restart-evidence/20261017-initial-class-resources/ for hashes and
successful logs.

Preservation retains 14690 starting files, 2944 older non-Audit proof sources,
all 239 Haskell files, all 206 active-package files, two stashes, and three
other worktrees. All 90 frozen module manifests retain 705 entries.
Older proofs, counterexamples, repairs, and marked drafts retain their bytes.
The previous editor checkpoint's documented early-log gap remains unchanged.
It is not a claim of recovered evidence. New checks use unique prefixes
and execute their immutable source snapshots directly.
