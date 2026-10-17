# Current library proof and complete initial local reduction

Starting published checkpoint: 8c80f5d5. Proof commit: 25726a34.
Source main remains c0cc8a05, merged at 896b0a1c.
The complete public Haskell theorem remains open.

## Top-level target

For each public operation P, prove:

`Valid(input) ∧ Supported_P(input, initialResources) ⇒ runHaskell(P, input) terminates with result ∧ Spec_P(input, result)`.

This is a family of public contracts. Specify the intended behavior first.
Then prove correspondence with the current Haskell implementation. Initial
support must not assume a later successful call or its result. Documented
errors and validation order form part of each contract.

The contracts include distinct accepted terms per node-count size, exact
counts, enumeration order, both rank/unrank inverse laws, transformation
language relations, generation coverage, and sampling laws. Terms,
accepting runs, and generator members have different definitions. Language
equality, inclusion, and representative restriction have different contracts.
Build and theorem totals do not establish a completion percentage.

## Current proof map

| Area | Established component result | Remaining boundary |
| --- | --- | --- |
| Exact Sized queries | Exact term classes and counts, explicit row order, size-major enumeration, and both rank/unrank inverse laws. | Current adapters and complete public composition. |
| Interned construction | Repaired modeled construction, nested Mu and unions, physical stores, and causal payload bounds. | Lazy forcing, publication, and Haskell runtime correspondence. |
| Recursive reads | Initial resources construct closed collection and supported open WarmHead exposure with exact heaps and stable replay. | Arbitrary unsupported open recursion and remaining callers. |
| Comparison, selection, and Merge | Initial counters and causal mass construct modeled workers with histories, effects, memo state, and sufficient fuel. | Remaining callers, separate language-law hypotheses, and runtime correspondence. |
| Recursive intersection | Closed resident operands construct checked native queries with language, full Frame, origins, stores, and initial instruction bounds without finite input Caps. | General adaptive callers and public correspondence. |
| Operand, Target, Force, and Leaf | Initial selected domains and reservations construct complete shared-state returns, language receipts, Frame, and Fits without finite input Caps. | Outer caller composition and runtime correspondence. |
| Mixed editors and class pass | Initial finite tries and supported selections construct complete returns, strict reads, and numeric replay without finite input Caps or semantic Cap-Merge sidecars. | Outer caller composition and runtime correspondence. |
| Scan and selected Required | Initial original records construct exact record selection, Required, caller Post, and selected domains without finite input Caps. | Outer parent and mutual callers. |
| Complete allocated local reduction | Initial stored fields construct their precheck, reached Scan/Required/class continuation, complete old graph and language receipt, same-inventory Frame/Post, and all nine independently larger worker fuels. | Parent reconstruction, mutual recursion, convergence, and public Haskell correspondence. |
| Ordinary recursive caller fragments | Initial finite ordinary profiles construct supported parent and mutual executions with guarded language and stores. | General constrained Mu inputs, open recursion, and convergence. |

Earlier arithmetic, equality, union-find, memo, generation, ranking,
sampling, and restricted-driver results remain preserved. These Lean
definitions are handwritten. They do not establish full correspondence
with compiled Haskell.

## New complete local result

Fourteen additive modules remove the remaining finite Cap coupling from
the local class path. The older proofs and their stronger output Cap laws
retain their bytes. The new execution theorems make no output Cap claim.

ForceNumeric.complete uses its actual initial target slot. A hit retains
the complete state and needs no query reservation. A miss constructs its
own uncapped Target and installs its historical receipt. LeafNumeric.complete
runs that Force and then the actual uncapped checked query. Both results
retain their existing language receipts, Frame, Fits, and worker equations.
Closed selected operands remain explicit lower-level requirements.

EditFrame retains Frame and Fits through the actual node, edge, and Head
operations. Causal guard retention supplies the recursive Head bridge.
EditScans, EditNumeric, and EditListNumeric construct the finite syntax
induction with Populated, HasLeaf, Allowed, and Safe. These support facts
remain explicit. Recursive closure follows from Safe before any Cap law.
Unselected ordinary children can stay open.

ClassNumeric.complete starts fresh target slots at the literal captured
forest. ClassPassNumeric.fold and pass preserve the source tail-first
order and final empty propagation. The same complete physical graph and
strict reads derive the full existing language receipt. ClassCallerNumeric
retains the probe heap and full caller Post at the same inventory as Frame.
The physical Merge store and semantic language coverage remain explicit.
The separate universal Cap-Merge store is no longer needed.

ClassesForecast computes the entire envelope from the original record
list. The already constructed Scan/Required preparation fits its joined
profile. Every positional selected sublist fits the original class fold
from that entry. The selected list and future forest are not initial inputs.
An empty pass requires no query Room. One initial ceiling covers all nine
independently larger source worker fuels.

ScanRequiredClassGraph retains the older stopped and completed graphs
with their exact strict reads. ClassesNumeric.complete then constructs
the original LocalWorker.classes return from initial caller invariants,
proper coherent active original records, and pure initial reservations.
Required derives the selected closed domains at its actual returned heap.
The class pass starts at that exact caller and global memo bundle.
The same return retains the full old semantic receipt, Frame, Fits, Post,
arity, original and returned availability, language, and nine-fuel replay.

LocalForecast computes its branch from the initial stored fields and
equality operations. Only a live branch reserves the complete original
class schedule. The precheck changes equality operations and retains the
native state. LocalNumeric.complete constructs that precheck from an
actual current field load and inherited readiness. Its three branches
return unchanged children, erased children, or the complete class result.
All branches retain the existing graph, strict source reads, full guarded
language receipt, same-inventory Frame/Post, numeric Fits, and exact replay.
Both outer result tables stay exact. The fourth and Merge memo laws remain
tied to the same returned caller.

Initial Context, Frame, Fits, available values, valid cached field load,
inherited readiness, and pure reservations remain explicit. No future
branch, graph, reached range, successful worker, or returned invariant is
an input. No finite input Cap or whole-forest closedness is required.
Standalone lower-level editors still require legitimate selected domains
and safe finite edit syntax. The complete local producer derives these
from its actual reached stages.

Source reads remain logical evidence. Numeric bounds are partly
noncomputable logical majorants. They do not establish extracted Haskell
budgets, concrete host capacity, or actual lazy evaluation events.
True memo answers establish emptiness. False answers do not establish
nonemptiness.

## Missing work

1. Lift the complete local producer through the allocated parent edge
   reconstruction. Derive its initial constructor and numeric reservations
   from source fields. Keep actual returned inventories, physical effects,
   strict reads, and full caller Post. Do not replace a future range premise
   with another premise about a future successful call.
2. Compose the outer node and edge memo calls, descendants, and mutual
   recursion. Prove progress and convergence for the intended domain.
   Cover general constrained Mu and supported open inputs. Preserve the
   actual source refusal policy for unsupported references and busy cells.
3. Connect the handwritten workers to current Haskell adapters, lazy
   forcing, publication order, concrete memo events, validation errors,
   runtime, and resource capacity.
4. Compose every public language, counting, enumeration, ranking,
   generation, and sampling contract through those adapters. Preserve
   exactness, inclusion, and representative restriction as distinct laws.

Read restart-evidence/20261017-uncapped-class/README.md and
checkpoint-validation.json for exact checks and evidence boundaries.
Audit passes 3020 jobs and 65987 theorem dependency checks. All fourteen
final strict logs are empty. All fourteen canonical targets pass.
Earlier failed attempts retain their immutable source and raw logs.
Ten groups check 36 handwritten public declarations, fourteen Receipt
projections, nine reused pure forecast aliases, and thirteen constructed
integrations. Their 72 signature and axiom pairs use only standard axioms.
Eight component manifests retain 325 entries and 325 hash references.

This checkpoint adds no Haskell change or new behavior defect. FINDINGS
keeps the external repair registry first. Field-pool repair b9219b9e is
merged and validated in unchanged source c0cc8a05. The Chain reproducer
returns `Left (FieldAtomOnDatatype "Next" 0)`. Standalone holds retains
opaque-pool evaluation. Record every later Haskell repair with its failure,
reproducer, affected files, commit, checks, and upstream status.
