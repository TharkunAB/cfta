# Next general progress: constrained structural bounds

Reviewed at 2026-10-16T15:59:05+02:00. Read-only source and declaration audit. No build, source edit, or new Haskell defect is claimed.

The new plain theorem removes the successful-execution premise for one effective-own-empty Region pass. The next constrained theorem needs TWO independent ingredients: reached native machine-key safety and a structural recursive progress certificate. Current semantic correctness and physical growth do not supply the second ingredient.

## Exact remaining inputs

`SourceCurrentAllocatedLocalReduction.Ranges` (line 68) quantifies only actual precheck returns `.classes records`. It asks for `SourceCurrentConjunctionScanClassPass.Ranges` at the literal prefix-returned checked state. That structure (line 80) has a Scan plan and a Pass plan after an actual successful Scan, exact Retained records, and an actual required-worker return.

`SourceCurrentConjunctionClassScanCompletion.Ranges` (line 26) follows current primary/secondary gate outcomes and false conjunction-memo continuations. Only the primary-true/secondary-false branch asks for `AllocatedSeededQuery.SeededRanges`. The seed rotation is `rest ++ [seed]`. Its `FoldRanges` (line 71) asks for native WordRanges at the actual completed head-operand and tail-fold return. ClassPass.Ranges follows the tail-first class fold. SharedEditRanges follows actual selected-child prefixes and native leaf requests. These are checks at exact reached states. They are not supplied completed queries or semantic answers.

`SourceCurrentAllocatedParentWorkerActual.ResidentRanges` (line 49) needs that full Local range plan only if the original raw guard is not contradictory and its actual initial field load succeeds. Context, inherited EqReady, and EdgeResident derive the physical field/readiness/child facts. They do not by themselves derive every native key range.

`SourceCurrentAllocatedNativeRequestBounds.WordRanges` (line 134) is `∀ fuel next after, Steps fuel control state next after → Words width next`. `Words` checks KeySafe for reached node and edge requests. A node check is conditional on a cacheable `requestKey`; the edge check is unconditional. These are finite machine-key bounds, not a completion witness, language law, or well-foundedness measure. Do not describe them as asymptotic bounds or a finite inventory of future keys. Current outer WorkerRanges follows supplied bounded observations and imposes no continuation condition after failure. A vacuous zero-fuel WorkerRanges proof therefore cannot establish outer success.

## Why the plain argument does not extend directly

`PartialPlainRegion.Region` stops at Mu and union. Every traversed ordinary edge has EFFECTIVE own accessor `.ok (some [])`. Empty raw equality storage is insufficient when positive guard fields encode equalities. PlainInputs.own_empty derives the exact source accessor fact.

The plain parent theorem obtains original/erased/singleton-Empty child Shape. Selected nonempty classes can replace a child with a newly constructed intersection. Such a child need not be the original child, an erased slot, or Empty. Thus the current ReturnedDomain.Stored Shape is not a suitable general invariant. Semantic NodeLaw/EdgeLaw, closure of free variables, physical residency, and heap growth cannot imply that literal child-list shape or ordinary-height descent.

Ordinary height treats Mu and explicit union as opaque. Unfolding or binder cleanup can expose a larger ordinary body. `SourceEqualityPartialHeightBoundary.actual_heights` and `.not_parent_height_bound` record a checked historical worker fixture with heights `(2,1,3)`. `SourceEqualityOuterCallerCycle.actual_cycle` and `.not_wellFounded` record a historical two-key dependency cycle. These are warnings against unrestricted height/key arguments. They use the historical local worker and do NOT establish a current-gate counterexample. Current source contains the endpoint/descendant blocker repair; do not transfer these old receipts to the current caller without proving its actual gates select the same branch.

The live source states the remaining issue explicitly in Equality/Operations.hs:119-142. Preventing selected endpoints above constrained Mu avoids the known cycle, but does not prove all recursive cycles impossible. Unequal-length classes can move a constrained node into a deeper unfolding of an unconstrained recursive node. Inherited-first combination and descent must be part of any proposed measure. Ordinary height alone and the number of initial request keys do not address that migration.

## Smallest concrete next proof stage

Start with a stricter, input-defined constrained domain: finite ordinary trees with Empty, ordinary rows, and recursively finite ordinary children; exclude Mu, explicit union, and references THROUGHOUT this first domain. Allow nonempty normalized own classes. This is a substantive extension of the plain Region, while avoiding a claim about general recursive constraints.

The first new lemma family should prove **structural result certificates for actual checked native requests on that domain**, independently of language semantics: returned node remains in the domain, and its ordinary height is no greater than EACH original operand. The per-input bound is needed: a class target can be taller than the leaf being narrowed. A bound only by the maximum of the two operands does not prove the leaf remains below its outer parent. Use the actual ordinary pair/edge walks and literal makeEdge/makeNode/union work. This is a proposed obligation, not an existing theorem.

Warm native hits need the same structural certificate for their captured requests. Existing Context.sound proves semantic outer result laws and is insufficient. Derive a structural cache invariant from empty cells, actual publication/demand, and actual producers, then retain it through reached effects. Do not assume a future producer certificate or reset a current warm table. A first cold instance is valid; serial warm closure must be proved from actual previous returns. Existing ReturnedDomain/FlatMemo lifecycle patterns show how to store certificates at exact owners.

Next compose the structural certificates through literal projection, merge, required paths, target/leaf requests, and class edits. Existing MergedOrdinaryHeight provides makeNode and ordinaryUnion maximum-height laws; they are constructor components, not whole checked-native or class-pass nonincrease. Prove each edited current input is nonincreasing and remains in the finite ordinary domain. Preserve original row order, raw full guards, and actual checked/memo state.

Only after that component is proved should Parent return a generalized certificate: returned children stay in the domain and have height at most the original edge height. Store it against the actual captured edge owner. Then reuse the existing node-rank induction, fixed sibling cap, forward owner frame, and reverse NoNewActive machinery. Reached WordRanges remain an explicit separate machine-safety condition until a causal allocation-bound theorem discharges them. No future successful body, desired semantic answer, finite future-key inventory, or arbitrary class-output height oracle is needed for this proof stage.

General Mu/unconstrained-unfolding inputs need a different well-founded progress/domain theorem that survives constraint migration. The source's two sufficient-case comments are not yet current formal theorems. Even a completed proof for those cases would not establish arbitrary unequal-length classes, all-input general completion, or repeated-pass convergence. Host forcing, concurrent publication, concrete containers, and frontend correspondence remain separate full-goal work.
