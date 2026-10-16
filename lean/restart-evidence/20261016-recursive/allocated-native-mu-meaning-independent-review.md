# Independent review of local Mu meaning and contextual node adapter

Reviewed 2026-10-16 04:54 CEST. Read-only review. No proof source edits or new builds.

Reviewed source hashes:
- `SourceCurrentAllocatedNativeMuMeaning.lean`: `c8f228087e9e4b745b779f424c57356fcca40051fef51e34e72932bdad479a3e`
- `SourceCurrentAllocatedNativeClosedReceipts.lean`: `374655d6eefd43cd4b8557cc429657cd251ed537bcfc27b57871ce578f814ebe`
- `SourceCurrentAllocatedNativeContextCache.lean`: `eef24f799571d5900e746fd9f7b4207a533763b1ed50522857f196296cc7274b`

## Finding

No mathematical defect or circular output-result assumption was found in
MuMeaning or ClosedReceipts.mu_node_law. Their claims are local conditional
language laws. They do not yet prove the semantics or termination of a general
actual checked compileMu execution.

## Original-rank descent and candidate containment

MuMeaning:133-159 derives descent from the independent RankedInput.body law.
It converts canonical pair ranks back to ordered left/right ranks. If both
operands are Mu, both body ranks decrease. If exactly one is Mu, that rank
strictly decreases and the other rank stays the same. The sum is strictly
below the original bound in either case. Nonempty and valid original-input
premises are explicit. No output rank or output syntax measure is assumed.

MuMeaning:103-116 performs strong induction on the original rank-sum bound.
After descent it chooses lower=first+second, weakens old context completeness
to lower, and derives candidate containment by the strict induction hypothesis.
Only then does complete_extend install the actual result language as the fresh
pair candidate. It applies the local body law and the actual binder equation.
The final candidate containment is not a public premise of this theorem.
The rank bound is a semantic derivation bound. It is not native execution fuel.

Soundness:65-80 tests the monotone physical body transformer at the fixed
original pair language and uses least_le. It needs only one-sided soundness
of seen pairs. It does not assume exact enclosing pair equality for arbitrary
candidates. Freshness ensures the newly bound pair does not overwrite an old
context obligation. The completeness context uses the dual one-sided law.

## Actual constructor linkage

optionalBinder_least:27-38 uses the exact maybeMu done receipt at the supplied
before heap and the result theorem of optionalBinder_checked. Its explicit
SemanticHeap, GuardedProbeHeap and body availability premises support the
stored callback compilation. SourceRecursiveIntersectionGuardedEffects:21-59
handles both actual branches: real binder construction with its source
substitution/probes/cleanup, and the unchanged-body branch when the pair is
not free. It does not replace maybeMu by a pure function or an eager native
intersection execution. The actual returned value and after heap come from
the same supplied done equation. No final heap invariant is assumed here.

The result equality is a least-body-transformer law, not a proof of all
constructor heap effects. Those physical effects remain available from the
separate constructor verified/ready theorems and must be composed at the
actual checked execution state.

## Exact request, domain and binding scope

ClosedReceipts.mu_node_law:25-70 computes the canonical pair directly from
inputOf request.left/right. Its done receipt uses that same pair. Its local
body laws extend request.domain.key with that pair; NodeLaw uses the original
request domain. The key and domain are not silently swapped or rebound.
NodeInputs supplies valid left/right model inputs when each NodeLaw field is
used. No final value law is supplied: bodySound/bodyComplete describe the
intermediate physical body in extended pair contexts, while the theorem
derives the final optional-binder result law.

Important remaining source adapter: bindings is an arbitrary explicit list.
The theorem does not identify it with the literal source left-before-right
Mu binding names, or invert an actual checked compileMu trace. This is sound
because the body laws refer to that same extension, and pair contexts inspect
seen pairs. It is not yet an exact source branch receipt.

The next actual-source application must derive:

- the chosen bothMu/leftMu/rightMu branch, freshness and complete physical
  operand identities from the original scope;
- equality of the physical min/max pair and the semantic pair, using Original
  codecs and physical identity readback;
- bindings=(SourceRecursiveIntersectionEnvironment.bindings left right).map
  Prod.fst, in left-before-right order, plus the actual entered_key equation;
- physical body inputs equal the two semantic unfolded inputs, using existing
  SourceRecursiveIntersectionCode.body_encoded and original source scope;
- the local bodySound/bodyComplete laws from the actual recursive body trace,
  including contextual memo-hit laws at the fixed original input model;
- the actual returned body availability, actual maybeMu done receipt, physical
  growth and finish-cell receipt at the same reached native/equality state.

The local body premises are substantial. They must not be advertised as
already derived checked recursive body semantics. No old eager Evaluation or
Produced theorem can discharge them merely by matching an outer request.

## Allowed claim

The completed actual optional-binder constructor transports derived local
unfolded-body laws to a contextual NodeLaw. Its semantic completeness induction
closes the previously explicit fresh-candidate containment obligation by
strict original-rank descent. General checked body completion, actual child
law derivation, contextual warm-cache admission and full caller composition
remain separate obligations. Current comments in the reviewed files state
that component boundary accurately.
