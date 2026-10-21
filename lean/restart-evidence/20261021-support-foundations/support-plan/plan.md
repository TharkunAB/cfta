# Structural support at actual cache readers

Reviewed: 2026-10-21 02:00 CEST. This note is a proof plan, except for the
separate checked Empty support component. No Lean job was run for this note.

## Existing strongest reusable contracts

`SourceCurrentMemoMergeEffects.Stored` stores exact original keys, original
and result availability, and conditional result closedness. `hit_original`
uses coherent available readback to identify the full captured original.
It does not constrain how the result relates structurally to that original.

`SourceCurrentMemoMergeLanguage.CacheCovers` stores original-language inclusion
into result-language. `run_language`, `call_language` and `cold_language`
derive it by actual mutual Run/Call induction, body Certified contracts and
first-winner reread. That direction is necessary for merge overapproximation.
It is vacuous on Empty and cannot exclude an unsupported Empty-to-owner hit.
The actual SourceCurrentPhysicalMergeSupportBoundary.empty_hit proves this
boundary for physical Stored. This is a fabricated initial table, not a run
from an empty completed table.

`SourceCurrentHereditaryMerge.Certificate` and `Stored` already use the useful
nonhistorical pattern: Annotated valid original implies Annotated valid result.
Its run/call/cold proofs discharge actual recursive calls and preserve local
laws at hits and first-writer completion. `SourceCurrentHereditaryMergeStore`
adds actual comparison/unfold effects and the conditional causal Mu store.
These are the right induction templates. Produced or Writer alone would be
a further historical existential, not the requested new structural law.
Guard-only annotation support cannot constrain row symbols or positions.
The finite-ordinary domain/profile/guard caches are conditional on their
restricted original domains; they do not supply general recursive support.

Native NodeMeaning/EdgeMeaning give exact independent intersection language
only under empty-domain and closed-input hypotheses. They do not prove a
structural source law for arbitrary entered requests. In particular, an
unproductive closed recursive result can have an empty least language;
semantic equivalence alone cannot identify its stored row structure.

## Checked smallest foundation

The separate frozen package /tmp/mcfta-merge-empty-support contains:

    EmptySafe memo := forall entry,
      memo Empty.referenceOf = some entry -> entry.result = Empty

    empty_safe : EmptySafe empty
    run actual safe : EmptySafe saved
    call actual safe : EmptySafe saved /\ (input = Empty -> output = Empty)

These statements retain the exact Run/Call input, result, heap and table
indices. They need no physical, semantic or availability premise.
InternedEmptyNormalization.reference_empty is the existing exact tagged-key
inversion. Empty's actual miss body is pure Empty. Each completion checks the
new candidate and retains the old winner. The proof is an actual mutual
instruction induction. It excludes empty_hit with any non-Empty owner under
this additional invariant. It does not prove full structural support.

Final source SHA256:
75ff3cc7e9e4b1416ad1a297087cd2e517f27ad2e4f356da4e2c8b1d3d358af3.
Selected strict direct-3 and complete public-1 both pass. No canonical job
or official source edit belongs to this component.

## Proposed stronger signature support

Let P : Symbol -> Nat -> Prop be an allowed live row signature predicate.
Use a structural value predicate H_P with these clauses:

- Empty and references satisfy H_P.
- A node satisfies H_P when every literal row satisfies E_P.
- A union satisfies H_P when every literal member satisfies H_P.
- A Mu satisfies H_P when its stored body satisfies H_P.

For a complete row e, the necessary raw-row predicate is:

    E_P e := Empty is in e.children OR
      (P e.symbol e.children.length AND forall c in e.children, H_P c).

The dead-row arm is essential. The actual checked native sentinel creates
makeEdge left.symbol Top [Empty]. Its arity is one even when the original
row has another arity. Unconditional raw row signature preservation is false
for this literal branch. Actual makeNode removes all such rows. A live row
therefore uses the second arm. This is a source-level obstruction to the
naive candidate, not a runtime defect or a checked new counterexample.

Use a cache law attached to each full captured original, not to the heap:

    CacheSupport P memo := forall key entry,
      memo key = some entry -> (H_P entry.original -> H_P entry.result).

The target Merge theorem is the existing effect-contract shape:

    actual : Call clear top input before memo output after saved
    SemanticReady before; CostHeap before; physical Stored before memo;
    CacheSupport P memo; Available before input
    ---------------------------------------------------------------
    Effect before after AND physical Stored after saved AND
    CacheSupport P saved AND (H_P input -> H_P output).

The Run companion needs the same existing Certified grammar instantiated
with this request contract. It cannot claim arbitrary Work preserves support
without the actual local constructor certificate. Empty tables discharge
CacheSupport without a premise. A retained winner uses its own captured law
after hit_original; a miss must prove its candidate before remember/reread.
No Top-valid premise is needed for a signature predicate that ignores guards.

Required local proof obligations, all unproved here:

1. makeEdge preserves its exact symbol, child order and length at available
   coherent inputs. makeNode selects only canonical surviving input rows.
   The dead-row arm is discharged when a row survives.
2. makeUnion/ordinaryUnion normalization preserves H_P, including flattened
   operands and normalized ordinary rows. Do not assume literal operand
   identity across union normalization.
3. Actual selection returns only original retained values. Use
   SourceMergedSelection.retain_members and the distinct selection member law.
   Comparison effects still need the existing semantic/cost/store certificates;
   there is no need to identify a semantic cover as a literal child copy.
4. Small groups use ordered child certificates and unchanged row signatures.
   Large groups use MergedSourceGrouping's exact symbol+arity class and
   actual column/map lengths. Top guard insertion does not add a signature.
5. The actual body and mutual Run/Call induction preserve CacheSupport.
   Reuse HereditaryMerge's certification route and winner readback, rather
   than proving another existential production predicate.

This is a coarse safety invariant. It permits new combinations of supported
columns and does not identify an original occurrence, same path, full row,
strict value mass or active cache key. It cannot alone prove owner exclusion.
EmptySafe must still be retained separately: H_P treats references and
row-free recursive records permissively and is not Empty identity.

## Native propagation needs causal local premises

The reusable native pattern is already explicit in:

- HereditaryNativeScope.Bindings: exact available source Mu records for all
  actual domain names. A bare reference annotation has no stored-body content.
- HereditaryNativeCode.NodeLaw/EdgeLaw: conditional support from BOTH actual
  operands plus the bound names, for the exact captured request.
- HereditaryConstruction.MuStored: BOTH complete stored probes support the
  stored body. Physical Facts, Good or heap growth does not imply this law.
- HereditaryNativeCache.Stored: returned node/edge maps carry local laws for
  their own captured requests. Initial empty result tables satisfy them.
- HereditaryNativeUniversalStore.Stored: constructor law plus native laws at
  every source heap. This avoids inventing a certificate at a later query view.
- HereditaryNativePhysicalTrace.completed: actual checked-trace induction
  derives local laws before actual protected finish steps install returned cells.

The prospective signature versions replace Annotated by H_P and row annotation
by E_P. A signature Binders law must be derived from the actual stored probe
and callback construction, including warm hits and generated encode roots.
A signature native NodeLaw must require support for domain binding readbacks;
otherwise an internal reference can read an unrelated unsupported stored Mu.
Clean controls only exclude caller-written driver finish instructions. Clean
and Good do not supply either structural premise by themselves.

For arbitrary unfinished native prefixes, use the existing physical bind-prefix
split and protected finish route, as NativePrefixWriterMaps does. It is valid
to expose only laws for actual returned cells. Do not infer final History or
final Certified for the entire reached control. A global unary inventory of
all unrelated resident values is stronger than necessary and is not proposed.

## Scope after this work

Empty support is checked in the separate component. Signature support and its
causal construction/entered binding/Required adapters remain proposed proofs.
No desired source ancestry is a premise of the proposed cache certificate.
No forward rank, convergence, general outer completion, active owner exclusion,
whole startup proof or production Haskell refinement follows from this note.
