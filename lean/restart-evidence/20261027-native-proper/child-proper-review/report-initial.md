# Actual shallow-child ProperState preservation

Recorded 2026-10-27T22:56:26.845588+01:00. Status: OPEN.
Draft V1 is UNTESTED. Root owns all compiler and integration checks.
No compiler, native/runtime evaluation, Git, repository write, network or
board operation was performed by this worker. Earlier frozen areas are untouched.

The one new module has three public theorems and no new operational definition,
predicate, structure or instance. It follows the existing CachedPrepareCanonical
proof shape. Original source files and theorem declarations remain unchanged.

## Exact API

Namespace MicroCFTA.SourcePruningEnumerationShallowChild:
prepared_proper scs value before after action fragment
  (proper : EnumerationProgress.ProperState before)
  (inputs : EnumerationProgress.ProperInputs scs)
  (prepared : prepareChild scs value = some action)
  (success : Success action before fragment after) : ProperState after.

Namespace MicroCFTA.SourcePruningEnumerationCachedPrepare:
rows_proper heap fuel scs value before rows
  (proper : ProperState before.core) (inputs : ProperInputs scs)
  (cached : prepareChild heap fuel scs value before = some rows) :
  ∀fragment after,(fragment,after)∈rows→ProperState after.core.

cache_proper heap fuel scs value before after
  (proper : ProperState before.core) (inputs : ProperInputs scs)
  (observed : (match prepareChild heap fuel scs value before with
    | some [] => some before
    | some [(_,result)] => some result
    | _ => none) = some after) : ProperState after.core.

EnumGuard and NativeGuard retain their existing independent Type parameters.
Symbol remains SourcePruningTemplates.Symbol. No DecidableEq assumption is added.
Cached observers use the ACTUAL same input heap and actual count fuel.
They do not assume count adequacy separately, because actual Some preparation
is the execution receipt. No assumed future cache correctness is an input.

## Proof connection

Empty has a prepared reject action, but reject has no successful raw row.
Reference has no preparation. Both cases use actual constructor observations.
An ordinary node with any terminal input has no preparation. In the actual
successful branch, that terminal-any test is false. ProperInputs supplies Valid
and nonempty for each inherited trie. The actual branch supplies nonterminal.
Thus the literal fresh payload has ProperValue. Exact allocation and bind
readback identify its actual intermediate core. Existing allocation_proper and
setValue_proper preserve ProperState at those same cores. The final pure row
identifies the actual reached core. No desired endpoint invariant is supplied.

Mu and Union remain in scope. Their actual successful branch allocates an empty
suspended bucket. allocation_proper proves the result directly. The proof does
not store inherited paths on those opaque values, infer Discharged or require
nonrecursive constructors. Empty buckets are proper by the existing definition.

For cached preparation, erase_some identifies EXACT raw rows and their actual
cached cores. Membership in an actual returned cached row gives the required
raw Success. prepared_proper then proves that attached row's core proper.
The cache observer covers the actual synthetic unchanged cache on some[]
rejection and the attached singleton cache on success. None and longer rows
cannot meet that actual observation. It does not equate caches to raw cores
without the existing erasure equation.

## Origin inputs and remaining scope

ProperInputs permits terminal tries before dispatch. Nonterminal is DERIVED
from actual shallow preparation, not added as a caller premise. Existing
EnumerationProgress.descend_proper derives ProperInputs for actual descendScs
from valid suspended inputs; this is a concrete source connection for traversal.
This draft does not prove terminal incoming/assimilation preservation, native
head resource completion, whole recursive ProperState induction or coverage.
Those producers must still supply genuine old ProperState and ProperInputs.

The proof uses no Graph or fabricated native language correspondence. The reused
allocation_proper and setValue_proper signatures are graph-independent. Importing
EnumerationProgress does not transfer its graph evaluator preservation facts.

No supplied desired final ProperState, successful future callback, assignment,
Satisfies, universal Ranges, availability, Packet or language admission is added.
This local actual-success proof does not derive Safe, index correctness, native
heap correctness, nonempty output, model acceptance, rendering or physical
Haskell correspondence. No Haskell defect or source change is claimed.

The only unresolved current proof risk is compiler elaboration/linter validation
of the new Bool.eq_false_iff/List.any_eq_true payload step and copied bind
inversions. These use existing source proof patterns. No semantic obstruction
was found in the bounded source review. V1 and exact originals are preserved.
The bundle remains OPEN until actual Root check receipts and later review cues.
