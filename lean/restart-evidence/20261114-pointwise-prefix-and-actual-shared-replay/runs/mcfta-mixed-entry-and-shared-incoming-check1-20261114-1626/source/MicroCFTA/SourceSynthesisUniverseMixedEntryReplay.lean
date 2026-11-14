-- UNCOMPILED SOURCE DRAFT. Root owns validation.
import MicroCFTA.SourceRecursiveIntersectionReplayEffects
import MicroCFTA.SourceSynthesisCurrentUniverseAliasAtoms

/-!
# The original mixed domain after actual later effects

Canonical domain replay returns the original entry in the unchanged later
cache. Both checked source aliases can then use that original domain and
the actual later machine. No second initialization or future result is used.
-/
namespace MicroCFTA.SourceSynthesisUniverseMixedEntryReplay
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel

set_option autoImplicit false

section Generic
variable {Symbol Guard : Type}

/-- The original literal entry replays with the same identity and no later cache effect. -/
theorem mixed_entry_replay_after_extension
    (before after : Machine Symbol Guard) (valid : Cache.Valid before.domains)
    (left right : Value Symbol Guard) (first second : Nat)
    (growth : Extension
      ⟨before.heap, (SourceRecursiveIntersectionEnvironment.enter before.domains
        IntersectionEmptyDomain.emptyKey left right first second).2⟩ after) :
    SourceRecursiveIntersectionEnvironment.enter after.domains IntersectionEmptyDomain.emptyKey
        left right first second =
      ((SourceRecursiveIntersectionEnvironment.enter before.domains IntersectionEmptyDomain.emptyKey
        left right first second).1, after.domains) := by
  exact make_domain_replay before.domains after.domains _ valid growth.domains

end Generic

open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

/-- Both same-source aliases retain their checked value in the original domain after actual extensions. -/
theorem current_stored_universe_open_alias_checked_after_mixed_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (heap : State Symbol Guard) (growth : Grows sourceHeap heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (patternId : Nat)
    (patternAvailable : Available heap pattern) (patternClosed : pattern.free = [])
    (patternIdentity : SourceRecursiveIntersectionControl.identity pattern = some patternId)
    (patternShape : SourceRecursiveIntersectionControl.tag pattern = 1 ∨
      SourceRecursiveIntersectionControl.tag pattern = 3)
    (left : Value Symbol Guard)
    (leftAlias : left = .reference (.interned entry.identity) ∨ left = body) :
    let universeValue : Value Symbol Guard := .mu entry body depth ordinary
    let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
      universeValue pattern entry.identity patternId
    let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
    ∀ later : Machine Symbol Guard, SourceRecursiveIntersectionKernel.Valid later → Extension initial later →
      SourceRecursiveIntersectionEnvironment.enter later.domains IntersectionEmptyDomain.emptyKey
          universeValue pattern entry.identity patternId = (entered.1, later.domains) ∧
      ∀ fuel : Nat,
      Checked later
        (execute top SourceEqualityPCSNativeEdge.conjoin fuel entered.1 left universeValue later)
        (fun after value => Available after.heap value ∧ value = universeValue ∧
          ∀ atom ∈ InternedBoundaryAtoms.atoms value, atom = .mu entry.identity) := by
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let entered := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let initial : Machine Symbol Guard := ⟨heap, entered.2⟩
  dsimp only
  intro later laterValid continuation
  have replay := mixed_entry_replay_after_extension
    (⟨heap, domains⟩ : Machine Symbol Guard) later cacheValid
    universeValue pattern entry.identity patternId continuation
  refine ⟨replay, ?_⟩
  intro fuel
  have laterGrowth : Grows sourceHeap later.heap := grows_trans growth continuation.heap
  have laterPattern : Available later.heap pattern := continuation.available pattern patternAvailable
  have checked := SourceSynthesisCurrentUniverseAliasAtoms.current_stored_universe_open_alias_checked_after_mixed_entry
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    later.heap laterValid.1 laterGrowth later.domains laterValid.2 pattern patternId
    laterPattern patternClosed patternIdentity patternShape left leftAlias fuel
  dsimp only at checked
  rw [replay] at checked
  exact checked

end MicroCFTA.SourceSynthesisUniverseMixedEntryReplay

#print axioms MicroCFTA.SourceSynthesisUniverseMixedEntryReplay.mixed_entry_replay_after_extension
#print axioms MicroCFTA.SourceSynthesisUniverseMixedEntryReplay.current_stored_universe_open_alias_checked_after_mixed_extension
