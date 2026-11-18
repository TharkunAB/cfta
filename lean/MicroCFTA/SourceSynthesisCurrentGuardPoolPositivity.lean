import MicroCFTA.SourceSynthesisOriginalSharedRankCompletion
import MicroCFTA.SourceSynthesisCurrentNativeGuardOrigins
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.SourceCurrentNativeGuardAlphabet

namespace MicroCFTA.SourceSynthesisCurrentGuardPoolPositivity
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisOriginalSharedRankCompletion (seed)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisOriginalGuardAlphabet (alphabet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
set_option autoImplicit false

theorem native_guard_pool_advance_positive
    (initial : List Guard)
    (initialTop : ∀ guard ∈ initial, guard.guard = .top)
    (count : Nat) :
    ∀ guard ∈ SourceCurrentNativeGuardAlphabet.advance initial count,
      guard.guard = .top ∧ (SourceCompactGuards.positive guard.guard).isSome = true
 := by
  induction count generalizing initial with
  | zero =>
      intro guard member
      have topField := initialTop guard member
      exact ⟨topField, by rw [topField]; rfl⟩
  | succ count ih =>
      have nextTop : ∀ guard ∈ SourceCurrentNativeGuardAlphabet.step initial, guard.guard = .top := by
        intro guard member
        unfold SourceCurrentNativeGuardAlphabet.step at member
        rcases List.mem_append.mp member with previous | paired
        · rcases List.mem_append.mp previous with original | unit
          · exact initialTop guard original
          · cases List.mem_singleton.mp unit
            rfl
        · obtain ⟨first, firstIn, secondMap⟩ := List.mem_flatMap.mp paired
          obtain ⟨second, secondIn, rfl⟩ := List.mem_map.mp secondMap
          dsimp only [SourceEqualityPCSNativeEdge.conjoin, SourceEqualityConstraintConstructors.conjoin]
          rw [initialTop first firstIn, initialTop second secondIn]
          simp [GuardConjunction.merge, GuardConjunction.normalize,
            GuardConjunction.atoms, GuardConjunction.canonical, GuardConjunction.conjoin]
      change ∀ guard ∈ SourceCurrentNativeGuardAlphabet.advance
        (SourceCurrentNativeGuardAlphabet.step initial) count,
        guard.guard = .top ∧ (SourceCompactGuards.positive guard.guard).isSome = true
      exact ih (SourceCurrentNativeGuardAlphabet.step initial) nextTop

theorem accepted_source_seed_guard_pool_positive
    [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (rootValue : Value Symbol Guard) (sourceHeap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty =
      InternedNestedConstruction.Outcome.done rootValue sourceHeap) :
    ∀ (count : Nat) (guard : Guard),
      guard ∈ SourceCurrentNativeGuardAlphabet.advance (seed sourceHeap).1 count →
      guard.guard = .top ∧ (SourceCompactGuards.positive guard.guard).isSome = true
 := by
  have literalTop : ∀ guard ∈ alphabet (encodedLibrary lib), guard.guard = .top := by
    intro guard member
    simp only [alphabet, List.mem_cons, List.mem_append, List.mem_map] at member
    rcases member with rfl | rfl | rfl | ⟨_entry, _member, rfl⟩ | ⟨_entry, _member, rfl⟩
    all_goals rfl
  have derivedTop : ∀ guard,
      SourceEqualityConstraintOrigins.Derived (alphabet (encodedLibrary lib))
        SourceSynthesisGeneralizeSyntax.top SourceEqualityPCSNativeEdge.conjoin guard →
      guard.guard = .top := by
    intro guard origin
    induction origin with
    | literal member => exact literalTop _ member
    | top => rfl
    | conjunction first second firstTop secondTop =>
        dsimp only [SourceEqualityPCSNativeEdge.conjoin, SourceEqualityConstraintConstructors.conjoin]
        rw [firstTop, secondTop]
        simp [GuardConjunction.merge, GuardConjunction.normalize,
          GuardConjunction.atoms, GuardConjunction.canonical, GuardConjunction.conjoin]
  have mappedBuilt : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisProgramBuildRolesGeneric.mapSyntax SourceSynthesisLabelProgramBuildRoles.literal expression)
      [] empty = InternedNestedConstruction.Outcome.done rootValue sourceHeap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have origins := SourceSynthesisCurrentNativeGuardOrigins.constructed
    SourceSynthesisLabelProgramBuildRoles.literal lib query signed expression accepted
    rootValue sourceHeap mappedBuilt
  have verified := InternedFreshOrdinaryFacts.build_verified
    (ordinarySymbols expression) [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)
  have sourceFacts : Facts sourceHeap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have seedTop : ∀ guard ∈ (seed sourceHeap).1, guard.guard = .top := by
    intro guard member
    change guard ∈ (SourceRecursiveIntersectionSourceProfile.edgePayloads sourceHeap).map
      (fun edge => edge.entry.key.constraint) at member
    obtain ⟨edge, payload, same⟩ := List.mem_map.mp member
    obtain ⟨identity, _range, read⟩ := List.mem_filterMap.mp payload
    change (sourceHeap.edges.issued identity).bind sourceHeap.edgeRecords = some edge at read
    obtain ⟨key, _issued, stored⟩ := Option.bind_eq_some_iff.mp read
    have keySame := (sourceFacts.coherent.edges key edge stored).2.1
    rw [← same, keySame]
    exact derivedTop _ (origins key edge stored)
  intro count guard member
  exact native_guard_pool_advance_positive (seed sourceHeap).1 seedTop count guard member

end MicroCFTA.SourceSynthesisCurrentGuardPoolPositivity
