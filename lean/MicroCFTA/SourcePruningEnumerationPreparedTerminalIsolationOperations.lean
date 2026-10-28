import MicroCFTA.SourcePruningEnumerationIsolationReads
import MicroCFTA.SourcePruningEnumerationTerminalPrefixNeutral
import MicroCFTA.SourcePruningEnumerationDispatchShape
import MicroCFTA.SourcePruningEnumerationFoldCacheBounds
import MicroCFTA.SourcePruningEnumerationNativeReferences
import MicroCFTA.SourcePruningEnumerationIncomingCarriers

/-!
# Isolation through actual terminal operations

The prefix joins only the original listed classes.
The fold writes only its selected source and target slots.
The incoming action writes only its actual reached class.
No resource reservation or future endpoint premise is an input.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open EnumerationReferences EnumerationDischargeHistory
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard : Type}
attribute [local instance] terminalPrefixMonadList terminalPrefixLawfulMonadList

/-- The actual prefix retains an isolated class and selects other recorded slots. -/
theorem run_isolated
    (fuel held heldHandle : Nat) (first : Suspended) (rest : List Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (before after : State Symbol EnumGuard) (recorded : List Nat) (winner : Nat)
    (moved : EnumerationWaitingIndex.Waiting)
    (total : UnionFind.Total before.representatives)
    (isolated : IsolatedPending held heldHandle before)
    (avoids : Avoids before.representatives held (first :: rest))
    (success : Success (run fuel first rest waiting) before (recorded, winner, moved) after) :
    UnionFind.Total after.representatives ∧ IsolatedPending held heldHandle after ∧
      (∀ source ∈ recorded, source ≠ held) ∧
      ¬UnionFind.SameClass after.representatives held winner ∧
      (∀ uv, UnionFind.SameClass after.representatives held uv ↔
        UnionFind.SameClass before.representatives held uv) := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  have heldFixed := (root_iff before.representatives roots paths held).mp isolated.root
  unfold run at success
  obtain ⟨actualRecorded, scanned, preScan, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨scanValid, recordedSame⟩ := representatives_scan before.values roots fuel (first :: rest)
    before scanned actualRecorded ⟨rfl, paths⟩ preScan
  obtain ⟨ignored, united, unions, continued⟩ := (success_bind _ _ _ _ _).mp continued
  cases ignored
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united :=
    terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
      (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨actualWinner, resolved, resolution, final⟩ := (success_bind _ _ _ _ _).mp continued
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var
    actualWinner united resolved joined resolution
  obtain ⟨same, stateSame⟩ := (success_pure _ _ _ _).mp final
  have recordedEq : actualRecorded = recorded := congrArg Prod.fst same.symm
  have winnerEq : actualWinner = winner := congrArg (fun value => value.2.1) same.symm
  rw [recordedEq] at recordedSame
  subst actualRecorded actualWinner after
  have sameSelected (uv : Nat) : uv ∈ recorded ↔ uv ∈ selected := by
    rw [recordedSame, resolve_members roots rest [roots first.var] uv]
    simp [List.mem_map]
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  have notRecorded : held ∉ recorded := by
    intro member
    rw [recordedSame] at member
    obtain ⟨sc, present, named⟩ := List.mem_map.mp member
    exact avoids sc present ((class_iff before.representatives roots paths held sc.var).mpr
      (heldFixed.trans named.symm))
  have notSelected : held ∉ selected := fun member => notRecorded ((sameSelected held).mpr member)
  have heldRootResolved := (joined_root_set before.values roots selected resolved resolvedValid first.var
    winner count firstSelected path held).mpr ⟨heldFixed, Or.inl notSelected⟩
  have winnerRoot : IsRoot resolved.representatives winner := ⟨count, .root (UnionFind.reaches_terminal path)⟩
  have winnerFixed := resolvedValid.oldRoots winner winnerRoot
  have winnerSelected : winner ∈ selected := by
    rcases (resolvedValid.joined first.var winner).mp (UnionFind.sameClass_root path) with named | both
    · simpa [winnerFixed, named] using firstSelected
    · simpa [winnerFixed] using both.2
  have different : held ≠ winner := fun named => notSelected (by simpa [named] using winnerSelected)
  have classes : ∀ uv, UnionFind.SameClass resolved.representatives held uv ↔
      UnionFind.SameClass before.representatives held uv := by
    intro uv
    rw [resolvedValid.joined held uv, class_iff before.representatives roots paths held uv, heldFixed]
    simp [notSelected]
  refine ⟨resolvedValid.total, ⟨heldRootResolved, ?_, ?_⟩, ?_, ?_, classes⟩
  · rw [resolvedValid.values]
    exact isolated.stored
  · intro value member sc listed related
    exact isolated.incoming value (by simpa only [resolvedValid.values] using member) sc listed
      ((classes sc.var).mp related)
  · intro source member named
    exact notRecorded (by simpa only [named] using member)
  · intro related
    exact different ((UnionFind.sameClass_iff_roots heldRootResolved.choose_spec
      (.root (UnionFind.reaches_terminal path))).mp related)

end MicroCFTA.SourcePruningEnumerationTerminalPrefix

namespace MicroCFTA.SourcePruningEnumerationDispatch
open EnumerationState EnumerationCorrectness EnumerationDischargeHistory EnumerationReferences
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- An actual dispatcher singleton retains every different isolated slot. -/
theorem dispatch_isolated
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (source target : Nat) (queries : Queries) (action : EnumerateM Symbol EnumGuard Unit)
    (afterCaller : Caller width) (savedQueries : Queries) (after : EnumerationState.State Symbol EnumGuard)
    (held heldHandle : Nat) (isolated : IsolatedPending held heldHandle before)
    (sourceOther : source ≠ held) (targetOther : target ≠ held)
    (selected : dispatch checkEmpty nativeFuel p h beforeCaller before source target queries =
      (.ok (some action), afterCaller, savedQueries))
    (completed : ExceptT.run (action before) = [.ok ((), after)]) :
    IsolatedPending held heldHandle after ∧ after.representatives = before.representatives := by
  rcases SourcePruningEnumerationDispatchShape.singleton checkEmpty nativeFuel p h
    beforeCaller before source target queries action afterCaller savedQueries after selected completed with
    rfl | ⟨_different, sourceNode, targetNode, merged, sourceScs, targetScs, sourceStored, targetStored, rfl⟩
  · exact ⟨isolated, rfl⟩
  · refine ⟨⟨isolated.root, ?_, ?_⟩, rfl⟩
    · simpa only [assimilated, List.getElem?_set_ne sourceOther, List.getElem?_set_ne targetOther]
        using isolated.stored
    · exact SourcePruningEnumerationNativeReferences.assimilated_allowed
        (fun uv => ¬UnionFind.SameClass before.representatives held uv)
        before source target sourceNode targetNode merged sourceScs targetScs
        isolated.incoming sourceStored targetStored

end MicroCFTA.SourcePruningEnumerationDispatch


namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState EnumerationCorrectness EnumerationDischargeHistory
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}

/-- Every actual fold outcome retains the original different isolated slot and forest. -/
theorem run_isolated
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol EnumGuard)
    (target : Nat) (queries : Queries)
    (result : Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourceCurrentAllocatedConjunctionWorker.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol EnumGuard)))))
    (afterCaller : Caller width) (savedQueries : Queries)
    (after : EnumerationState.State Symbol EnumGuard)
    (held heldHandle : Nat) (proper : IsolatedPending held heldHandle before)
    (sourcesOther : ∀ source ∈ sources, source ≠ held) (targetOther : target ≠ held)
    (observed : run checkEmpty nativeFuel p h sources beforeCaller before target queries =
      (result, afterCaller, savedQueries, after)) : IsolatedPending held heldHandle after ∧ after.representatives = before.representatives := by
  induction sources generalizing beforeCaller before queries with
  | nil =>
      simp only [run, Prod.mk.injEq] at observed
      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨proper, rfl⟩
  | cons source rest ih =>
      rcases dispatchObserved : SourcePruningEnumerationDispatch.dispatch checkEmpty nativeFuel p h
        beforeCaller before source target queries with ⟨dispatchResult, reachedCaller, saved⟩
      cases dispatchResult with
      | error fault =>
          simp only [run, dispatchObserved, Prod.mk.injEq] at observed
          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨proper, rfl⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [run, dispatchObserved, Prod.mk.injEq] at observed
              rcases observed with ⟨rfl, rfl, rfl, rfl⟩
              exact ⟨proper, rfl⟩
          | some action =>
              cases rawObserved : ExceptT.run (action before) with
              | nil =>
                  simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                  rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                  exact ⟨proper, rfl⟩
              | cons head tail =>
                  cases head with
                  | error failure =>
                      simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                      rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                      exact ⟨proper, rfl⟩
                  | ok pair =>
                      rcases pair with ⟨ignored, middle⟩
                      cases ignored
                      cases tail with
                      | nil =>
                          have middleFacts := SourcePruningEnumerationDispatch.dispatch_isolated
                            checkEmpty nativeFuel p h beforeCaller before source target queries action
                            reachedCaller saved middle held heldHandle proper
                            (sourcesOther source (by simp)) targetOther dispatchObserved rawObserved
                          simp only [run, dispatchObserved, rawObserved] at observed
                          have finalFacts := ih reachedCaller middle saved middleFacts.1
                            (fun next member => sourcesOther next (List.mem_cons_of_mem source member)) observed
                          exact ⟨finalFacts.1, finalFacts.2.trans middleFacts.2⟩
                      | cons second remaining =>
                          simp only [run, dispatchObserved, rawObserved, Prod.mk.injEq] at observed
                          rcases observed with ⟨rfl, rfl, rfl, rfl⟩
                          exact ⟨proper, rfl⟩

end MicroCFTA.SourcePruningEnumerationFold
