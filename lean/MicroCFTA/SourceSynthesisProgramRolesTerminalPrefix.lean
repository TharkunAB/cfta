import MicroCFTA.SourceSynthesisProgramEnumerationRoles
import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.EnumerationDriver

/-!
# Program roles at the actual terminal prefix endpoint

The prefix changes only the representative forest. Its bucket avoids each
marked Program class. Those roots retain their raw payloads and classes.
Payload assimilation follows this intermediate endpoint.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesTerminalPrefix
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationReferences InternedConstructorTemplates
open SourceSynthesisProgramEnumerationRoles
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Waiting" => EnumerationWaitingIndex.Waiting
variable {valid : Constraint → Prop} {literal : String → Symbol}

local instance prefixRolesMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance prefixRolesLawfulMonadList : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

private theorem prefix_effects
    (fuel : Nat) (first : Suspended) (rest : List Suspended) (waiting moved : Waiting)
    (before after : Core) (recorded : List Nat) (winner : Nat)
    (total : UnionFind.Total before.representatives)
    (actual : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) :
    after = {before with representatives := after.representatives} ∧
      ∀ held, IsRoot before.representatives held → Avoids before.representatives held (first :: rest) →
        EnumerationDriver.Protected held before after ∧
          ¬UnionFind.SameClass after.representatives held winner ∧ held ∉ recorded := by
  obtain ⟨roots, paths⟩ := roots_exist before.representatives total
  unfold SourcePruningEnumerationTerminalPrefix.run at actual
  obtain ⟨visited, scanned, scan, afterScan⟩ := (success_bind _ _ _ _ _).mp actual
  obtain ⟨discarded, united, unions, afterUnions⟩ := (success_bind _ _ _ _ _).mp afterScan
  cases discarded
  obtain ⟨computedWinner, resolved, resolution, finalPure⟩ := (success_bind _ _ _ _ _).mp afterUnions
  obtain ⟨returnedSame, afterSame⟩ := (success_pure _ _ _ _).mp finalPure
  have recordedSame : recorded = visited := congrArg (fun result : List Nat × Nat × Waiting => result.1) returnedSame
  have winnerSame : winner = computedWinner := congrArg (fun result : List Nat × Nat × Waiting => result.2.1) returnedSame
  subst recorded winner after
  obtain ⟨scanValid, idsSame⟩ := representatives_scan before.values roots fuel (first :: rest) before scanned visited ⟨rfl, paths⟩ scan
  let selected := rest.foldl (fun selected sc => roots sc.var :: selected) [roots first.var]
  have joined : Merging before.values roots selected united :=
    terminal_unions before.values roots [roots first.var] fuel first.var rest scanned united
      (merging_initial before.values roots scanned first.var scanValid) (by simp) unions
  obtain ⟨resolvedValid, count, path⟩ := merging_representative before.values roots selected fuel first.var computedWinner united resolved joined resolution
  have scanFrame : scanned = {before with representatives := scanned.representatives} := by
    apply mapM_invariant (fun (sc : Suspended) => representative fuel sc.var)
      (fun current => current = {before with representatives := current.representatives})
      (first :: rest) ?_ before scanned visited rfl scan
    intro sc _member current root next previous step
    obtain ⟨found, _lookup, _rootSame, nextSame⟩ := (representative_success fuel sc.var current next root).mp step
    rw [nextSame]
    exact congrArg (fun state : Core => {state with representatives := found.forest}) previous
  have unionFrame : united = {before with representatives := united.representatives} := by
    apply forM_invariant (fun (sc : Suspended) => unionVariables fuel first.var sc.var)
      (fun current => current = {before with representatives := current.representatives})
      rest ?_ scanned united scanFrame unions
    intro sc _member current next previous step
    obtain ⟨forest, _lookup, nextSame⟩ := (unionVariables_success fuel first.var sc.var current next).mp step
    rw [nextSame]
    exact congrArg (fun state : Core => {state with representatives := forest}) previous
  have shape : resolved = {before with representatives := resolved.representatives} := by
    obtain ⟨found, _lookup, _rootSame, finalSame⟩ := (representative_success fuel first.var united resolved computedWinner).mp resolution
    rw [finalSame]
    exact congrArg (fun state : Core => {state with representatives := found.forest}) unionFrame
  have sameSelected (uv : Nat) : uv ∈ visited ↔ uv ∈ selected := by
    rw [idsSame, resolve_members roots rest [roots first.var] uv]
    simp [List.mem_map]
  have firstSelected : roots first.var ∈ selected :=
    (resolve_members roots rest [roots first.var] (roots first.var)).mpr (Or.inl (by simp))
  refine ⟨shape, ?_⟩
  intro held heldRoot separate
  have heldFixed := (root_iff before.representatives roots paths held).mp heldRoot
  have notRecorded : held ∉ visited := by
    intro member
    rw [idsSame] at member
    obtain ⟨sc, present, same⟩ := List.mem_map.mp member
    exact separate sc present ((class_iff before.representatives roots paths held sc.var).mpr (heldFixed.trans same.symm))
  have notSelected : held ∉ selected := fun member => notRecorded ((sameSelected held).mpr member)
  have heldRootAfter := (joined_root_set before.values roots selected resolved resolvedValid first.var computedWinner count firstSelected path held).mpr ⟨heldFixed, Or.inl notSelected⟩
  have classes : ∀ uv, UnionFind.SameClass resolved.representatives held uv ↔ UnionFind.SameClass before.representatives held uv := by
    intro uv
    rw [resolvedValid.joined held uv, class_iff before.representatives roots paths held uv, heldFixed]
    simp [notSelected]
  have notWinner : ¬UnionFind.SameClass resolved.representatives held computedWinner := by
    intro same
    have firstSame := UnionFind.sameClass_trans same (UnionFind.sameClass_symm (UnionFind.sameClass_root path))
    exact separate first (by simp) ((classes first.var).mp firstSame)
  have valueFrame := congrArg (fun state : Core => state.values[held]?) shape
  exact ⟨⟨valueFrame, heldRootAfter, classes⟩, notWinner, notRecorded⟩

/-- The same terminal prefix retains every marked Program root and its complete class. -/
theorem terminal_prefix_program_slots
    (heap : NativeHeap) (fuel : Nat) (first : Suspended) (rest : List Suspended)
    (waiting moved : Waiting) (before after : Core) (recorded : List Nat) (winner : Nat)
    (marked : Nat → Prop) (safe : Safe before)
    (roles : ProgramSlots valid literal heap before marked)
    (avoids : ∀ uv, marked uv → Avoids before.representatives uv (first :: rest))
    (actual : Success (SourcePruningEnumerationTerminalPrefix.run fuel first rest waiting)
      before (recorded, winner, moved) after) :
    after = {before with representatives := after.representatives} ∧
      ProgramSlots valid literal heap after marked ∧
      ∀ uv, marked uv → EnumerationDriver.Protected uv before after ∧
        ¬UnionFind.SameClass after.representatives uv winner ∧ uv ∉ recorded := by
  obtain ⟨shape, preserved⟩ := prefix_effects fuel first rest waiting moved before after recorded winner safe.1.total actual
  have protects : ∀ uv, marked uv → EnumerationDriver.Protected uv before after :=
    fun uv known => (preserved uv (roles.roots uv known) (avoids uv known)).1
  have counterSame : after.counter = before.counter := by
    have projected := congrArg (fun state : Core => state.counter) shape
    exact projected
  have valuesSame : after.values = before.values := by
    have projected := congrArg (fun state : Core => state.values) shape
    exact projected
  refine ⟨shape, ?_, fun uv known => preserved uv (roles.roots uv known) (avoids uv known)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro uv known
    rw [counterSame]
    exact roles.bounded uv known
  · intro uv known
    exact (protects uv known).root
  · intro uv known payload member sc listed same
    have old : payload ∈ before.values := by
      rw [← valuesSame]
      exact member
    exact roles.incoming uv known payload old sc listed (((protects uv known).classes sc.var).mp same)
  · intro uv known
    obtain ⟨payload, stored, role⟩ := roles.stored uv known
    exact ⟨payload, (protects uv known).value.trans stored, role⟩

end MicroCFTA.SourceSynthesisProgramRolesTerminalPrefix
