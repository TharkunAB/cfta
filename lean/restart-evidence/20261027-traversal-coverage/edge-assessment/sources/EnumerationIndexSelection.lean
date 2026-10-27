import MicroCFTA.EnumerationExpandableIndex
import MicroCFTA.EnumerationExecution

/-!
# Indexed scheduling selects exactly the old slot scan

The new fold resolves each raw key of the waiting map. Its order and
multiplicity can differ from the old suspended-reference fold. Successful
lookups preserve the representative map, so both folds block the same
representatives. Candidate order and the three-way result are retained.
-/
namespace MicroCFTA.EnumerationIndexSelection
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationExpandableIndex
open EnumerationExecution

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
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

/-- The increasing finite view of the cached expandable set uses the allocated slot domain. -/
def candidates (state : Cached Symbol Guard) : List Nat :=
  (List.range state.core.counter).filter state.expandable

/-- The finite map's key enumeration contains exactly its stored entries. -/
def WaitingKeys (state : Cached Symbol Guard) (keys : List Nat) : Prop :=
  ∀ uv, uv ∈ keys ↔ state.waiting uv ≠ none

/-- The new source fold resolves a raw waiting-map key. -/
def resolveKey (fuel : Nat) (blocked : List Nat) (uv : Nat) : EnumerateM Symbol Guard (List Nat) :=
  resolve fuel blocked ⟨.terminal, uv⟩

/-- Indexed scheduling traverses only the waiting keys before it subtracts blocked representatives. -/
def findIndexed (fuel : Nat) (candidates keys : List Nat) : EnumerateM Symbol Guard (Option (List Nat)) := do
  let blocked ← keys.foldlM (resolveKey fuel) []
  finishScan (candidates, blocked)

/-- Each actual indexed lookup returns the same canonical representative as the old slot fold. -/
theorem resolveKey_scan (values : List (UVarValue Symbol)) (roots : Nat → Nat)
    (fuel : Nat) (blocked result : List Nat) (uv : Nat) (before after : State Symbol Guard)
    (valid : ScanValid values roots before) (success : Success (resolveKey fuel blocked uv) before result after) :
    ScanValid values roots after ∧ result = roots uv :: blocked :=
  resolve_scan values roots fuel blocked result ⟨.terminal, uv⟩ before after valid success

/-- The actual indexed fold preserves representative meanings and computes its exact pure selection. -/
theorem findIndexed_exact (fuel : Nat) (candidates keys : List Nat) (roots : Nat → Nat)
    (before after : State Symbol Guard) (result : Option (List Nat))
    (paths : Roots before.representatives roots) (success : Success (findIndexed fuel candidates keys) before result after) :
    ScanValid before.values roots after ∧
      result = offered candidates (keys.foldl (fun blocked uv => roots uv :: blocked) []) := by
  unfold findIndexed at success
  obtain ⟨blocked, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨valid, rfl⟩ := foldlM_exact (resolveKey fuel) (fun blocked uv => roots uv :: blocked)
    (ScanValid before.values roots)
    (fun blocked uv before result after valid done => resolveKey_scan _ roots fuel blocked result uv before after valid done)
    keys [] blocked before middle ⟨rfl, paths⟩ traversed
  obtain ⟨rfl, rfl⟩ := (finishScan_success _ middle after result).mp finished
  exact ⟨valid, rfl⟩

/-- Candidate collection preserves the increasing order of slot indices. -/
theorem candidate_fold (graph : Graph Symbol Guard) (roots : Nat → Nat)
    (entries : List (UVarValue Symbol × Nat)) (accumulator : List Nat × List Nat) :
    (entries.foldl (collectPure graph roots) accumulator).1 =
      accumulator.1 ++ (entries.filter (fun entry => candidate graph entry.1)).map Prod.snd := by
  induction entries generalizing accumulator with
  | nil => simp
  | cons entry rest ih =>
      rw [List.foldl_cons, ih]
      have step : (collectPure graph roots accumulator entry).1 =
          if candidate graph entry.1 then accumulator.1 ++ [entry.2] else accumulator.1 := by
        rcases entry with ⟨value, index⟩
        cases value <;> simp [collectPure, candidate]
      rw [step]
      cases chosen : candidate graph entry.1 <;> simp [chosen, List.append_assoc]

/-- The maintained expandable set has the exact increasing list produced by the old slot scan. -/
theorem candidates_exact (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (correct : Correct graph state)
    (roots : Nat → Nat) :
    candidates state = (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).1 := by
  rw [candidate_fold]
  simp only [List.nil_append]
  unfold candidates
  rw [correct.aligned, List.range_eq_range', ← List.zipIdx_map_snd 0 state.core.values, List.filter_map]
  congr 1
  apply List.filter_congr
  intro entry member
  have stored := List.mem_zipIdx_iff_getElem?.mp member
  simp only [Function.comp_def, correct.expandable, stored, Option.map_some, Option.getD_some]

/-- The raw waiting-key fold blocks exactly the representatives of its listed keys. -/
theorem key_blocked (roots : Nat → Nat) (keys blocked : List Nat) (uv : Nat) :
    uv ∈ keys.foldl (fun blocked key => roots key :: blocked) blocked ↔
      uv ∈ blocked ∨ ∃ key ∈ keys, roots key = uv := by
  induction keys generalizing blocked with
  | nil => simp
  | cons key rest ih =>
      simp only [List.foldl_cons, ih, List.mem_cons]
      clear ih
      grind only

/-- The slot scan blocks exactly the representatives of suspended raw references. -/
theorem scan_blocked (graph : Graph Symbol Guard) (roots : Nat → Nat) (values : List (UVarValue Symbol)) (uv : Nat) :
    uv ∈ (values.zipIdx.foldl (collectPure graph roots) ([], [])).2 ↔
      ∃ value ∈ values, ∃ sc ∈ references value, roots sc.var = uv := by
  rw [blocked_exact]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨entry, member, sc, present, same⟩
    exact ⟨entry.1, List.fst_mem_of_mem_zipIdx member, sc, present, same⟩
  · rintro ⟨value, member, sc, present, same⟩
    obtain ⟨index, stored⟩ := List.mem_iff_getElem?.mp member
    exact ⟨(value, index), List.mk_mem_zipIdx_iff_getElem?.mpr stored, sc, present, same⟩

/-- The cached count support and old suspended scan block exactly the same representatives. -/
theorem blocked_exact (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (correct : Correct graph state)
    (keys : List Nat) (keyView : WaitingKeys state keys) (roots : Nat → Nat) (uv : Nat) :
    uv ∈ keys.foldl (fun blocked key => roots key :: blocked) [] ↔
      uv ∈ (state.core.values.zipIdx.foldl (collectPure graph roots) ([], [])).2 := by
  rw [key_blocked, scan_blocked]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨key, member, same⟩
    obtain ⟨value, stored, sc, present, named⟩ :=
      (EnumerationWaitingIndex.support_exact _ _ correct.waiting key).mp ((keyView key).mp member)
    exact ⟨value, stored, sc, present, named ▸ same⟩
  · rintro ⟨value, stored, sc, present, same⟩
    exact ⟨sc.var, (keyView sc.var).mpr
      ((EnumerationWaitingIndex.support_exact _ _ correct.waiting sc.var).mpr ⟨value, stored, sc, present, rfl⟩), same⟩

/-- Equal blocked memberships preserve the exact offered list, including the empty-work distinction. -/
theorem offered_congr (candidates first second : List Nat) (same : ∀ uv, uv ∈ first ↔ uv ∈ second) :
    offered candidates first = offered candidates second := by
  unfold offered
  split
  · rfl
  · congr 1
    apply List.filter_congr
    intro uv _
    simp only [same uv]

/-- Any reachable indexed state gives exactly the old scheduler's result under the actual representative lookups. -/
theorem selection_exact (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (reached : Reachable graph state)
    (keys : List Nat) (keyView : WaitingKeys state keys) (fuel : Nat) (roots : Nat → Nat)
    (paths : Roots state.core.representatives roots) (oldAfter newAfter : State Symbol Guard)
    (oldResult newResult : Option (List Nat))
    (oldDone : Success (findExpandable graph fuel) state.core oldResult oldAfter)
    (newDone : Success (findIndexed fuel (candidates state) keys) state.core newResult newAfter) :
    oldResult = newResult ∧ Roots oldAfter.representatives roots ∧ Roots newAfter.representatives roots := by
  have correct := reached.correct
  obtain ⟨oldValid, oldSame⟩ := findExpandable_exact graph fuel roots state.core oldAfter oldResult paths oldDone
  obtain ⟨newValid, newSame⟩ := findIndexed_exact fuel (candidates state) keys roots state.core newAfter newResult paths newDone
  refine ⟨?_, oldValid.roots, newValid.roots⟩
  rw [oldSame, newSame, candidates_exact graph state correct roots]
  exact offered_congr _ _ _ (fun uv => (blocked_exact graph state correct keys keyView roots uv).symm)

/-- A finite reference representation supplies the sparse map's complete key set without an index premise. -/
def referenceKeys (state : Cached Symbol Guard) : List Nat :=
  (state.core.values.flatMap fun value => (references value).map EqualityTrie.Suspended.var).eraseDups

/-- Reachable mutation history derives completeness of the finite map-key view. -/
theorem referenceKeys_correct (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (reached : Reachable graph state) :
    WaitingKeys state (referenceKeys state) := by
  intro uv
  rw [EnumerationWaitingIndex.support_exact _ _ reached.correct.waiting uv]
  simp [referenceKeys]

/-- Extra representative fuel retains every successful indexed scan and its compressed state. -/
theorem findIndexed_moreFuel (fuel extra : Nat) (candidates keys : List Nat) :
    Retains (findIndexed (Symbol := Symbol) (Guard := Guard) fuel candidates keys)
      (findIndexed (fuel + extra) candidates keys) := by
  unfold findIndexed
  exact retains_bind _ _ _ _ (retains_foldlM _ _
    (fun blocked uv => resolve_moreFuel fuel extra blocked ⟨.terminal, uv⟩) keys []) (fun _ => retains_refl _)

/-- The indexed resolver terminates for any finite map-key enumeration and total forest. -/
theorem findIndexed_terminates (before : State Symbol Guard) (total : UnionFind.Total before.representatives)
    (candidates keys : List Nat) :
    ∃ fuel result after, Success (findIndexed fuel candidates keys) before result after := by
  obtain ⟨fuel, blocked, after, traversed, _⟩ := foldlM_terminates resolveKey
    (fun state : State Symbol Guard => UnionFind.Total state.representatives)
    (fun fuel extra blocked uv => resolve_moreFuel fuel extra blocked ⟨.terminal, uv⟩)
    (fun blocked uv state valid => resolve_terminates state valid blocked ⟨.terminal, uv⟩) keys [] before total
  refine ⟨fuel, offered candidates blocked, after, ?_⟩
  exact (success_bind _ _ _ _ _).mpr ⟨blocked, after, traversed, (finishScan_success _ _ _ _).mpr ⟨rfl, rfl⟩⟩

/-- Both source scheduling strategies complete at one finite bound and return the same exact three-way selection. -/
theorem selection_complete (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (reached : Reachable graph state)
    (keys : List Nat) (keyView : WaitingKeys state keys) (total : UnionFind.Total state.core.representatives) :
    ∃ fuel result oldAfter newAfter,
      Success (findExpandable graph fuel) state.core result oldAfter ∧
      Success (findIndexed fuel (candidates state) keys) state.core result newAfter ∧
      ∀ roots, Roots state.core.representatives roots →
        Roots oldAfter.representatives roots ∧ Roots newAfter.representatives roots := by
  obtain ⟨oldFuel, oldResult, oldAfter, oldDone⟩ := findExpandable_terminates graph state.core total
  obtain ⟨newFuel, newResult, newAfter, newDone⟩ := findIndexed_terminates state.core total (candidates state) keys
  have oldMore := findExpandable_moreFuel graph oldFuel newFuel state.core oldResult oldAfter oldDone
  have newMore : Success (findIndexed (oldFuel + newFuel) (candidates state) keys) state.core newResult newAfter := by
    simpa only [Nat.add_comm] using findIndexed_moreFuel newFuel oldFuel (candidates state) keys state.core newResult newAfter newDone
  obtain ⟨roots, paths⟩ := roots_exist state.core.representatives total
  have same := (selection_exact graph state reached keys keyView _ roots paths oldAfter newAfter oldResult newResult oldMore newMore).1
  subst newResult
  refine ⟨oldFuel + newFuel, oldResult, oldAfter, newAfter, oldMore, newMore, ?_⟩
  intro actual actualPaths
  exact (selection_exact graph state reached keys keyView _ actual actualPaths oldAfter newAfter oldResult oldResult oldMore newMore).2

/-- The concrete finite index views obtain exact selection equivalence from mutation history, without a cached-invariant assumption. -/
theorem reachable_selection (graph : Graph Symbol Guard) (state : Cached Symbol Guard) (reached : Reachable graph state)
    (total : UnionFind.Total state.core.representatives) :
    ∃ fuel result oldAfter newAfter,
      Success (findExpandable graph fuel) state.core result oldAfter ∧
      Success (findIndexed fuel (candidates state) (referenceKeys state)) state.core result newAfter := by
  obtain ⟨fuel, result, oldAfter, newAfter, oldDone, newDone, _⟩ :=
    selection_complete graph state reached (referenceKeys state) (referenceKeys_correct graph state reached) total
  exact ⟨fuel, result, oldAfter, newAfter, oldDone, newDone⟩

end MicroCFTA.EnumerationIndexSelection
