import MicroCFTA.ObservationGraph
import MicroCFTA.SymbolicSelection

/-!
# Requested observations for imported automata

The adapter reuses the proved graph Cartesian product and alternative merge.
Every requested position reads a full symbol and leafness. Missing positions
have no map entry. Empty requests retain the original graph reference.
The graph view exposes the source binder and epsilon-union alternatives.
-/
namespace MicroCFTA.ImportObservations
open Language Observation ObservationGraph

/-- The child-request map keeps precisely the tails under its child index. -/
def childRequests (requested : List Path) (index : Nat) : List Path :=
  requested.filterMap fun target => match target with
    | [] => none
    | child :: rest => if child = index then some rest else none

theorem child_requests_exact (requested : List Path) (index : Nat) (rest : Path) :
    rest ∈ childRequests requested index ↔ index :: rest ∈ requested := by
  simp only [childRequests, List.mem_filterMap]
  constructor
  · rintro ⟨target, member, found⟩
    cases target with
    | nil => simp at found
    | cons child tail =>
        split at found <;> simp_all
  · intro member
    exact ⟨index :: rest, member, by simp⟩

/-- Build the trie read by the existing structural-specialization worker. -/
def requestPlan (requested : List Path) : Plan :=
  buildPlan (requested.map fun target => (target, Need.symbol))

theorem request_plan_exact (requested : List Path) (target : Path) :
    lookup (requestPlan requested) target = if target ∈ requested then some .symbol else none := by
  unfold requestPlan buildPlan
  rw [lookup_buildFrom, requestedAt_uniform, lookup_empty]
  simp [addNeed]

/-- A child lookup in the trie equals the source child-request map. -/
theorem child_request_plan (requested : List Path) (index : Nat) (rest : Path) :
    lookup (requestPlan requested) (index :: rest) =
      if rest ∈ childRequests requested index then some .symbol else none := by
  simp only [request_plan_exact, child_requests_exact]

/-- The extensional finite map returned by requested source observations. -/
def requestedView (requested : List Path) (term : Term (Label Symbol Refinement)) :
    Path → Option (Entry Symbol Refinement) :=
  fun target => if target ∈ requested then (term.atPath target).map (fun child => .symbol (rootObservation child)) else none

/-- The existing graph worker records exactly the source requested observation map. -/
theorem signature_requested (requested : List Path) (term : Term (Label Symbol Refinement)) :
    signature (requestPlan requested) term = requestedView requested term := by
  funext target
  rw [signature, readWith_correct, request_plan_exact]
  by_cases present : target ∈ requested <;> cases found : term.atPath target <;>
    simp [requestedView, present, signatureEntry, found]

/-- Requesting a nonexistent position does not invent an observation. -/
theorem absent_requested (requested : List Path) (term : Term (Label Symbol Refinement))
    (target : Path) (missing : term.atPath target = none) : requestedView requested term target = none := by
  simp [requestedView, missing]

/-- Prefix a child's observation map by its distinct argument index. -/
def prefixView (index : Nat) (view : Path → Option Value) : Path → Option Value
  | [] => none
  | child :: rest => if child = index then view rest else none

theorem prefix_exact (index : Nat) (view : Path → Option Value) (rest : Path) :
    prefixView index view (index :: rest) = view rest := by simp [prefixView]

/-- Child prefixes cannot overwrite one another in Map.fromList or Map.unions. -/
theorem prefix_disjoint (left right : Nat) (different : left ≠ right)
    (first second : Path → Option Value) (path : Path) :
    prefixView left first path = none ∨ prefixView right second path = none := by
  cases path with
  | nil => simp [prefixView]
  | cons index rest =>
      by_cases same : index = left
      · subst index; simp [prefixView, different]
      · simp [prefixView, same]

/-- Read the left-biased union of the source's indexed child maps. -/
def mergePrefixed (start : Nat) : List (Path → Option Value) → Path → Option Value
  | [], _ => none
  | first :: rest, path => (prefixView start first path).orElse (fun _ => mergePrefixed (start + 1) rest path)

theorem merge_prefixed_root (start : Nat) (children : List (Path → Option Value)) :
    mergePrefixed start children [] = none := by
  induction children generalizing start with
  | nil => rfl
  | cons first rest ih => simpa [mergePrefixed, prefixView] using ih (start + 1)

theorem merge_prefixed_before (start index : Nat) (before : index < start)
    (children : List (Path → Option Value)) (rest : Path) : mergePrefixed start children (index :: rest) = none := by
  induction children generalizing start with
  | nil => rfl
  | cons first children ih =>
      have different : index ≠ start := by omega
      simpa [mergePrefixed, prefixView, different] using ih (start + 1) (by omega)

/-- Map.unions of prefixed maps reads exactly the selected child's map. -/
theorem merge_prefixed_child (start index : Nat) (children : List (Path → Option Value)) (rest : Path) :
    mergePrefixed start children ((start + index) :: rest) = children[index]?.bind (fun child => child rest) := by
  induction children generalizing start index with
  | nil => simp [mergePrefixed]
  | cons first children ih =>
      cases index with
      | zero =>
          simp only [Nat.add_zero, mergePrefixed, prefix_exact, List.getElem?_cons_zero, Option.bind_some]
          rw [merge_prefixed_before (start + 1) start (by omega)]
          cases first rest <;> rfl
      | succ index =>
          have different : start + (index + 1) ≠ start := by omega
          simp only [mergePrefixed, prefixView, different, ↓reduceIte, Option.orElse_none, List.getElem?_cons_succ]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1) index

/-- The root map followed by the union of child maps, as in source Map.unions. -/
def mergedObservations (root : Value) (children : List (Path → Option Value)) : Path → Option Value :=
  fun path => (if path = [] then some root else none).orElse (fun _ => mergePrefixed 0 children path)

/-- The source completeObservations root and indexed child-map readback. -/
def completeObservations (root : Value) (children : List (Path → Option Value)) : Path → Option Value
  | [] => some root
  | index :: rest => children[index]?.bind (fun child => child rest)

/-- The concrete map union implements completeObservations with no overwrite between children. -/
theorem merged_observations_exact (root : Value) (children : List (Path → Option Value)) :
    mergedObservations root children = completeObservations root children := by
  funext path
  cases path with
  | nil => simp [mergedObservations, completeObservations]
  | cons index rest =>
      simpa [mergedObservations, completeObservations] using merge_prefixed_child 0 index children rest

/-- Parent observations retain the root and every requested existing descendant. -/
def parentObservations (requested : List Path) (root : Value) (children : List (Path → Option Value)) :
    Path → Option Value :=
  fun path => if path = [] ∨ path ∈ requested then completeObservations root children path else none

theorem complete_root (root : Value) (children : List (Path → Option Value)) :
    completeObservations root children [] = some root := rfl

theorem complete_child (root : Value) (children : List (Path → Option Value)) (index : Nat) (rest : Path) :
    completeObservations root children (index :: rest) = children[index]?.bind (fun child => child rest) := rfl

theorem parent_root (requested : List Path) (root : Value) (children : List (Path → Option Value)) :
    parentObservations requested root children [] = some root := by simp [parentObservations, completeObservations]

/-- Source splitByObservations, through the existing graph worker and its finite request budget. -/
def split [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State) :
    List (Variant State Symbol Refinement) :=
  if requested = [] then [originalVariant state]
  else specialize automaton (planBudget (requestPlan requested)) (requestPlan requested) state

theorem split_empty [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (state : State) :
    split automaton [] state = [originalVariant state] := by simp [split]

/-- The concrete empty-request branch and graph Cartesian split both retain the exact language. -/
theorem split_cover [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path)
    (state : State) (term : Term (Label Symbol Refinement)) :
    (∃ part ∈ split automaton requested state, AcceptsNode automaton part.node term) ↔ Accepts automaton state term := by
  by_cases empty : requested = []
  · subst requested
    simp [split, originalVariant, original_accepts_iff]
  · simpa [split, empty] using specialize_cover automaton (planBudget (requestPlan requested)) (requestPlan requested) state term

/-- Every emitted part has exactly the observations of each term it accepts. -/
theorem split_view [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path)
    (state : State) (part : Variant State Symbol Refinement) (member : part ∈ split automaton requested state)
    (term : Term (Label Symbol Refinement)) (accepted : AcceptsNode automaton part.node term) :
    part.view = requestedView requested term := by
  by_cases empty : requested = []
  · subst requested
    have same : part = originalVariant state := by simpa [split] using member
    subst part
    funext path
    simp [originalVariant, requestedView]
  · rw [←signature_requested]
    exact (specialize_exact automaton (requestPlan requested) state part (by simpa [split, empty] using member) term accepted).2

/-- The finite comparison key is an injective encoding of a supported sparse observation map. -/
def key (requested : List Path) (view : Path → Option (Entry Symbol Refinement)) :
    List (Option (Entry Symbol Refinement)) := viewKey (requestPlan requested) view

/-- Distinct observation keys cannot describe the same accepted term. -/
theorem distinct_keys_disjoint [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (left right : Variant State Symbol Refinement)
    (leftMember : left ∈ split automaton requested state) (rightMember : right ∈ split automaton requested state)
    (different : key requested left.view ≠ key requested right.view) (term : Term (Label Symbol Refinement)) :
    ¬(AcceptsNode automaton left.node term ∧ AcceptsNode automaton right.node term) := by
  rintro ⟨inLeft, inRight⟩
  exact different (congrArg (key requested)
    ((split_view automaton requested state left leftMember term inLeft).trans
      (split_view automaton requested state right rightMember term inRight).symm))

/-- Every accepted term appears in a part with its own requested observation key. -/
theorem split_complete [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (term : Term (Label Symbol Refinement)) (accepted : Accepts automaton state term) :
    ∃ part ∈ split automaton requested state, AcceptsNode automaton part.node term ∧
      key requested part.view = key requested (requestedView requested term) := by
  obtain ⟨part, member, inside⟩ := (split_cover automaton requested state term).mpr accepted
  exact ⟨part, member, inside, congrArg (key requested) (split_view automaton requested state part member term inside)⟩

/-- Merging all candidates with a key keeps that exact key in the representative view. -/
theorem merged_key [DecidableEq Symbol] [DecidableEq Refinement]
    (plan : Plan) (candidates : List (Candidate State Symbol Refinement))
    (wanted : List (Option (Entry Symbol Refinement)))
    (present : wanted ∈ (candidates.map fun candidate => viewKey plan candidate.view).eraseDups) :
    viewKey plan (groupedVariant (candidates.filter fun candidate => decide (viewKey plan candidate.view = wanted))).view = wanted := by
  obtain ⟨witness, member, same⟩ := List.mem_map.mp (List.mem_eraseDups.mp present)
  have included : witness ∈ candidates.filter (fun candidate => decide (viewKey plan candidate.view = wanted)) :=
    List.mem_filter.mpr ⟨member, by simpa using same⟩
  cases filtered : candidates.filter (fun candidate => decide (viewKey plan candidate.view = wanted)) with
  | nil => simp [filtered] at included
  | cons first rest =>
      have firstMember : first ∈ candidates.filter (fun candidate => decide (viewKey plan candidate.view = wanted)) := by
        rw [filtered]; simp
      have keySame : viewKey plan first.view = wanted := by simpa using (List.mem_filter.mp firstMember).2
      simpa [groupedVariant, filtered] using keySame

/-- The actual merge emits one key for each first occurrence and no duplicate key. -/
theorem merged_keys [DecidableEq Symbol] [DecidableEq Refinement]
    (plan : Plan) (candidates : List (Candidate State Symbol Refinement)) :
    (groupCandidates plan candidates).map (fun part => viewKey plan part.view) =
      (candidates.map fun candidate => viewKey plan candidate.view).eraseDups := by
  calc
    _ = ((candidates.map fun candidate => viewKey plan candidate.view).eraseDups).map id := by
      simp only [groupCandidates, List.map_map]
      apply List.map_congr_left
      intro wanted member
      exact merged_key plan candidates wanted member
    _ = _ := by simp

theorem merged_keys_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (plan : Plan) (candidates : List (Candidate State Symbol Refinement)) :
    ((groupCandidates plan candidates).map fun part => viewKey plan part.view).Nodup := by
  rw [merged_keys]
  exact SymbolicDriver.eraseDups_nodup _

/-- The source import split has no repeated observation key. -/
theorem split_keys_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State) :
    ((split automaton requested state).map fun part => key requested part.view).Nodup := by
  by_cases empty : requested = []
  · simp [split, empty]
  · simp only [split, empty, ↓reduceIte, key, planBudget, specialize]
    exact merged_keys_nodup _ _

/-- Sorting the parts cannot change key uniqueness or introduce overlapping groups. -/
theorem reordered_keys_nodup [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (ordered : List (Variant State Symbol Refinement))
    (permutation : ordered.Perm (split automaton requested state)) :
    (ordered.map fun part => key requested part.view).Nodup :=
  (permutation.map _).nodup_iff.mpr (split_keys_nodup automaton requested state)

/-- A merged imported part is identified by its complete requested observation key. -/
def GroupLanguage [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (wanted : List (Option (Entry Symbol Refinement))) (term : Term (Label Symbol Refinement)) : Prop :=
  ∃ part ∈ split automaton requested state, key requested part.view = wanted ∧ AcceptsNode automaton part.node term

/-- Each group contains all and only source terms with its observation key. -/
theorem group_language_exact [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (wanted : List (Option (Entry Symbol Refinement))) (term : Term (Label Symbol Refinement)) :
    GroupLanguage automaton requested state wanted term ↔
      Accepts automaton state term ∧ wanted = key requested (requestedView requested term) := by
  constructor
  · rintro ⟨part, member, same, accepted⟩
    exact ⟨(split_cover automaton requested state term).mp ⟨part, member, accepted⟩,
      same.symm.trans (congrArg (key requested) (split_view automaton requested state part member term accepted))⟩
  · rintro ⟨accepted, rfl⟩
    obtain ⟨part, member, inside, same⟩ := split_complete automaton requested state term accepted
    exact ⟨part, member, same, inside⟩

/-- Exact local decoders compose without losing an imported source term. -/
theorem decoder_cover [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (decode : List (Option (Entry Symbol Refinement)) → Nat → Option (Term (Label Symbol Refinement)))
    (each : ∀ wanted term, (∃ rank, decode wanted rank = some term) ↔
      GroupLanguage automaton requested state wanted term)
    (term : Term (Label Symbol Refinement)) :
    (∃ wanted rank, decode wanted rank = some term) ↔ Accepts automaton state term := by
  constructor
  · rintro ⟨wanted, rank, decoded⟩
    exact ((group_language_exact automaton requested state wanted term).mp ((each wanted term).mp ⟨rank, decoded⟩)).1
  · intro accepted
    exact ⟨_, (each _ term).mpr ((group_language_exact automaton requested state _ term).mpr ⟨accepted, rfl⟩)⟩

/-- Local distinct-term ranks cannot collide across separately keyed import groups. -/
theorem decoder_injective [DecidableEq Symbol] [DecidableEq Refinement]
    (automaton : Automaton State (Label Symbol Refinement)) (requested : List Path) (state : State)
    (decode : List (Option (Entry Symbol Refinement)) → Nat → Option (Term (Label Symbol Refinement)))
    (sound : ∀ wanted rank term, decode wanted rank = some term → GroupLanguage automaton requested state wanted term)
    (distinct : ∀ wanted left right term, decode wanted left = some term → decode wanted right = some term → left = right)
    (first second : List (Option (Entry Symbol Refinement))) (left right : Nat) (term : Term (Label Symbol Refinement))
    (a : decode first left = some term) (b : decode second right = some term) : first = second ∧ left = right := by
  have one := ((group_language_exact automaton requested state first term).mp (sound first left term a)).2
  have two := ((group_language_exact automaton requested state second term).mp (sound second right term b)).2
  have same : first = second := one.trans two.symm
  exact ⟨same, distinct first left right term a (by simpa only [←same] using b)⟩

/-- A request below a leaf remains absent, including its unrequested root. -/
example : requestedView [[0]] (.node (⟨"a", ()⟩ : Label String Unit) []) [] = none ∧
    requestedView [[0]] (.node (⟨"a", ()⟩ : Label String Unit) []) [0] = none := by decide +kernel

/-- A missing request still produces the existing leaf's part with an empty observation map. -/
example : (split (fun (_ : Unit) => [⟨(⟨"a", ()⟩ : Label String Unit), [], fun _ => true⟩]) [[0]] ()).length = 1 := by
  decide +kernel

end MicroCFTA.ImportObservations
