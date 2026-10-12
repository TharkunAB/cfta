import MicroCFTA.MinimizeSchedule
import MicroCFTA.SymbolicSelection

/-!
# Indexed minimization copies

The parent index can retain stale entries. It must contain every actual
parent. Copying only indexed rows then gives the same ordered rows as the
complete table traversal. Root representative insertion adds child links.
-/
namespace MicroCFTA.MinimizeParentIndex
open MinimizeSchedule

/-- The new source copies only changed transitions that are not already present. -/
def copy (source destination : Nat) (transitions : List Transition) : List Transition :=
  transitions ++ (((transitions.filter fun edge => source ∈ edge.children).map
    (redirectTransition source destination)).filter (fun edge => edge ∉ transitions)).eraseDups

/-- A transition outside the affected set is unchanged by the redirect. -/
theorem redirect_absent (source destination : Nat) (edge : Transition)
    (absent : source ∉ edge.children) : redirectTransition source destination edge = edge := by
  cases edge with
  | mk symbol refinement children constraint =>
      simp only [redirectTransition, Transition.mk.injEq, true_and, and_true]
      calc
        _ = children.map id := by
          apply List.map_congr_left
          intro child present
          have different : child ≠ source := by intro same; subst child; exact absent present
          simp [different]
        _ = children := List.map_id children

/-- Filtering unchanged copies before deduplication removes exactly existing rows. -/
theorem copies_filter (source destination : Nat) (original remaining : List Transition)
    (subset : ∀ edge ∈ remaining, edge ∈ original) :
    (((remaining.filter fun edge => source ∈ edge.children).map (redirectTransition source destination)).filter
      (fun edge => edge ∉ original)) =
    ((remaining.map (redirectTransition source destination)).removeAll original) := by
  induction remaining with
  | nil => rfl
  | cons edge rest ih =>
      have later := ih (fun next member => subset next (by simp [member]))
      simp only [List.filter_cons, List.map_cons, List.removeAll, List.filter_cons] at *
      by_cases affected : source ∈ edge.children
      · by_cases present : redirectTransition source destination edge ∈ original
        · simpa [affected, present] using later
        · simpa [affected, present] using congrArg (redirectTransition source destination edge :: ·) later
      · have same := redirect_absent source destination edge affected
        have present := subset edge (by simp)
        simpa [affected, same, present] using later

/-- Deduplication preserves a list with distinct entries. -/
theorem dedup_identity (transitions : List Transition) (distinct : transitions.Nodup) :
    transitions.eraseDups = transitions := by
  induction transitions with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨absent, tail⟩ := List.nodup_cons.mp distinct
      rw [List.eraseDups_cons]
      have kept : rest.filter (fun edge => !edge == first) = rest := by
        apply List.filter_eq_self.mpr
        intro edge member
        have different : edge ≠ first := by intro same; subst edge; exact absent member
        simpa using different
      rw [kept, ih tail]

/-- On distinct source rows the optimized copy preserves exact order and contents. -/
theorem copy_exact (source destination : Nat) (transitions : List Transition)
    (distinct : transitions.Nodup) :
    copy source destination transitions = copyAlternatives (source, destination) transitions := by
  rw [copyAlternatives, List.eraseDups_append]
  have dedup : transitions.eraseDups = transitions := by
    exact dedup_identity transitions distinct
  rw [dedup, copy, copies_filter source destination transitions transitions (fun _ member => member)]

/-- The finite source set sorts distinct parent state names. -/
theorem stateSet_distinct (states : List Nat) : (stateSet states).Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (SymbolicDriver.eraseDups_nodup states)

/-- Every copied row remains distinct, so the optimization can be repeated. -/
theorem copy_distinct (source destination : Nat) (transitions : List Transition)
    (distinct : transitions.Nodup) : (copy source destination transitions).Nodup := by
  rw [copy_exact source destination transitions distinct]
  exact SymbolicDriver.eraseDups_nodup _

/-- The index maps a child state to its finite sorted parent set. -/
abbrev Index := Nat → List Nat

/-- Stale parents are permitted. Every actual child link must have its parent. -/
def Complete (rows : Rows) (parents : Index) : Prop :=
  ∀ state transitions, (state, transitions) ∈ rows → ∀ edge ∈ transitions, ∀ child ∈ edge.children,
    state ∈ parents child

/-- Construct the source parent index from every transition child. -/
def initialParents (rows : Rows) : Index := fun child =>
  stateSet (rows.filterMap fun (state, transitions) =>
    if transitions.any (fun edge => child ∈ edge.children) then some state else none)

/-- The initial parent index includes every actual child link. -/
theorem initialParents_complete (rows : Rows) : Complete rows (initialParents rows) := by
  intro state transitions present edge member child linked
  rw [initialParents, mem_stateSet]
  apply List.mem_filterMap.mpr
  refine ⟨(state, transitions), present, ?_⟩
  have found : transitions.any (fun edge => child ∈ edge.children) = true :=
    List.any_eq_true.mpr ⟨edge, member, by simpa using linked⟩
  simp [found]

/-- Adjusting each state once equals a conditional table map, with the same row order. -/
theorem adjust_fold (affected : List Nat) (distinct : affected.Nodup)
    (update : List Transition → List Transition) (rows : Rows) :
    affected.foldl (fun table state => adjust table state update) rows =
      rows.map (fun (state, transitions) =>
        (state, if state ∈ affected then update transitions else transitions)) := by
  induction affected generalizing rows with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp distinct
      rw [List.foldl_cons, ih unique]
      simp only [adjust, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro entry present
      rcases entry with ⟨state, transitions⟩
      by_cases atFirst : state = first
      · subst state
        simp [absent]
      · by_cases inRest : state ∈ rest <;> simp [atFirst, inRest]

/-- The source visits only the finite parent set of the replaced state. -/
def indexedCopy (source destination : Nat) (parents : Index) (rows : Rows) : Rows :=
  (parents source).foldl (fun table state => adjust table state (copy source destination)) rows

/-- An unaffected row has no new copy and retains its complete source order. -/
theorem copy_unaffected (source destination : Nat) (transitions : List Transition)
    (absent : ∀ edge ∈ transitions, source ∉ edge.children) : copy source destination transitions = transitions := by
  have none : transitions.filter (fun edge => source ∈ edge.children) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro edge member
    simpa using absent edge member
  simp [copy, none]

/-- A complete distinct parent index gives exactly the former complete-table traversal. -/
theorem indexedCopy_exact (source destination : Nat) (parents : Index) (rows : Rows)
    (complete : Complete rows parents) (parentDistinct : (parents source).Nodup)
    (rowDistinct : ∀ state transitions, (state, transitions) ∈ rows → transitions.Nodup) :
    indexedCopy source destination parents rows = rows.map (fun (state, transitions) =>
      (state, copyAlternatives (source, destination) transitions)) := by
  rw [indexedCopy, adjust_fold _ parentDistinct]
  apply List.map_congr_left
  rintro ⟨state, transitions⟩ present
  by_cases affected : state ∈ parents source
  · simp only [affected, ↓reduceIte]
    rw [copy_exact source destination transitions (rowDistinct state transitions present)]
  · have absent : ∀ edge ∈ transitions, source ∉ edge.children := by
      intro edge member linked
      exact affected (complete state transitions present edge member source linked)
    simp only [affected, ↓reduceIte]
    rw [← copy_exact source destination transitions (rowDistinct state transitions present),
      copy_unaffected source destination transitions absent]

/-- Copying adds affected parents to the destination child entry. -/
def copiedParents (parents : Index) (source destination : Nat) : Index := fun child =>
  if child = destination then stateSet (parents child ++ parents source) else parents child

/-- Root insertion also adds the root as a parent of every representative child. -/
def updatedParents (initial source destination : Nat) (retained : Transition) (parents : Index) : Index := fun child =>
  if source = initial ∧ child ∈ retained.children then
    stateSet (source :: copiedParents parents source destination child)
  else copiedParents parents source destination child

/-- Every prior parent remains available after copying and root insertion. -/
theorem parents_grow (initial source destination : Nat) (retained : Transition) (parents : Index)
    (child state : Nat) (present : state ∈ parents child) :
    state ∈ updatedParents initial source destination retained parents child := by
  have copied : state ∈ copiedParents parents source destination child := by
    simp only [copiedParents]
    split
    · rw [mem_stateSet]; exact List.mem_append_left _ present
    · exact present
  simp only [updatedParents]
  split
  · rw [mem_stateSet]; exact List.mem_cons_of_mem _ copied
  · exact copied

/-- Every affected source parent is recorded for the copied destination link. -/
theorem destination_parent (initial source destination : Nat) (retained : Transition) (parents : Index)
    (state : Nat) (present : state ∈ parents source) :
    state ∈ updatedParents initial source destination retained parents destination := by
  have copied : state ∈ copiedParents parents source destination destination := by
    simp only [copiedParents, ↓reduceIte, mem_stateSet, List.mem_append]
    exact Or.inr present
  simp only [updatedParents]
  split
  · rw [mem_stateSet]; exact List.mem_cons_of_mem _ copied
  · exact copied

/-- An installed representative's child is present even if no old root row used it. -/
theorem inserted_parent (initial source destination : Nat) (retained : Transition) (parents : Index)
    (atRoot : source = initial) (child : Nat) (linked : child ∈ retained.children) :
    source ∈ updatedParents initial source destination retained parents child := by
  simp [updatedParents, atRoot, linked, mem_stateSet]

/-- Both set unions preserve the source index's distinct parent keys. -/
theorem updated_distinct (initial source destination : Nat) (retained : Transition) (parents : Index)
    (distinct : ∀ child, (parents child).Nodup) (child : Nat) :
    (updatedParents initial source destination retained parents child).Nodup := by
  simp only [updatedParents]
  split
  · exact stateSet_distinct _
  · simp only [copiedParents]
    split
    · exact stateSet_distinct _
    · exact distinct child

/-- Every child of an old or copied transition has its required parent entry. -/
theorem copied_links (initial source destination : Nat) (retained : Transition) (parents : Index)
    (rows : Rows) (complete : Complete rows parents) (state : Nat) (transitions : List Transition)
    (present : (state, transitions) ∈ rows) (edge : Transition)
    (member : edge ∈ copy source destination transitions) (child : Nat) (linked : child ∈ edge.children) :
    state ∈ updatedParents initial source destination retained parents child := by
  rcases List.mem_append.mp member with old | added
  · exact parents_grow _ _ _ _ _ _ _ (complete state transitions present edge old child linked)
  · obtain ⟨original, selected, same⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_eraseDups.mp added)).1
    obtain ⟨old, affected⟩ := List.mem_filter.mp selected
    subst edge
    obtain ⟨before, oldChild, image⟩ := List.mem_map.mp linked
    by_cases changed : before = source
    · have childEq : destination = child := by simpa [redirectTransition, changed] using image
      rw [← childEq]
      exact destination_parent _ _ _ _ _ _ (complete state transitions present original old source (by simpa using affected))
    · have childEq : before = child := by simpa [redirectTransition, changed] using image
      rw [← childEq]
      exact parents_grow _ _ _ _ _ _ _ (complete state transitions present original old before oldChild)

/-- Install a root representative after deleting the selected transition. -/
def replaceRemoved (initial source : Nat) (removed retained : Transition) (transitions : List Transition) : List Transition :=
  let remaining := transitions.filter (· != removed)
  if source = initial then (retained :: remaining).eraseDups else remaining

/-- The complete changed table follows the source's two row updates. -/
def rewriteRows (initial source destination : Nat) (removed retained : Transition) (parents : Index) (rows : Rows) : Rows :=
  adjust (indexedCopy source destination parents rows) source (replaceRemoved initial source removed retained)

/-- The updated index remains complete after copied rows and representative insertion. -/
theorem rewrite_complete (initial source destination : Nat) (removed retained : Transition)
    (parents : Index) (rows : Rows) (complete : Complete rows parents)
    (parentDistinct : (parents source).Nodup) :
    Complete (rewriteRows initial source destination removed retained parents rows)
      (updatedParents initial source destination retained parents) := by
  intro state transitions present edge member child linked
  unfold rewriteRows indexedCopy at present
  rw [adjust_fold _ parentDistinct] at present
  simp only [adjust, List.map_map, Function.comp_def] at present
  obtain ⟨⟨oldState, original⟩, oldPresent, same⟩ := List.mem_map.mp present
  have stateEq : oldState = state := congrArg Prod.fst same
  subst oldState
  have rowsEq := congrArg Prod.snd same
  dsimp only at rowsEq
  subst transitions
  have copyLinks (current : Transition)
      (found : current ∈ if state ∈ parents source then copy source destination original else original)
      (value : Nat) (link : value ∈ current.children) :
      state ∈ updatedParents initial source destination retained parents value := by
    by_cases affected : state ∈ parents source
    · exact copied_links initial source destination retained parents rows complete state original oldPresent current
        (by simpa [affected] using found) value link
    · exact parents_grow _ _ _ _ _ _ _ (complete state original oldPresent current
        (by simpa [affected] using found) value link)
  by_cases modified : state = source
  · subst state
    simp only [↓reduceIte, replaceRemoved] at member
    by_cases atRoot : source = initial
    · simp only [atRoot, ↓reduceIte, List.mem_eraseDups, List.mem_cons] at member
      rcases member with same | prior
      · subst edge; exact inserted_parent _ _ _ _ _ atRoot child linked
      · exact copyLinks edge (by simpa only [atRoot] using (List.mem_filter.mp prior).1) child linked
    · simp only [atRoot, ↓reduceIte] at member
      exact copyLinks edge (List.mem_filter.mp member).1 child linked
  · exact copyLinks edge (by simpa [modified] using member) child linked

/-- Every row remains distinct across an indexed rewrite. -/
theorem rewrite_distinct (initial source destination : Nat) (removed retained : Transition)
    (parents : Index) (rows : Rows) (parentDistinct : (parents source).Nodup)
    (distinct : ∀ state transitions, (state, transitions) ∈ rows → transitions.Nodup) :
    ∀ state transitions, (state, transitions) ∈ rewriteRows initial source destination removed retained parents rows →
      transitions.Nodup := by
  intro state transitions present
  unfold rewriteRows indexedCopy at present
  rw [adjust_fold _ parentDistinct] at present
  simp only [adjust, List.map_map, Function.comp_def] at present
  obtain ⟨⟨oldState, original⟩, oldPresent, same⟩ := List.mem_map.mp present
  have stateEq : oldState = state := congrArg Prod.fst same
  subst oldState
  have rowsEq := congrArg Prod.snd same
  dsimp only at rowsEq
  subst transitions
  have copied : (if state ∈ parents source then copy source destination original else original).Nodup := by
    split
    · exact copy_distinct source destination original (distinct state original oldPresent)
    · exact distinct state original oldPresent
  split
  · simp only [replaceRemoved]
    split
    · exact SymbolicDriver.eraseDups_nodup _
    · exact copied.filter _
  · exact copied

/-- The complete changed row table equals the established full-table schedule operation. -/
theorem rewrite_exact (initial source destination : Nat) (removed retained : Transition)
    (parents : Index) (rows : Rows) (complete : Complete rows parents)
    (parentDistinct : (parents source).Nodup)
    (distinct : ∀ state transitions, (state, transitions) ∈ rows → transitions.Nodup) :
    rewriteRows initial source destination removed retained parents rows =
      adjust (rows.map fun (state, transitions) =>
        (state, copyAlternatives (source, destination) transitions)) source
          (replaceRemoved initial source removed retained) := by
  rw [rewriteRows, indexedCopy_exact source destination parents rows complete parentDistinct distinct]

/-- The current schedule carries the parent index beside its observable fields. -/
structure State where
  current : ScheduleState
  parents : Index

/-- The source skip conditions are unchanged. An applied step uses indexed copies. -/
def step (initial : Nat) (original : Rows) (state : State) (replacement : Replacement) : State :=
  match transitionAt original replacement.removed, transitionAt original replacement.retained with
  | some removed, some retained =>
      let source := replacement.removed.node
      let destination := replacement.retained.node
      if source = destination ∧ removed = retained then
        ⟨{state.current with rows := adjust state.current.rows source List.eraseDups}, state.parents⟩
      else if source ≠ destination ∧ row original destination ≠ [retained] then state
      else if removed ∉ row state.current.rows source then state
      else if retained ∉ row state.current.rows destination then state
      else if !keepsGuards state.current.rows source then state
      else if !unconstrainedBelow state.current.rows retained then state
      else
        ⟨⟨rewriteRows initial source destination removed retained state.parents state.current.rows,
          state.current.applied ++ [(source, destination)],
          if source = initial then (state.current.rootRepresentatives ++ [replacement.retained]).eraseDups
            else state.current.rootRepresentatives⟩,
          updatedParents initial source destination retained state.parents⟩
  | _, _ => state

/-- Each optimized step has exactly the earlier schedule's rows, redirects, and root ledger. -/
theorem step_exact (initial : Nat) (original : Rows) (state : State) (replacement : Replacement)
    (complete : Complete state.current.rows state.parents)
    (parentDistinct : ∀ child, (state.parents child).Nodup)
    (distinct : ∀ name transitions, (name, transitions) ∈ state.current.rows → transitions.Nodup) :
    (step initial original state replacement).current = applyStep initial original state.current replacement := by
  cases left : transitionAt original replacement.removed with
  | none => simp [step, applyStep, left]
  | some removed =>
      cases right : transitionAt original replacement.retained with
      | none => simp [step, applyStep, left, right]
      | some retained =>
          simp only [step, applyStep, left, right]
          repeat' first | split | rfl
          all_goals simp_all only
          all_goals rw [rewrite_exact _ _ _ _ _ _ _ complete (parentDistinct _) distinct]
          all_goals simp_all
          all_goals apply congrArg (adjust _ _)
          all_goals funext transitions
          all_goals simp_all [replaceRemoved]

/-- Row-local deletion and deduplication cannot invalidate a complete parent index. -/
theorem adjust_subset_complete (rows : Rows) (parents : Index) (complete : Complete rows parents)
    (source : Nat) (change : List Transition → List Transition)
    (subset : ∀ transitions edge, edge ∈ change transitions → edge ∈ transitions) :
    Complete (adjust rows source change) parents := by
  intro name transitions present edge member child linked
  obtain ⟨⟨oldName, original⟩, oldPresent, same⟩ := List.mem_map.mp present
  have nameEq : oldName = name := congrArg Prod.fst same
  subst oldName
  have rowsEq := congrArg Prod.snd same
  dsimp only at rowsEq
  subst transitions
  by_cases changed : name = source
  · exact complete name original oldPresent edge (subset original edge (by simpa [changed] using member)) child linked
  · exact complete name original oldPresent edge (by simpa [changed] using member) child linked

/-- Deduplicating one row retains the distinct-row invariant. -/
theorem adjust_dedup_distinct (rows : Rows) (source : Nat)
    (distinct : ∀ name transitions, (name, transitions) ∈ rows → transitions.Nodup) :
    ∀ name transitions, (name, transitions) ∈ adjust rows source List.eraseDups → transitions.Nodup := by
  intro name transitions present
  obtain ⟨⟨oldName, original⟩, oldPresent, same⟩ := List.mem_map.mp present
  have nameEq : oldName = name := congrArg Prod.fst same
  subst oldName
  have rowsEq := congrArg Prod.snd same
  dsimp only at rowsEq
  subst transitions
  split
  · exact SymbolicDriver.eraseDups_nodup _
  · exact distinct name original oldPresent

/-- Local source invariants needed for every later indexed step. -/
def Valid (state : State) : Prop :=
  Complete state.current.rows state.parents ∧ (∀ child, (state.parents child).Nodup) ∧
    ∀ name transitions, (name, transitions) ∈ state.current.rows → transitions.Nodup

/-- Every skip, deduplication, and rewrite step preserves the derived parent invariant. -/
theorem step_valid (initial : Nat) (original : Rows) (state : State) (replacement : Replacement)
    (valid : Valid state) : Valid (step initial original state replacement) := by
  cases left : transitionAt original replacement.removed with
  | none => simpa [step, left] using valid
  | some removed =>
      cases right : transitionAt original replacement.retained with
      | none => simpa [step, left, right] using valid
      | some retained =>
          simp only [step, left, right]
          split
          · exact ⟨adjust_subset_complete _ _ valid.1 _ List.eraseDups
                (fun _ _ member => List.mem_eraseDups.mp member), valid.2.1,
                adjust_dedup_distinct _ _ valid.2.2⟩
          · split
            · exact valid
            · split
              · exact valid
              · split
                · exact valid
                · split
                  · exact valid
                  · split
                    · exact valid
                    · exact ⟨rewrite_complete _ _ _ _ _ _ _ valid.1 (valid.2.1 _),
                        updated_distinct _ _ _ _ _ valid.2.1,
                        rewrite_distinct _ _ _ _ _ _ _ (valid.2.1 _) valid.2.2⟩

/-- Complete source schedule with a parent index built from the actual initial rows. -/
def scheduleIndexed (initial : Nat) (original : Rows) (steps : List Replacement) : State :=
  steps.foldl (step initial original) ⟨⟨original, [], []⟩, initialParents original⟩

/-- Every finite schedule has exactly the old observable result and a complete final parent index. -/
theorem fold_exact (initial : Nat) (original : Rows) (steps : List Replacement) (state : State)
    (valid : Valid state) :
    (steps.foldl (step initial original) state).current =
      steps.foldl (applyStep initial original) state.current ∧
    Valid (steps.foldl (step initial original) state) := by
  induction steps generalizing state with
  | nil => exact ⟨rfl, valid⟩
  | cons first rest ih =>
      have next := step_valid initial original state first valid
      have same := step_exact initial original state first valid.1 valid.2.1 valid.2.2
      have later := ih (step initial original state first) next
      exact ⟨by simpa only [List.foldl_cons, same] using later.1, later.2⟩

/-- The source optimization retains every established whole-schedule result. -/
theorem schedule_exact (initial : Nat) (original : Rows) (steps : List Replacement)
    (distinct : ∀ name transitions, (name, transitions) ∈ original → transitions.Nodup) :
    (scheduleIndexed initial original steps).current = schedule initial original steps ∧
      Valid (scheduleIndexed initial original steps) :=
  fold_exact initial original steps _
    ⟨initialParents_complete original, fun _ => stateSet_distinct _, distinct⟩

/-- The unchanged final validation returns the same result after indexed scheduling. -/
theorem finish_exact (initial : Nat) (original : Rows) (steps : List Replacement)
    (validate : Rows → Validation)
    (distinct : ∀ name transitions, (name, transitions) ∈ original → transitions.Nodup) :
    finish initial original steps (scheduleIndexed initial original steps).current validate =
      finish initial original steps (schedule initial original steps) validate := by
  rw [(schedule_exact initial original steps distinct).1]

/-- Repeated optimized copies preserve complete order and distinctness. -/
theorem copyFold_exact (redirects : List (Nat × Nat)) (transitions : List Transition)
    (distinct : transitions.Nodup) :
    redirects.foldl (fun current redirect => copy redirect.1 redirect.2 current) transitions =
      redirects.foldl (fun current redirect => copyAlternatives redirect current) transitions ∧
    (redirects.foldl (fun current redirect => copy redirect.1 redirect.2 current) transitions).Nodup := by
  induction redirects generalizing transitions with
  | nil => exact ⟨rfl, distinct⟩
  | cons redirect rest ih =>
      have next := copy_distinct redirect.1 redirect.2 transitions distinct
      have same := copy_exact redirect.1 redirect.2 transitions distinct
      have later := ih (copy redirect.1 redirect.2 transitions) next
      exact ⟨by simpa only [List.foldl_cons, same] using later.1, later.2⟩

/-- Final representative checks use the same optimized copy worker. -/
def representativeCopiesIndexed (original : Rows) (applied : List (Nat × Nat)) (chosen : Address) : List Transition :=
  match transitionAt original chosen with
  | none => []
  | some edge => applied.foldl (fun current redirect => copy redirect.1 redirect.2 current) [edge]

/-- Every final representative list agrees exactly, including copied child order. -/
theorem representativeCopies_exact (original : Rows) (applied : List (Nat × Nat)) (chosen : Address) :
    representativeCopiesIndexed original applied chosen = representativeCopies original applied chosen := by
  cases found : transitionAt original chosen with
  | none => simp [representativeCopiesIndexed, representativeCopies, found]
  | some edge => simpa only [representativeCopiesIndexed, representativeCopies, found] using
      (copyFold_exact applied [edge] (by simp)).1

/-- A root representative can introduce a child that the old root never used. -/
def insertedChildRows : Rows :=
  [(0, [leaf 0]), (1, [⟨10, 0, [2], noConstraint⟩]), (2, [leaf 2]), (3, [leaf 3])]

/-- Copy-only parent updates miss that new root link on a later rewrite. -/
theorem insertion_requires_parent_update :
    let retained : Transition := ⟨10, 0, [2], noConstraint⟩
    let before := initialParents insertedChildRows
    let changed := rewriteRows 0 0 1 (leaf 0) retained before insertedChildRows
    indexedCopy 2 3 (copiedParents before 0 1) changed ≠
      changed.map (fun (state, transitions) => (state, copyAlternatives (2, 3) transitions)) := by
  cbv
  intro same
  simp at same

/-- Recording the inserted root links restores the exact later copy schedule. -/
theorem inserted_parent_update_restores_copy :
    let retained : Transition := ⟨10, 0, [2], noConstraint⟩
    let before := initialParents insertedChildRows
    let changed := rewriteRows 0 0 1 (leaf 0) retained before insertedChildRows
    indexedCopy 2 3 (updatedParents 0 0 1 retained before) changed =
      changed.map (fun (state, transitions) => (state, copyAlternatives (2, 3) transitions)) := by
  cbv

end MicroCFTA.MinimizeParentIndex
