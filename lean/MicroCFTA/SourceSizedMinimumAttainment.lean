import MicroCFTA.SourceSizedMinimumConvergence
import MicroCFTA.SourceSizedMinimumStructuralBound

/-!
# Attainment of computed structural minimum entries

Each known entry starts from an actual source row and finite child runs.
The proof follows the actual pass order and the derived finite iteration.
The row guards are erased throughout this theorem.
-/
namespace MicroCFTA.SourceSizedMinimumAttainment
open SourceSizedMinimumPass SourceSizedMinimumConvergence SourceSizedDecided
open Language RecursiveSize
variable {Q Symbol Guard : Type}

private def Attained (source : Q → List (Row Q Symbol Guard)) (known : Table Q) : Prop :=
  ∀ current value, known current = some value →
    ∃ term, Accepts (automaton source (fun _ _ => true)) current term ∧ (nodeSize term : Int) = value

private theorem fold_member (values : List Int) (first : Int) :
    values.foldl min first ∈ first :: values := by
  induction values generalizing first with
  | nil => exact List.mem_cons_self
  | cons next rest ih =>
      have found := ih (min first next)
      rcases List.mem_cons.mp found with atFirst | inRest
      · have choice : min first next = first ∨ min first next = next := by omega
        rcases choice with same | same
        · exact List.mem_cons.mpr (Or.inl (atFirst.trans same))
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl (atFirst.trans same)))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ inRest)

private theorem least_member (values : List Int) (value : Int) (observed : least values = some value) :
    value ∈ values := by
  cases values with
  | nil => simp only [least, reduceCtorEq] at observed
  | cons first rest =>
      have same : rest.foldl min first = value := Option.some.inj observed
      rw [← same]
      exact fold_member rest first

private theorem children_attained (source : Q → List (Row Q Symbol Guard)) (known : Table Q)
    (attained : Attained source known) (children : List Q) (sizes : List Int)
    (observed : children.mapM known = some sizes) :
    ∃ terms, All₂ (Accepts (automaton source (fun _ _ => true))) children terms ∧
      (forestSize terms : Int) = sizes.sum := by
  induction children generalizing sizes with
  | nil =>
      change some [] = some sizes at observed
      have same := Option.some.inj observed
      subst sizes
      exact ⟨[], .nil, rfl⟩
  | cons child rest ih =>
      cases head : known child with
      | none => simp [List.mapM_cons, head] at observed
      | some value =>
          cases tail : rest.mapM known with
          | none => simp [List.mapM_cons, head, tail] at observed
          | some values =>
              have same : value :: values = sizes := by simpa [List.mapM_cons, head, tail] using observed
              subst sizes
              obtain ⟨term, accepted, exactSize⟩ := attained child value head
              obtain ⟨terms, acceptedTail, exactTail⟩ := ih values tail
              refine ⟨term :: terms, .cons accepted acceptedTail, ?_⟩
              change ((nodeSize term + forestSize terms : Nat) : Int) = value + values.sum
              omega

private theorem transition_attained (source : Q → List (Row Q Symbol Guard)) (known : Table Q)
    (attained : Attained source known) (current : Q) (row : Row Q Symbol Guard)
    (member : row ∈ source current) (value : Int) (observed : transitionMinimum known row = some value) :
    ∃ term, Accepts (automaton source (fun _ _ => true)) current term ∧ (nodeSize term : Int) = value := by
  cases children : row.children.mapM known with
  | none => simp only [transitionMinimum, children, Option.map_none, reduceCtorEq] at observed
  | some sizes =>
      have cost : 1 + sizes.sum = value := by
        simpa only [transitionMinimum, children, Option.map_some, Option.some.injEq] using observed
      obtain ⟨terms, accepted, exactSize⟩ := children_attained source known attained row.children sizes children
      refine ⟨.node row.label terms, ?_, ?_⟩
      · exact .node (row.edge (fun _ _ => true)) terms (List.mem_map.mpr ⟨row, member, rfl⟩) accepted rfl
      · simp only [nodeSize]
        change ((forestSize terms + 1 : Nat) : Int) = value
        omega

private theorem add_attained [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (key : Q) (known : Table Q) (attained : Attained source known) :
    Attained source (addMinimum key (source key) known) := by
  intro current value observed
  cases selected : least ((source key).filterMap (transitionMinimum known)) with
  | none => exact attained current value (by simpa only [addMinimum, selected] using observed)
  | some candidate =>
      have listed := least_member _ candidate selected
      obtain ⟨row, member, rowCost⟩ := List.mem_filterMap.mp listed
      have candidateWitness := transition_attained source known attained key row member candidate rowCost
      by_cases same : current = key
      · subst current
        cases before : known key with
        | none =>
            have exactValue : candidate = value := by
              simpa only [addMinimum, selected, insertMinimum, ite_eq_left, before, Option.some.injEq] using observed
            subst value
            exact candidateWitness
        | some old =>
            have oldWitness := attained key old before
            have exactValue : min candidate old = value := by
              simpa only [addMinimum, selected, insertMinimum, ite_eq_left, before, Option.some.injEq] using observed
            have choice : value = candidate ∨ value = old := by omega
            rcases choice with isCandidate | isOld
            · rw [isCandidate]
              exact candidateWitness
            · rw [isOld]
              exact oldWitness
      · exact attained current value (by
          simpa only [addMinimum, selected, insertMinimum, ite_eq_right same] using observed)

private theorem scan_attained [DecidableEq Q] (source : Q → List (Row Q Symbol Guard))
    (keys : List Q) (known : Table Q) (attained : Attained source known) :
    Attained source (scan source keys known) := by
  induction keys with
  | nil => exact attained
  | cons key rest ih => exact add_attained source key (scan source rest known) ih

private theorem passes_attained [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (count : Nat) : ∀ known, Attained input.rows known → Attained input.rows (passes input count known) := by
  induction count with
  | zero => intro known attained; exact attained
  | succ count ih =>
      intro known attained
      exact ih (pass input known) (scan_attained input.rows input.states known attained)

/-- Every computed known entry has a finite guard-erased term of exactly that node size. -/
theorem minimum_attained [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) :
    ∀ current value, minimumSizes input current = some value →
      ∃ term, Accepts (automaton input.rows (fun _ _ => true)) current term ∧ (nodeSize term : Int) = value := by
  obtain ⟨count, reached⟩ := minimum_reachable input
  have initial : Attained input.rows (fun _ => none) := by
    intro current value impossible
    cases impossible
  have attained := passes_attained input count (fun _ => none) initial
  rw [reached] at attained
  exact attained

/-- The computed known size is attained and bounds every finite guard-erased run. -/
theorem minimum_is_least [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (current : Q) (value : Int) (found : minimumSizes input current = some value) :
    (∃ term, Accepts (automaton input.rows (fun _ _ => true)) current term ∧ (nodeSize term : Int) = value) ∧
      ∀ term, Accepts (automaton input.rows (fun _ _ => true)) current term → value ≤ (nodeSize term : Int) := by
  refine ⟨minimum_attained input current value found, ?_⟩
  intro term accepted
  obtain ⟨other, actual, bounded⟩ := SourceSizedMinimumStructuralBound.erased_lower_bound input current term accepted
  have same := Option.some.inj (found.symm.trans actual)
  subst other
  exact bounded

/-- An unknown computed entry is equivalent to absence of a finite guard-erased run. -/
theorem minimum_none_iff [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (current : Q) : minimumSizes input current = none ↔
      ¬ ∃ term, Accepts (automaton input.rows (fun _ _ => true)) current term := by
  constructor
  · intro absent ⟨term, accepted⟩
    obtain ⟨value, actual, _bounded⟩ := SourceSizedMinimumStructuralBound.erased_lower_bound input current term accepted
    rw [absent] at actual
    cases actual
  · intro noTerm
    cases found : minimumSizes input current with
    | none => rfl
    | some value =>
        obtain ⟨term, accepted, _exactSize⟩ := minimum_attained input current value found
        exact False.elim (noTerm ⟨term, accepted⟩)

end MicroCFTA.SourceSizedMinimumAttainment
