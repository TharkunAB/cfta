import MicroCFTA.RecursiveFieldBounds

/-!
# N-ary callback contracts below a requested forest height

Flat alternatives use child inverse laws only at the requested labelled
forest or at the single child below a private whole-term wrapper.
-/
namespace MicroCFTA.RecursiveNaryFieldBounds
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveNaryChoice
open RecursiveFieldBounds

/-- True child certificates below the request bound replay their source offset. -/
theorem branch_certified_below (limit : Nat) (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, ExactBelow limit child)
    (branch : Nat) (view : View) (wanted : List (EngineTerm Symbol)) (position : Position)
    (bound : forestHeight wanted ≤ limit)
    (member : (position, true) ∈ branchRows children branch view wanted) :
    ∃ term, select children position = some (wrap branch term) ∧ project view term = wanted := by
  obtain ⟨child, ⟨p, flag⟩, present, member, same⟩ := (branch_member children branch view wanted _).mp member
  have flagEq : flag = true := congrArg Prod.snd same
  subst flag
  obtain ⟨term, selected, projected⟩ := (exactChildren child (List.mem_of_getElem? present) view wanted bound p).mp member
  have within := (indexed child (List.mem_of_getElem? present) p).mp ⟨term, selected⟩
  have replay := select_offset children branch child present p term within selected
  have positionsEq := congrArg Prod.fst same
  exact ⟨term, by simpa only [positionsEq] using replay, projected⟩

/-- Each successful child selector supplies a true branch row in every view. -/
theorem branch_complete_below (limit : Nat) (children : List (Finite Symbol))
    (exactChildren : ∀ child ∈ children, ExactBelow limit child)
    (branch : Nat) (child : Finite Symbol) (present : children[branch]? = some child)
    (p : Position) (term : EngineTerm Symbol) (selected : child.select p = some term) (view : View)
    (bound : forestHeight (project view term) ≤ limit) :
    ((offset children branch (p, true)).1, true) ∈ branchRows children branch view (project view term) := by
  apply (branch_member children branch view (project view term) _).mpr
  exact ⟨child, (p, true), present,
    (exactChildren child (List.mem_of_getElem? present) view (project view term) bound p).mpr ⟨term, selected, rfl⟩,
    rfl⟩


/-- Arbitrary flat alternatives preserve height-restricted inverse contracts. -/
theorem field_exact_below (limit : Nat) (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child)
    (exactChildren : ∀ child ∈ children, ExactBelow limit child) : ExactBelow limit (RecursiveNaryChoice.field children) := by
  intro view wanted bound position
  change (position, true) ∈ RecursiveNaryChoice.positions children view wanted ↔
    ∃ term, select children position = some term ∧ project view term = wanted
  constructor
  · intro member
    cases view with
    | whole | spine =>
        simp only [RecursiveNaryChoice.positions, mem_sorted] at member
        obtain ⟨branch, term, rfl, member⟩ := whole_origin children wanted _ member
        obtain ⟨child, selected, projected⟩ := branch_certified_below limit children indexed exactChildren branch .whole [term] position (by simp_all [wrap, forestHeight, Term.height]; omega) member
        have same : child = term := by simpa [project] using projected
        subst child
        exact ⟨wrap branch term, selected, by simp [project_wrap]⟩
    | labelled =>
        obtain ⟨branch, _, member⟩ := List.mem_flatMap.mp ((mem_sorted _ _).mp member)
        obtain ⟨term, selected, projected⟩ := branch_certified_below limit children indexed exactChildren branch .labelled wanted position bound member
        exact ⟨wrap branch term, selected, (project_wrap branch term).2.2.trans projected⟩
  · rintro ⟨term, selected, rfl⟩
    obtain ⟨branch, child, p, childTerm, present, childSelected, _, same, rfl⟩ := select_origin children position term selected
    have complete := branch_complete_below limit children exactChildren branch child present p childTerm childSelected
    cases view with
    | whole | spine =>
        simp only [RecursiveNaryChoice.positions, mem_sorted, (project_wrap branch childTerm).1,
          (project_wrap branch childTerm).2.1]
        simpa only [wrap, wholeRows, project, same] using complete .whole (by simp only [(project_wrap branch childTerm).1, (project_wrap branch childTerm).2.1] at bound; simp_all [project, wrap, forestHeight, Term.height]; omega)
    | labelled =>
        rw [RecursiveNaryChoice.positions, mem_sorted, (project_wrap branch childTerm).2.2]
        exact List.mem_flatMap.mpr ⟨branch,
          List.mem_range.mpr (List.getElem?_eq_some_iff.mp present).1,
          by simpa only [same] using complete .labelled (by simpa only [project_wrap] using bound)⟩


end MicroCFTA.RecursiveNaryFieldBounds
