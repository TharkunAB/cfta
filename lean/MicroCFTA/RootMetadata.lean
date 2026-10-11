import MicroCFTA.SupportTerms
import MicroCFTA.RecipeCompile

/-!
# Root-count metadata and private term forests

The source counts a placeholder leaf as the one root that will fill it.
Unknown metadata makes no count claim. Empty choices have count one, with
no members to contradict that count.
-/
namespace MicroCFTA.RootMetadata
open Language GeneratorCombinators SupportTerms RecipeCompile

mutual
/-- The exact source `termRootCount`, including open integer leaves. -/
def termRoots : Term (Label Symbol) → Nat
  | .node (.user _) _ => 1
  | .node .placeholder [] => 1
  | .node _ children => forestRoots children

/-- Sum the roots contributed by an ordered child forest. -/
def forestRoots : List (Term (Label Symbol)) → Nat
  | [] => 0
  | first :: rest => termRoots first + forestRoots rest
end

mutual
/-- The eventual user forest, with an explicit label for an unfilled leaf. -/
def prospectiveSurface : Term (Label Symbol) → List (Term (Option Symbol))
  | .node (.user symbol) children => [.node (some symbol) (prospectiveForest children)]
  | .node .placeholder [] => [.node none []]
  | .node _ children => prospectiveForest children

/-- Keep every eventual root in forest order. -/
def prospectiveForest : List (Term (Label Symbol)) → List (Term (Option Symbol))
  | [] => []
  | first :: rest => prospectiveSurface first ++ prospectiveForest rest
end

/-- Root metadata counts exactly the eventual user forest. -/
theorem roots_exact (term : Term (Label Symbol)) : termRoots term = (prospectiveSurface term).length := by
  induction term using Term.rec
    (motive_2 := fun terms => forestRoots terms = (prospectiveForest terms).length) with
  | node label children ih =>
    cases label <;> cases children <;> simp_all [termRoots, prospectiveSurface]
  | nil => rfl
  | cons first rest hf hr => simp [forestRoots, prospectiveForest, hf, hr]

/-- Known metadata describes every member; unknown metadata imposes no restriction. -/
def Sound (count : RootCount) (terms : List (Term (Label Symbol))) : Prop :=
  ∀ size, count = .known size → ∀ term ∈ terms, termRoots term = size

/-- Reading the exact roots of one member gives sound metadata. -/
theorem singleton_sound (term : Term (Label Symbol)) : Sound (.known (termRoots term)) [term] := by
  intro size same selected member
  have sizeEq := RootCount.known.inj same
  have termEq := List.mem_singleton.mp member
  simp [termEq, sizeEq]

/-- Unknown metadata cannot falsely certify an arity. -/
theorem unknown_sound (terms : List (Term (Label Symbol))) : Sound .unknown terms := by
  intro size impossible
  cases impossible

/-- Combining choice metadata preserves the count claim for every alternative. -/
theorem common_sound (parts : List (RootCount × List (Term (Label Symbol))))
    (sound : ∀ part ∈ parts, Sound part.1 part.2) :
    Sound (commonRoots (parts.map Prod.fst)) (parts.flatMap Prod.snd) := by
  intro size count term member
  cases parts with
  | nil => simp at member
  | cons first rest =>
    simp only [List.map_cons, commonRoots] at count
    split at count
    · next agree =>
      have every : ∀ part ∈ first :: rest, part.1 = .known size := by
        intro part present
        rcases List.mem_cons.mp present with rfl | present
        · exact count
        · have same : part.1 = first.1 := by
            have check := List.all_eq_true.mp agree part.1 (List.mem_map.mpr ⟨part, present, rfl⟩)
            exact beq_iff_eq.mp check
          exact same.trans count
      obtain ⟨part, present, termPresent⟩ := List.mem_flatMap.mp member
      exact sound part present size (every part present) term termPresent
    · cases count

/-- Enumerating root counts cannot report a false common count. -/
theorem enumerated_sound (terms : List (Term (Label Symbol))) :
    Sound (commonRoots (terms.map fun term => .known (termRoots term))) terms := by
  have proved := common_sound (terms.map fun term => (RootCount.known (termRoots term), [term])) (by
    intro part member
    obtain ⟨term, _, rfl⟩ := List.mem_map.mp member
    exact singleton_sound term)
  simpa only [List.map_map, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_singleton', Function.comp_def] using proved

/-- Application adds the complete child-root counts. -/
theorem apply_roots (left right : Term (Label Symbol)) :
    termRoots (.node .apply [left, right]) = termRoots left + termRoots right := by
  simp [termRoots, forestRoots]

/-- Product metadata agrees with every independently selected operand pair. -/
theorem add_sound (leftCount rightCount : RootCount) (left right : List (Term (Label Symbol)))
    (hl : Sound leftCount left) (hr : Sound rightCount right) :
    Sound (addRoots leftCount rightCount)
      (left.flatMap fun first => right.map fun second => .node .apply [first, second]) := by
  intro size same term member
  cases leftCount with
  | unknown => cases same
  | known a => cases rightCount with
    | unknown => cases same
    | known b =>
      have sum : a + b = size := RootCount.known.inj same
      obtain ⟨first, leftMember, selected⟩ := List.mem_flatMap.mp member
      obtain ⟨second, rightMember, rfl⟩ := List.mem_map.mp selected
      rw [apply_roots, hl a rfl first leftMember, hr b rfl second rightMember, sum]

/-- Closing any source term establishes exactly one root. -/
theorem label_roots (symbol : Symbol) (term : Term (Label Symbol)) :
    termRoots (labelTerm symbol term) = 1 := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ term ∈ terms, termRoots (labelTerm symbol term) = 1) with
  | node label children ih =>
    cases label with
    | choice index =>
      cases children with
      | nil => rfl
      | cons first rest => cases rest with
        | nil => exact ih first (by simp)
        | cons second rest => rfl
    | _ => simp [labelTerm, termRoots]
  | nil => simp_all
  | cons first rest hf hr =>
    rename_i term member
    rcases List.mem_cons.mp member with rfl | member
    · exact hf
    · exact hr term member

/-- A labelled finite source's stored count one is always sound. -/
theorem label_sound (symbol : Symbol) (terms : List (Term (Label Symbol))) :
    Sound (.known 1) (terms.map (labelTerm symbol)) := by
  intro size same term member
  have equal := RootCount.known.inj same
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  simpa [equal] using label_roots symbol original

/-- Private binary join keys contribute no user roots. -/
theorem join_roots (group : Nat) (left right : Term (Label Symbol)) :
    termRoots (joinTerm group left right) = termRoots left + termRoots right := by
  simp [joinTerm, termRoots, forestRoots]

/-- A private choice wrapper retains the root count of its member. -/
theorem choice_roots (index : Nat) (term : Term (Label Symbol)) :
    termRoots (.node (.choice index) [term]) = termRoots term := by
  simp [termRoots, forestRoots]

/-- A known single-root position has exactly one eventual child tree. -/
theorem known_one_singleton (terms : List (Term (Label Symbol))) (sound : Sound (.known 1) terms)
    (term : Term (Label Symbol)) (member : term ∈ terms) :
    ∃ root, prospectiveSurface term = [root] := by
  apply List.length_eq_one_iff.mp
  rw [← roots_exact]
  exact sound 1 rfl term member

/-- A spine of single-root positions gives exactly one root per argument position. -/
theorem aligned_spine_roots (terms : List (Term (Label Symbol)))
    (one : ∀ term ∈ terms, termRoots term = 1) : forestRoots terms = terms.length := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
    simp only [forestRoots, one first (by simp), List.length_cons]
    rw [ih (fun term member => one term (by simp [member]))]
    omega

end MicroCFTA.RootMetadata
