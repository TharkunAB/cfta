import MicroCFTA.SourceCurrentConjunctionClassWitness
open MicroCFTA MicroCFTA.Language MicroCFTA.EqualityNormalize
open MicroCFTA.SourceCurrentConjunctionClassWitness

-- The common witness is a proper subtree at every literal rotated operand.
example (term : Term Symbol) (paths : Class) (active : Nontrivial paths) (satisfied : ClassSat term paths) :
    ∃ part, (∀ path ∈ SourceEmptinessClassFold.seededPaths (paths.map (List.map Int.ofNat)),
      SymbolicSignedPaths.lookup term path = some part) ∧ part.height < term.height := by
  obtain ⟨part, _, common, smaller⟩ := class_rotated_common term paths active satisfied
  exact ⟨part, common, smaller⟩

-- An active satisfied class cannot contain the root, even before a native query exists.
example (term : Term Symbol) (paths : Class) (active : Nontrivial paths) (satisfied : ClassSat term paths) :
    [] ∉ paths := by
  intro member
  obtain ⟨part, common, smaller⟩ := class_common term paths active satisfied
  have same := Option.some.inj (common [] member)
  subst part
  omega

-- Rotation keeps repeated path occurrences without changing their common lookup property.
example (term part : Term Symbol) (first second : List Int) :
    (∀ path ∈ [second, first, first], SymbolicSignedPaths.lookup term path = some part) ↔
      ∀ path ∈ [first, second, first], SymbolicSignedPaths.lookup term path = some part := by
  exact rotated_common term [first, second, first] part

-- Two equal sibling terms give a genuine nonempty common proper subtree.
example (symbol : Symbol) (part : Term Symbol) :
    ∃ common, (∀ path ∈ SourceEmptinessClassFold.seededPaths ([[0], [1]].map (List.map Int.ofNat)),
      SymbolicSignedPaths.lookup (.node symbol [part, part]) path = some common) ∧
      common.height < (Term.node symbol [part, part]).height := by
  have active : Nontrivial [[0], [1]] := ⟨[0], by simp, [1], by simp, by decide⟩
  have satisfied : ClassSat (.node symbol [part, part]) [[0], [1]] := by
    intro left leftMember right rightMember _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
    rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl
    all_goals exact ⟨part, rfl, rfl⟩
  obtain ⟨common, _, chosen, smaller⟩ := class_rotated_common (.node symbol [part, part]) [[0], [1]] active satisfied
  exact ⟨common, chosen, smaller⟩
