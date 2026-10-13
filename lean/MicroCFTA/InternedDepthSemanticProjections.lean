import MicroCFTA.InternedDepthSemantics

/-!
# Existing semantic projections of the deeper shape interpreter

A coherent shape has no deep names without an opaque alternative.
The new interpreter preserves coherence. Its profile projection agrees
with the earlier independent profile interpreter. The free-name projection
is a separate remaining proof.
-/
namespace MicroCFTA.InternedDepthSemanticProjections
open InternedNestedConstruction InternedDepthSemantics

/-- Deep names require an ordinary or Mu boundary in the shape. -/
def Coherent (value : Shape Atom) : Prop := value.hasOpaque = false → value.deep = []

/-- A list of shape inputs satisfies the same local representation condition. -/
def CoherentMany (values : List (Shape Atom)) : Prop := ∀ value ∈ values, Coherent value

/-- Forget deep names and depth to recover the existing root profile. -/
def profile (value : Shape Atom) : InternedProfileSemantics.Abstract Atom :=
  if value.hasOpaque then none else some value.roots

/-- Renaming preserves the shape condition. -/
theorem coherent_map (function : Atom → Other) (value : Shape Atom) (valid : Coherent value) : Coherent (value.map function) := by
  intro flag
  simp only [Shape.map] at flag ⊢
  rw [valid flag]
  rfl

/-- A union can lack opaque alternatives only if both operands lack them. -/
theorem coherent_combine (first second : Shape Atom) (left : Coherent first) (right : Coherent second) :
    Coherent (combine first second) := by
  intro empty
  have both : first.hasOpaque = false ∧ second.hasOpaque = false := by simpa [combine] using empty
  simp only [combine, left both.1, right both.2, List.nil_append]

/-- Every source edge has a coherent shape, including a discarded edge. -/
theorem coherent_edge (children : List (Shape Atom)) : Coherent (edge children) := by
  unfold edge
  split <;> simp [Coherent]

/-- Both binder forms preserve the shape condition. -/
theorem coherent_binder (smart : Bool) (body : Shape (Sum Unit Atom)) (valid : Coherent body) :
    Coherent (binder smart body) := by
  unfold binder
  split
  · simp [Coherent]
  · intro empty
    change body.hasOpaque = false at empty
    change lower body.deep = []
    rw [valid empty]
    rfl

/-- Ordered shape union preserves the condition of all operands. -/
theorem coherent_many (values : List (Shape Atom)) (valid : CoherentMany values) : Coherent (combineMany values) := by
  induction values with
  | nil => intro _; rfl
  | cons first rest ih =>
      exact coherent_combine first _ (valid first List.mem_cons_self)
        (ih (fun value member => valid value (List.mem_cons_of_mem _ member)))

mutual
/-- Every pure source expression preserves coherent shape inputs. -/
theorem evaluate_coherent (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (valid : CoherentMany environment) : Coherent (evaluate expression environment) := by
  cases expression with
  | empty => rw [evaluate]; intro _; rfl
  | var index =>
      rw [evaluate]
      cases found : environment[index]? with
      | none => intro _; rfl
      | some value => exact valid value (List.mem_of_getElem? found)
  | node edges => rw [evaluate]; exact evaluateEdges_coherent edges environment valid
  | union members => rw [evaluate]; exact coherent_many _ (evaluateMany_coherent members environment valid)
  | binder smart body =>
      rw [evaluate]
      apply coherent_binder
      apply evaluate_coherent body
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · intro _; rfl
      · obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
        exact coherent_map Sum.inr original (valid original included)
termination_by sizeOf expression

/-- Ordered child evaluation preserves coherence at every position. -/
theorem evaluateMany_coherent (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) : CoherentMany (evaluateMany expressions environment) := by
  cases expressions with
  | nil => rw [evaluateMany]; intro value member; cases member
  | cons first rest =>
      rw [evaluateMany]
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact evaluate_coherent first environment valid
      · exact evaluateMany_coherent rest environment valid value member
termination_by sizeOf expressions

/-- Ordered edge evaluation preserves coherence after deleted edges. -/
theorem evaluateEdges_coherent (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) : Coherent (evaluateEdges expressions environment) := by
  cases expressions with
  | nil => rw [evaluateEdges]; intro _; rfl
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [evaluateEdges]
          exact coherent_combine _ _ (coherent_edge _) (evaluateEdges_coherent rest environment valid)
termination_by sizeOf expressions
end

/-- Empty decisions agree after profile projection. -/
theorem profile_empty (value : Shape Atom) : InternedProfileSemantics.isEmpty (profile value) = value.isEmpty := by
  cases flag : value.hasOpaque <;> cases roots : value.roots <;> simp [profile, Shape.isEmpty, flag, roots, InternedProfileSemantics.isEmpty]

/-- Projection commutes with external-name maps. -/
theorem profile_map (function : Atom → Other) (value : Shape Atom) :
    profile (value.map function) = InternedProfileSemantics.mapNames function (profile value) := by
  cases flag : value.hasOpaque <;> simp [profile, Shape.map, flag, InternedProfileSemantics.mapNames]

/-- Shape union projects to the existing ordered profile union. -/
theorem profile_combine (first second : Shape Atom) :
    profile (combine first second) = InternedProfileSemantics.combine (profile first) (profile second) := by
  cases left : first.hasOpaque <;> cases right : second.hasOpaque <;>
    simp [profile, combine, left, right, InternedProfileSemantics.combine]

/-- Ordered shape union projects to ordered profile union. -/
theorem profile_many (values : List (Shape Atom)) :
    profile (combineMany values) = InternedProfileSemantics.combineMany (values.map profile) := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp only [combineMany, profile_combine, List.map_cons, InternedProfileSemantics.combineMany, ih]

/-- Smart and raw binder projection matches the existing binder decision. -/
theorem profile_binder (smart : Bool) (body : Shape (Sum Unit Atom)) (valid : Coherent body) :
    profile (binder smart body) = if smart then InternedProfileSemantics.lower (profile body) else none := by
  cases smart with
  | false => simp [binder, profile]
  | true =>
      cases flag : body.hasOpaque with
      | false => simp [binder, profile, flag, valid flag, hasLocal, InternedProfileSemantics.lower, lower, InternedFreeNameSemantics.lower]; rfl
      | true => simp only [binder, Bool.not_true, Bool.false_or, profile, flag, ↓reduceIte, InternedProfileSemantics.lower]
                split <;> rfl

/-- An edge's projected profile uses the exact existing live-child decision. -/
theorem profile_edge (children : List (Shape Atom)) :
    profile (edge children) = if (children.map profile).all (fun child => !InternedProfileSemantics.isEmpty child)
      then none else some [] := by
  have same : (children.map profile).all (fun child => !InternedProfileSemantics.isEmpty child) =
      !children.any Shape.isEmpty := by
    rw [List.all_map]
    simp only [Function.comp_def, profile_empty]
    exact (List.not_any_eq_all_not).symm
  rw [same]
  unfold edge
  cases selected : children.any Shape.isEmpty <;> simp only [Bool.false_eq_true, Bool.not_false,
    Bool.not_true, ↓reduceIte, profile]

/-- Ordinary edge observations have no root reference alternatives. -/
theorem edges_roots (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom)) :
    (evaluateEdges expressions environment).roots = [] := by
  induction expressions with
  | nil => simp only [evaluateEdges]
  | cons first rest ih =>
      cases first with
      | mk symbol guard children => simp only [evaluateEdges, combine, ih, List.append_nil, edge]; split <;> rfl

/-- Extending a coherent shape environment gives a coherent symbolic local. -/
theorem local_coherent (environment : List (Shape Atom)) (valid : CoherentMany environment) :
    CoherentMany (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · intro _; rfl
  · obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    exact coherent_map Sum.inr original (valid original included)

/-- Projection preserves the exact symbolic-local environment used by the profile interpreter. -/
theorem profile_local (environment : List (Shape Atom)) :
    (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr)).map profile =
      some [.inl ()] :: (environment.map profile).map (InternedProfileSemantics.mapNames Sum.inr) := by
  simp only [List.map_cons, List.map_map, Function.comp_def, profile_map]
  rfl

mutual
/-- The richer shape interpreter has exactly the existing pure root profile. -/
theorem evaluate_profile (expression : Syntax Symbol Guard) (environment : List (Shape Atom))
    (valid : CoherentMany environment) :
    profile (evaluate expression environment) = InternedProfileSemantics.evaluate expression (environment.map profile) := by
  cases expression with
  | empty => simp [evaluate, profile, InternedProfileSemantics.evaluate]
  | var index =>
      rw [evaluate, InternedProfileSemantics.evaluate]
      cases found : environment[index]? <;> simp [List.getElem?_map, found, profile]
  | node edges => simpa only [evaluate, InternedProfileSemantics.evaluate] using evaluateEdges_profile edges environment valid
  | union members =>
      rw [evaluate, profile_many, evaluateMany_profile members environment valid, InternedProfileSemantics.evaluate]
  | binder smart body =>
      rw [evaluate, profile_binder smart _ (evaluate_coherent body _ (local_coherent environment valid)),
        evaluate_profile body _ (local_coherent environment valid), profile_local]
      cases smart <;> simp only [InternedProfileSemantics.evaluate, Bool.false_eq_true, ↓reduceIte]
termination_by sizeOf expression

/-- Every ordered child has its exact original profile interpretation. -/
theorem evaluateMany_profile (expressions : List (Syntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) :
    (evaluateMany expressions environment).map profile =
      InternedProfileSemantics.evaluateMany expressions (environment.map profile) := by
  cases expressions with
  | nil => simp only [evaluateMany, List.map_nil, InternedProfileSemantics.evaluateMany]
  | cons first rest =>
      simp only [evaluateMany, List.map_cons, evaluate_profile first environment valid,
        evaluateMany_profile rest environment valid, InternedProfileSemantics.evaluateMany]
termination_by sizeOf expressions

/-- Ordinary node shape opacity matches the existing live-edge decision. -/
theorem evaluateEdges_profile (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Shape Atom))
    (valid : CoherentMany environment) :
    profile (evaluateEdges expressions environment) =
      if InternedProfileSemantics.evaluateEdges expressions (environment.map profile) then none else some [] := by
  cases expressions with
  | nil => simp [evaluateEdges, profile, InternedProfileSemantics.evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [evaluateEdges, profile_combine, profile_edge, evaluateMany_profile children environment valid,
            evaluateEdges_profile rest environment valid, InternedProfileSemantics.evaluateEdges]
          cases head : (InternedProfileSemantics.evaluateMany children (environment.map profile)).all
            (fun child => !InternedProfileSemantics.isEmpty child) <;>
            cases tail : InternedProfileSemantics.evaluateEdges rest (environment.map profile) <;> rfl
termination_by sizeOf expressions
end

end MicroCFTA.InternedDepthSemanticProjections
