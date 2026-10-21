import MicroCFTA.SourceEqualityPCSNativeEdge

/-!
# Public guard readback for annotated stored records

Only complete edge annotations read by the independent language need the
source normalized-payload invariant. Probe metadata does not define meaning.
The independent PCS interpretation and public indicator interpretation then
agree through ordinary, union, and least-language recursive records.
-/
namespace MicroCFTA.SourceEqualityAnnotationLanguage
open Language InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open InternedGuardedLanguage

/-- Every semantic edge annotation of a stored record satisfies one source predicate. -/
inductive Annotated (valid : Guard → Prop) : Value Symbol Guard → Prop where
  | empty : Annotated valid .empty
  | reference (name) : Annotated valid (.reference name)
  | node (entry) (edges : List (EdgeValue Symbol Guard)) (depth free)
      (guards : ∀ edge ∈ edges, valid edge.entry.key.constraint)
      (children : ∀ child ∈ edges.flatMap EdgeValue.children, Annotated valid child) : Annotated valid (.node entry edges depth free)
  | union (entry) (members : List (Value Symbol Guard)) (depth free)
      (children : ∀ child ∈ members, Annotated valid child) : Annotated valid (.union entry members depth free)
  | mu (entry) (body depth ordinary : Value Symbol Guard) (annotated : Annotated valid body) : Annotated valid (.mu entry body depth ordinary)

/-- Equal complete child meanings give equal ordered forest acceptance across guard interpretations. -/
theorem forest_congr_holds (first second : Guard → Term Symbol → Bool) (ambient : Env Symbol)
    (children : List (Value Symbol Guard)) (same : ∀ child ∈ children, meaning first ambient child = meaning second ambient child)
    (terms : List (Term Symbol)) : forest first ambient children terms ↔ forest second ambient children terms := by
  induction children generalizing terms with
  | nil => cases terms <;> simp only [forest]
  | cons child rest ih =>
      cases terms with
      | nil => simp only [forest]
      | cons term terms =>
          rw [forest, forest]
          exact and_congr (iff_of_eq (congrFun (same child List.mem_cons_self) term))
            (ih (fun child member => same child (List.mem_cons_of_mem _ member)) terms)

/-- Agreement on actual annotated guards transports the complete independent stored-record language. -/
theorem meaning_congr_holds (first second : Guard → Term Symbol → Bool) (valid : Guard → Prop)
    (agree : ∀ guard, valid guard → ∀ term, first guard term = second guard term)
    (value : Value Symbol Guard) (annotated : Annotated valid value) (ambient : Env Symbol) :
    meaning first ambient value = meaning second ambient value := by
  induction annotated generalizing ambient with
  | empty | reference => simp only [meaning]
  | node entry edges depth free guards children ih =>
      rw [meaning, meaning]
      funext term
      apply propext
      apply exists_congr
      intro edge
      rcases edge with ⟨edge, edgeMember⟩
      cases edge with
      | mk entry children =>
          rw [edgeMeaning, edgeMeaning]
          apply exists_congr
          intro terms
          apply and_congr Iff.rfl
          exact and_congr (forest_congr_holds first second ambient children
            (fun child member => ih child (List.mem_flatMap.mpr ⟨.mk entry children, edgeMember, member⟩) ambient) terms)
            (by rw [agree entry.key.constraint (guards (.mk entry children) edgeMember) term])
  | union entry members depth free children ih =>
      rw [meaning, meaning]
      funext term
      apply propext
      apply exists_congr
      intro member
      exact iff_of_eq (congrFun (ih member.val member.property ambient) term)
  | mu entry body depth ordinary annotated ih =>
      rw [meaning, meaning]
      apply BinderLanguage.least_congr
      intro candidate term
      exact iff_of_eq (congrFun (ih (bind ambient (.interned entry.identity) candidate)) term)

/-- Every normalized stored source annotation has exactly the public complete-constraint language. -/
theorem public_eq [DecidableEq Formula] (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (value : Value (Label Formula) (Constraint Formula))
    (annotated : Annotated (fun guard => SourceEqualityGuardReadback.Cached guard.equalities) value)
    (ambient : Env (Label Formula)) :
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value = meaning (acceptsConstraint formulas solver) ambient value :=
  meaning_congr_holds _ _ _ (fun guard cached term => SourceEqualityPCSGuard.public_eq formulas solver guard (SourceEqualityGuardReadback.active cached) term)
    value annotated ambient

/-- Actual normalized complete edges retain exact public readback of the independent PCS edge interpretation. -/
theorem edge_public_eq [DecidableEq Formula] (formulas : SourceGuards.Formulas Formula) (solver : SourceGuards.Entailment Formula)
    (edge : EdgeValue (Label Formula) (Constraint Formula)) (stored : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    (children : ∀ child ∈ edge.children, Annotated (fun guard => SourceEqualityGuardReadback.Cached guard.equalities) child)
    (ambient : Env (Label Formula)) :
    edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient edge = edgeMeaning (acceptsConstraint formulas solver) ambient edge := by
  cases edge with
  | mk entry values =>
      change SourceEqualityGuardReadback.Cached entry.key.constraint.equalities at stored
      funext term
      apply propext
      rw [edgeMeaning, edgeMeaning]
      apply exists_congr
      intro terms
      apply and_congr Iff.rfl
      exact and_congr (forest_congr_holds _ _ ambient values (fun child member => public_eq formulas solver child (children child member) ambient) terms)
        (by rw [SourceEqualityPCSGuard.public_eq formulas solver entry.key.constraint (SourceEqualityGuardReadback.active stored) term])

end MicroCFTA.SourceEqualityAnnotationLanguage
