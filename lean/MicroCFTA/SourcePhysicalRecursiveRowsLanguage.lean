import MicroCFTA.SourcePhysicalRecursiveRowsReadback

/-!
# Independent language of the actual one-knot exposure

The language contains a base leaf and any finite number of unary steps.
The proof follows actual physical epsilon transitions and the stored rows
proved by unfolding. It derives cold-to-warm language preservation from
exact replay and this independent inductive language.
-/
namespace MicroCFTA.SourcePhysicalRecursiveRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency Language
open InternedNestedConstruction (Outcome)

/-- The independent finite language of one base and one recursive unary step. -/
inductive Chain (base step : Symbol) : Term Symbol → Prop
  | base : Chain base step (.node base [])
  | step : Chain base step term → Chain base step (.node step [term])

/-- Read the existing physical epsilon graph with the plain guard. -/
abbrev Physical [DecidableEq Symbol] (state : State Symbol Unit) (value : Value Symbol Unit) (term : Term Symbol) :=
  EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state (fun _ _ => true)) value term

/-- The actual ordinary result has exactly its base and recursive-step language equation. -/
theorem exposed_equation [DecidableEq Symbol] (state : State Symbol Unit) (root result : Value Symbol Unit)
    (base step : Symbol) (exposed : Exposed root result base step) (term : Term Symbol) :
    Physical state result term ↔ term = .node base [] ∨
      ∃ child, term = .node step [child] ∧ Physical state root child := by
  obtain ⟨entry, edges, depth, free, rfl⟩ := exposed.ordinary
  obtain ⟨first, second, firstSymbol, firstChildren, secondSymbol, secondChildren, _, members⟩ := exposed.rows
  constructor
  · intro accepted
    cases accepted with
    | reference member accepted => simp [MergedPhysicalLanguage.graph, MergedPhysicalComparison.successors] at member
    | node edge terms member runs guard =>
        obtain ⟨stored, present, rfl⟩ := List.mem_map.mp member
        rcases (members stored).mp present with rfl | rfl
        · rw [firstChildren] at runs
          cases runs
          exact Or.inl (by rw [firstSymbol])
        · rw [secondChildren] at runs
          cases runs with
          | cons child rest =>
              cases rest
              exact Or.inr ⟨_, by rw [secondSymbol], child⟩
  · intro accepted
    rcases accepted with same | ⟨child, same, accepted⟩
    · rw [same, ← firstSymbol]
      exact .node ⟨first.entry.key.symbol, first.children, fun _ => true⟩ []
        (List.mem_map.mpr ⟨first, (members first).mpr (Or.inl rfl), rfl⟩) (by rw [firstChildren]; exact .nil) rfl
    · rw [same, ← secondSymbol]
      exact .node ⟨second.entry.key.symbol, second.children, fun _ => true⟩ [child]
        (List.mem_map.mpr ⟨second, (members second).mpr (Or.inr rfl), rfl⟩)
        (by rw [secondChildren]; exact .cons accepted .nil) rfl

/-- A completed actual Mu exposure gives one exact epsilon step to its returned record. -/
theorem mu_equation [DecidableEq Symbol] (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary result : Value Symbol Unit) (before after : State Symbol Unit)
    (done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) before = .done result after)
    (term : Term Symbol) : Physical before (.mu entry body depth ordinary) term ↔ Physical before result term := by
  constructor
  · intro accepted
    cases accepted with
    | reference member accepted =>
        rename_i target
        have same : target = result := by
          simpa only [MergedPhysicalLanguage.graph, MergedPhysicalComparison.successors, done, List.mem_singleton] using member
        exact same ▸ accepted
    | node edge terms member runs guard =>
        simp [MergedPhysicalLanguage.graph, MergedPhysicalComparison.constructorRows] at member
  · intro accepted
    exact .reference (by simp [MergedPhysicalLanguage.graph, MergedPhysicalComparison.successors, done]) accepted

/-- Source unfolding and derived row readback yield the exact knot language equation. -/
theorem knot_equation [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary result : Value Symbol Unit)
    (before after : State Symbol Unit)
    (done : InternedStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) before = .done result after)
    (exposed : Exposed (knot entry bodyEntry base step depth ordinary) result base.key.symbol step.key.symbol)
    (term : Term Symbol) :
    Physical before (knot entry bodyEntry base step depth ordinary) term ↔ term = .node base.key.symbol [] ∨
      ∃ child, term = .node step.key.symbol [child] ∧ Physical before (knot entry bodyEntry base step depth ordinary) child :=
  (mu_equation entry _ depth ordinary result before after done term).trans
    (exposed_equation before _ result base.key.symbol step.key.symbol exposed term)

/-- Every finite physical run contains a finite number of unary recursive steps. -/
theorem accepts_chain [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary result : Value Symbol Unit)
    (before after : State Symbol Unit)
    (done : InternedStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) before = .done result after)
    (exposed : Exposed (knot entry bodyEntry base step depth ordinary) result base.key.symbol step.key.symbol)
    (term : Term Symbol) (accepted : Physical before (knot entry bodyEntry base step depth ordinary) term) :
    Chain base.key.symbol step.key.symbol term := by
  rcases (knot_equation entry bodyEntry base step depth ordinary result before after done exposed term).mp accepted with
    rfl | ⟨child, rfl, childAccepted⟩
  · exact .base
  · exact .step (accepts_chain entry bodyEntry base step depth ordinary result before after done exposed child childAccepted)
termination_by term.height
decreasing_by
  subst term
  simp [Term.height]

/-- Every independently specified finite chain has an actual physical accepting run. -/
theorem chain_accepts [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary result : Value Symbol Unit)
    (before after : State Symbol Unit)
    (done : InternedStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) before = .done result after)
    (exposed : Exposed (knot entry bodyEntry base step depth ordinary) result base.key.symbol step.key.symbol)
    (term : Term Symbol) (chain : Chain base.key.symbol step.key.symbol term) :
    Physical before (knot entry bodyEntry base step depth ordinary) term := by
  induction chain with
  | base => exact (knot_equation entry bodyEntry base step depth ordinary result before after done exposed _).mpr (Or.inl rfl)
  | step child ih =>
      exact (knot_equation entry bodyEntry base step depth ordinary result before after done exposed _).mpr (Or.inr ⟨_, rfl, ih⟩)

/-- Exact current unfolding preserves the knot language and then replays without further effects. -/
theorem unfold_language [DecidableEq Symbol] (entry bodyEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (base step : Cache.Interned (EdgeKey Symbol Unit)) (depth ordinary : Value Symbol Unit)
    (state : State Symbol Unit) (facts : Facts state)
    (available : Available state (knot entry bodyEntry base step depth ordinary)) :
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) state = .done result after ∧
      Facts after ∧ Available after result ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) after = .done result after ∧
      (∀ term, Physical state (knot entry bodyEntry base step depth ordinary) term ↔ Chain base.key.symbol step.key.symbol term) ∧
      (∀ term, Physical after (knot entry bodyEntry base step depth ordinary) term ↔ Chain base.key.symbol step.key.symbol term) ∧
      (∀ term, Physical state (knot entry bodyEntry base step depth ordinary) term ↔ Physical after result term) := by
  obtain ⟨result, after, currentDone, oldDone, afterFacts, growth, history, resultAvailable, rootAvailable, exposed⟩ :=
    unfold_complete entry bodyEntry base step depth ordinary state facts available
  have replay := MergedPhysicalWarmup.unfold_replay _ state after result after facts.coherent.valid oldDone (grows_refl after)
  have currentReplay : InternedFreshOrdinaryStoredSubstitution.unfold (knot entry bodyEntry base step depth ordinary) after = .done result after :=
    (InternedFreshOrdinaryStoredSubstitution.unfold_mu_eq entry _ depth ordinary after (body_prepared _ _ _ _)).trans replay
  have cold := fun term => Iff.intro
    (accepts_chain entry bodyEntry base step depth ordinary result state after oldDone exposed term)
    (chain_accepts entry bodyEntry base step depth ordinary result state after oldDone exposed term)
  have warm := fun term => Iff.intro
    (accepts_chain entry bodyEntry base step depth ordinary result after after replay exposed term)
    (chain_accepts entry bodyEntry base step depth ordinary result after after replay exposed term)
  exact ⟨result, after, currentDone, afterFacts, resultAvailable, currentReplay, cold, warm, fun term =>
    (cold term).trans ((warm term).symm.trans (mu_equation entry _ depth ordinary result after after replay term))⟩

end MicroCFTA.SourcePhysicalRecursiveRows
