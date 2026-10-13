import MicroCFTA.Language

/-!
# Recursive coverage used by merged narrowing

The source may reuse an ancestor pair while it compares recursive nodes.
Such a reuse is sound for finite accepted terms. A certificate records the
successful comparisons. It does not assert that every source call terminates.
The automaton exposes the source's closed outgoing edges. Its correspondence
with recursive node exposure remains a separate representation contract.
-/
namespace MicroCFTA.MergedAlternativesSubsumption
open Language

mutual
/-- A finite successful source comparison, including ancestor-pair reuse. -/
inductive Checked (automaton : Automaton State Symbol) :
    List (State × State) → State → State → Prop where
  | same : Checked automaton above state state
  | seen : (wide, narrow) ∈ above → Checked automaton above wide narrow
  | expand (select : Edge State Symbol → Edge State Symbol)
      (member : ∀ edge ∈ automaton narrow, select edge ∈ automaton wide)
      (label : ∀ edge ∈ automaton narrow, (select edge).label = edge.label)
      (guard : ∀ edge ∈ automaton narrow, ∀ term, (select edge).guard term = true)
      (children : ∀ edge ∈ automaton narrow,
        Children automaton ((wide, narrow) :: above) (select edge).children edge.children) :
      Checked automaton above wide narrow

/-- Each child pair has a successful comparison with the same ancestor stack. -/
inductive Children (automaton : Automaton State Symbol) :
    List (State × State) → List State → List State → Prop where
  | nil : Children automaton above [] []
  | cons : Checked automaton above wide narrow → Children automaton above wides narrows →
      Children automaton above (wide :: wides) (narrow :: narrows)
end

/-- The simultaneous child certificates give the usual pointwise relation. -/
theorem children_all₂ (related : Children automaton above wides narrows) :
    All₂ (Checked automaton above) wides narrows := by
  induction narrows generalizing wides with
  | nil => cases related; exact .nil
  | cons narrow narrows ih =>
      cases related with
      | cons head tail => exact .cons head (ih tail)

/-- Transfer two pointwise relations through their shared middle list. -/
theorem all₂_transfer {R : A → B → Prop} {S : B → C → Prop} {T : A → C → Prop}
    (transfer : ∀ a b c, R a b → S b c → T a c)
    {first middle last} (related : All₂ R first middle) (accepted : All₂ S middle last) :
    All₂ T first last := by
  induction related generalizing last with
  | nil => cases accepted; exact .nil
  | cons head tail ih =>
      cases accepted with
      | cons accepted rest => exact .cons (transfer _ _ _ head accepted) (ih rest)

/-- Ancestor assumptions at a finite height suffice for every checked pair at that height. -/
theorem checked_bounded (automaton : Automaton State Symbol) (fuel : Nat)
    (above : List (State × State)) (wide narrow : State)
    (checked : Checked automaton above wide narrow)
    (ancestors : ∀ pair ∈ above, ∀ term,
      term ∈ enumerate automaton fuel pair.2 → term ∈ enumerate automaton fuel pair.1) :
    ∀ term, term ∈ enumerate automaton fuel narrow → term ∈ enumerate automaton fuel wide := by
  induction fuel generalizing above wide narrow with
  | zero => simp [enumerate]
  | succ fuel ih =>
      intro term accepted
      cases checked with
      | same => exact accepted
      | seen member => exact ancestors _ member term accepted
      | expand select coverMember coverLabel coverGuard coverChildren =>
          obtain ⟨edge, edgeMember, children, childrenAccepted, rfl, guard⟩ :=
            (mem_enumerate_succ automaton fuel narrow term).mp accepted
          let cover := select edge
          have oldAncestors : ∀ pair ∈ above, ∀ child,
              child ∈ enumerate automaton fuel pair.2 → child ∈ enumerate automaton fuel pair.1 := by
            intro pair member child accepted
            have larger := ancestors pair member child (enumerate_mono automaton (Nat.le_succ fuel) accepted)
            exact (mem_enumerate_iff automaton fuel pair.1 child).mpr
              ⟨enumerate_sound automaton _ larger, ((mem_enumerate_iff automaton fuel pair.2 child).mp accepted).2⟩
          have current : ∀ child, child ∈ enumerate automaton fuel narrow →
              child ∈ enumerate automaton fuel wide :=
            ih above wide narrow (.expand select coverMember coverLabel coverGuard coverChildren) oldAncestors
          have nextAncestors : ∀ pair ∈ (wide, narrow) :: above, ∀ child,
              child ∈ enumerate automaton fuel pair.2 → child ∈ enumerate automaton fuel pair.1 := by
            intro pair member child accepted
            rcases List.mem_cons.mp member with rfl | member
            · exact current child accepted
            · exact oldAncestors pair member child accepted
          apply (mem_enumerate_succ automaton fuel wide (.node edge.label children)).mpr
          refine ⟨cover, coverMember edge edgeMember, children, ?_, ?_, coverGuard edge edgeMember _⟩
          · exact all₂_transfer (fun first second child comparison accepted =>
              ih _ first second comparison nextAncestors child accepted) (children_all₂ (coverChildren edge edgeMember)) childrenAccepted
          · change Term.node edge.label children = Term.node (select edge).label children
            rw [coverLabel edge edgeMember]

/-- A complete successful comparison contains every finite term of its narrow input. -/
theorem checked_sound (automaton : Automaton State Symbol) (wide narrow : State)
    (checked : Checked automaton [] wide narrow) (term : Term Symbol)
    (accepted : Accepts automaton narrow term) : Accepts automaton wide term := by
  obtain ⟨fuel, member⟩ := enumerate_complete automaton accepted
  exact enumerate_sound automaton fuel
    (checked_bounded automaton fuel [] wide narrow checked (by simp) term member)

/-- Compare all child pairs and reject different arities. -/
def checkChildren (compare : State → State → Bool) : List State → List State → Bool
  | [], [] => true
  | wide :: wides, narrow :: narrows => compare wide narrow && checkChildren compare wides narrows
  | _, _ => false

/-- A fuel limit exposes successful finite executions without assuming totality. -/
def check [DecidableEq State] [DecidableEq Symbol] (automaton : Automaton State Symbol)
    (unconstrained : Edge State Symbol → Bool) : Nat → List (State × State) → State → State → Bool
  | fuel, above, wide, narrow =>
    if wide = narrow then true
    else if (wide, narrow) ∈ above then true
    else match fuel with
    | 0 => false
    | rest + 1 => (automaton narrow).all fun edge =>
        (automaton wide).any fun cover =>
          decide (cover.label = edge.label) && unconstrained cover &&
            checkChildren (check automaton unconstrained rest ((wide, narrow) :: above))
              cover.children edge.children

/-- Successful child comparisons yield the finite pointwise certificate. -/
theorem checkChildren_certificate (compare : State → State → Bool)
    (certify : ∀ wide narrow, compare wide narrow = true → Checked automaton above wide narrow)
    (wides narrows : List State) (success : checkChildren compare wides narrows = true) :
    Children automaton above wides narrows := by
  induction wides generalizing narrows with
  | nil => cases narrows <;> simp_all [checkChildren]; exact .nil
  | cons wide wides ih =>
      cases narrows with
      | nil => simp [checkChildren] at success
      | cons narrow narrows =>
          have both := Bool.and_eq_true_iff.mp success
          exact .cons (certify wide narrow both.1) (ih narrows both.2)

/-- Every successful bounded source search has a sound recursive comparison certificate. -/
theorem check_certificate [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (fuel : Nat) (above : List (State × State)) (wide narrow : State)
    (success : check automaton unconstrained fuel above wide narrow = true) :
    Checked automaton above wide narrow := by
  classical
  induction fuel generalizing above wide narrow with
  | zero =>
      simp only [check] at success
      split at success
      · rename_i same; subst narrow; exact .same
      · split at success
        · exact .seen (by assumption)
        · contradiction
  | succ fuel ih =>
      simp only [check] at success
      split at success
      · rename_i same; subst narrow; exact .same
      · split at success
        · exact .seen (by assumption)
        · have witnesses := List.all_eq_true.mp success
          let select (edge : Edge State Symbol) : Edge State Symbol :=
            if member : edge ∈ automaton narrow then
              Classical.choose (List.any_eq_true.mp (witnesses edge member))
            else edge
          have selected (edge : Edge State Symbol) (member : edge ∈ automaton narrow) :
              select edge ∈ automaton wide ∧
                (decide ((select edge).label = edge.label) && unconstrained (select edge) &&
                  checkChildren (check automaton unconstrained fuel ((wide, narrow) :: above))
                    (select edge).children edge.children) = true := by
            simp only [select, dite_eq_left member]
            exact Classical.choose_spec (List.any_eq_true.mp (witnesses edge member))
          refine .expand select (fun edge member => (selected edge member).1) ?_ ?_ ?_
          · intro edge member
            exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (selected edge member).2).1).1
          · intro edge member
            exact clear _ (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (selected edge member).2).1).2
          · intro edge member
            exact checkChildren_certificate _ (ih _)
              _ _ (Bool.and_eq_true_iff.mp (selected edge member).2).2

/-- A successful source comparison can safely remove its narrow operand from a union. -/
theorem check_sound [DecidableEq State] [DecidableEq Symbol]
    (automaton : Automaton State Symbol) (unconstrained : Edge State Symbol → Bool)
    (clear : ∀ edge, unconstrained edge = true → ∀ term, edge.guard term = true)
    (fuel : Nat) (wide narrow : State)
    (success : check automaton unconstrained fuel [] wide narrow = true)
    (term : Term Symbol) (accepted : Accepts automaton narrow term) :
    Accepts automaton wide term :=
  checked_sound automaton wide narrow
    (check_certificate automaton unconstrained clear fuel [] wide narrow success) term accepted

/-- The source retains every recursive operand and removes only covered other operands. -/
def Retained (recursive : State → Prop) (covers : State → State → Prop)
    (inputs : List State) (state : State) : Prop :=
  state ∈ inputs ∧ (recursive state ∨ ¬ ∃ wide ∈ inputs, recursive wide ∧ covers wide state)

/-- Removing an operand covered by a retained recursive operand preserves the union language. -/
theorem retained_union_exact (meaning : State → Value → Prop) (recursive : State → Prop)
    (covers : State → State → Prop)
    (sound : ∀ wide narrow, covers wide narrow → ∀ value, meaning narrow value → meaning wide value)
    (inputs : List State) (value : Value) :
    (∃ state, Retained recursive covers inputs state ∧ meaning state value) ↔
      ∃ state ∈ inputs, meaning state value := by
  classical
  constructor
  · rintro ⟨state, retained, accepted⟩
    exact ⟨state, retained.1, accepted⟩
  · rintro ⟨state, member, accepted⟩
    by_cases retained : recursive state ∨ ¬ ∃ wide ∈ inputs, recursive wide ∧ covers wide state
    · exact ⟨state, ⟨member, retained⟩, accepted⟩
    · have covered : ∃ wide ∈ inputs, recursive wide ∧ covers wide state := by
        exact Classical.byContradiction (fun absent => retained (Or.inr absent))
      obtain ⟨wide, wideMember, recursiveWide, coverage⟩ := covered
      exact ⟨wide, ⟨wideMember, Or.inl recursiveWide⟩, sound wide state coverage value accepted⟩

/-- Successful recursive source comparisons justify the child-union filter. -/
theorem checked_filter_exact (automaton : Automaton State Symbol) (recursive : State → Prop)
    (inputs : List State) (term : Term Symbol) :
    (∃ state, Retained recursive (Checked automaton []) inputs state ∧ Accepts automaton state term) ↔
      ∃ state ∈ inputs, Accepts automaton state term :=
  retained_union_exact (Accepts automaton) recursive (Checked automaton [])
    (checked_sound automaton) inputs term

end MicroCFTA.MergedAlternativesSubsumption
