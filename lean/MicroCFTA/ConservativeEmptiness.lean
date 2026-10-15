import MicroCFTA.Productivity

/-!
# Conservative emptiness on a finite requirement graph

Empty requirements are impossible. Requirements outside the explored graph
remain possible. Inside requirements read a synchronous Boolean fixed point.
The soundness premise describes accepted finite witnesses independently of
the Boolean algorithm. The source exploration, edge closure, path reads,
and intersection operations must still supply this premise.
-/
namespace MicroCFTA.ConservativeEmptiness

/-- A requirement is empty, outside the explored graph, or an explored state. -/
inductive Requirement (State : Type) where
  | empty
  | outside
  | inside (state : State)

/-- Omitted nodes remain possible at every iteration. -/
def canAccept (known : State → Bool) : Requirement State → Bool
  | .empty => false
  | .outside => true
  | .inside state => known state

/-- An explored state needs one row whose requirements all remain possible. -/
def step (rows : State → List (List (Requirement State))) (known : State → Bool) (state : State) : Bool :=
  (rows state).any (fun row => row.all (canAccept known))

/-- Requirement evaluation preserves inclusion of known states. -/
theorem canAccept_monotone (left right : State → Bool) (included : Productivity.Included left right)
    (requirement : Requirement State) : canAccept left requirement = true → canAccept right requirement = true := by
  cases requirement with
  | empty => intro impossible; cases impossible
  | outside => intro _; rfl
  | inside state => exact included state

/-- The synchronous row operator is monotone. -/
theorem step_monotone (rows : State → List (List (Requirement State))) : Productivity.Monotone (step rows) := by
  intro left right included state possible
  obtain ⟨row, member, obligations⟩ := List.any_eq_true.mp possible
  apply List.any_eq_true.mpr
  refine ⟨row, member, List.all_eq_true.mpr ?_⟩
  intro requirement selected
  exact canAccept_monotone left right included requirement (List.all_eq_true.mp obligations requirement selected)

/-- Compute the possible explored states from false, within the number of listed states. -/
def possible (states : List State) (rows : State → List (List (Requirement State))) : State → Bool :=
  Productivity.iterate (step rows) (fun _ => false) states.length

/-- Each iteration retains all states marked by the previous iteration. -/
theorem iterate_ascending (rows : State → List (List (Requirement State))) (fuel : Nat) :
    Productivity.Included (Productivity.iterate (step rows) (fun _ => false) fuel)
      (Productivity.iterate (step rows) (fun _ => false) (fuel + 1)) :=
  Productivity.iterate_ascending _ _ (step_monotone rows) (by intro state impossible; cases impossible) fuel

/-- A complete finite state list makes the computed iterate an actual fixed point. -/
theorem possible_fixed (states : List State) (complete : ∀ state, state ∈ states)
    (rows : State → List (List (Requirement State))) : step rows (possible states rows) = possible states rows :=
  Productivity.finite_stability states complete _ _ (step_monotone rows)
    (by intro state impossible; cases impossible)

/-- Extra synchronous iterations preserve the computed fixed point. -/
theorem iterate_stable (states : List State) (complete : ∀ state, state ∈ states)
    (rows : State → List (List (Requirement State))) (extra : Nat) :
    Productivity.iterate (step rows) (fun _ => false) (states.length + extra) = possible states rows := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, Productivity.iterate, ih]
      exact possible_fixed states complete rows

/-- The computed iterate is below every state set closed under the row operator. -/
theorem possible_least (states : List State) (rows : State → List (List (Requirement State)))
    (known : State → Bool) (closed : Productivity.Included (step rows known) known) :
    Productivity.Included (possible states rows) known :=
  Productivity.iterate_below_closed _ _ known (step_monotone rows)
    (by intro state impossible; cases impossible) closed states.length

/-- True certifies that the query is impossible in the computed overapproximation. -/
def provablyEmpty (states : List State) (rows : State → List (List (Requirement State)))
    (query : Requirement State) : Bool := !canAccept (possible states rows) query

/-- Independent witness semantics for a query, including the optimistic outside case. -/
def AcceptsRequirement (accepted : State → Term → Prop) : Requirement State → Term → Prop
  | .empty, _ => False
  | .outside, _ => True
  | .inside state, term => accepted state term

/-- Every explored obligation needs a smaller accepted witness; outside imposes no condition. -/
def Obligation (accepted : State → Term → Prop) (weight : Term → Nat) (parent : Term) : Requirement State → Prop
  | .empty => False
  | .outside => True
  | .inside state => ∃ term, accepted state term ∧ weight term < weight parent

/-- Source semantics must supply a stored row of necessary smaller-witness requirements. -/
def Decomposes (rows : State → List (List (Requirement State))) (accepted : State → Term → Prop)
    (weight : Term → Nat) : Prop :=
  ∀ state term, accepted state term →
    ∃ row ∈ rows state, ∀ requirement ∈ row, Obligation accepted weight term requirement

/-- Every finite semantic witness is marked at any fixed point of the row operator. -/
theorem fixed_no_loss (rows : State → List (List (Requirement State)))
    (accepted : State → Term → Prop) (weight : Term → Nat) (decomposes : Decomposes rows accepted weight)
    (known : State → Bool) (fixed : step rows known = known) (state : State) (term : Term)
    (witness : accepted state term) : known state = true := by
  have bounded : ∀ bound term, weight term = bound → ∀ state, accepted state term → known state = true := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro term size state witness
        obtain ⟨row, member, obligations⟩ := decomposes state term witness
        rw [← fixed]
        apply List.any_eq_true.mpr
        refine ⟨row, member, List.all_eq_true.mpr ?_⟩
        intro requirement selected
        have obligation := obligations requirement selected
        cases requirement with
        | empty => exact False.elim obligation
        | outside => rfl
        | inside child =>
            obtain ⟨childTerm, childWitness, smaller⟩ := obligation
            exact ih (weight childTerm) (by omega) childTerm rfl child childWitness
  exact bounded (weight term) term rfl state witness

/-- The finite algorithm does not reject an accepted explored-state witness. -/
theorem possible_no_loss (states : List State) (complete : ∀ state, state ∈ states)
    (rows : State → List (List (Requirement State))) (accepted : State → Term → Prop) (weight : Term → Nat)
    (decomposes : Decomposes rows accepted weight) (state : State) (term : Term) (witness : accepted state term) :
    possible states rows state = true :=
  fixed_no_loss rows accepted weight decomposes _ (possible_fixed states complete rows) state term witness

/-- An accepted query remains possible, including every query outside the explored graph. -/
theorem accepted_canAccept (states : List State) (complete : ∀ state, state ∈ states)
    (rows : State → List (List (Requirement State))) (accepted : State → Term → Prop) (weight : Term → Nat)
    (decomposes : Decomposes rows accepted weight) (query : Requirement State) (term : Term)
    (witness : AcceptsRequirement accepted query term) : canAccept (possible states rows) query = true := by
  cases query with
  | empty => exact False.elim witness
  | outside => rfl
  | inside state => exact possible_no_loss states complete rows accepted weight decomposes state term witness

/-- A true emptiness answer excludes every accepted finite witness under local semantic decomposition. -/
theorem provablyEmpty_sound (states : List State) (complete : ∀ state, state ∈ states)
    (rows : State → List (List (Requirement State))) (accepted : State → Term → Prop) (weight : Term → Nat)
    (decomposes : Decomposes rows accepted weight) (query : Requirement State)
    (empty : provablyEmpty states rows query = true) : ∀ term, ¬AcceptsRequirement accepted query term := by
  intro term witness
  have possible := accepted_canAccept states complete rows accepted weight decomposes query term witness
  simp only [provablyEmpty, possible, Bool.not_true, Bool.false_eq_true] at empty

end MicroCFTA.ConservativeEmptiness
