import MicroCFTA.RecursiveSize
import MicroCFTA.Productivity

/-!
# Minimum finite node counts

The table stores an optional natural number at each state. `none` means that
no finite run has been found. A sweep uses a right fold. Each row reads the
table produced by the rows to its right, as in `Map.foldrWithKey addMinimum`.
The state list represents the map key order. Completeness requires every
state in this finite model to occur in that list.

The algorithm ignores guards. Its language theorems therefore require plain
automata. They also apply to the structural language after guard erasure.
Natural numbers model the nonnegative values of Haskell's unbounded `Size`
integer. The concrete representation of Haskell maps is outside this module.
-/

namespace MicroCFTA.MinimumSize

open Language RecursiveSize

/-- A finite entry improves an unknown entry. Smaller finite entries improve larger ones. -/
def Improves (before after : Option Nat) : Prop :=
  ∀ size, before = some size → ∃ smaller, after = some smaller ∧ smaller ≤ size

/-- Compare every entry of two tables. -/
def Refines (before after : State → Option Nat) : Prop :=
  ∀ state, Improves (before state) (after state)

/-- Retain the least available finite size. -/
def best : Option Nat → Option Nat → Option Nat
  | none, other => other
  | other, none => other
  | some left, some right => some (min left right)

/-- Add child sizes only when every child has a finite entry. -/
def childSum (known : State → Option Nat) : List State → Option Nat
  | [] => some 0
  | child :: children => do
      let size ← known child
      let rest ← childSum known children
      pure (size + rest)

/-- Count the root and all children of a transition. -/
def edgeMinimum (known : State → Option Nat) (edge : Edge State Symbol) : Option Nat :=
  (childSum known edge.children).map (· + 1)

/-- Find the least available outgoing transition size. -/
def rowMinimum (known : State → Option Nat) : List (Edge State Symbol) → Option Nat
  | [] => none
  | edge :: edges => best (edgeMinimum known edge) (rowMinimum known edges)

/-- Update one row with the least size found so far. -/
def relax [DecidableEq State] (automaton : Automaton State Symbol)
    (state : State) (known : State → Option Nat) : State → Option Nat :=
  fun target => if target = state then best (known state) (rowMinimum known (automaton state))
    else known target

/-- Read the updated table after each row in a right fold. -/
def sweep [DecidableEq State] (automaton : Automaton State Symbol) (states : List State)
    (known : State → Option Nat) : State → Option Nat :=
  states.foldr (relax automaton) known

/-- Child summation equals a successful traversal followed by addition. -/
theorem childSum_traverse (known : State → Option Nat) (states : List State) :
    childSum known states = (states.mapM known).map List.sum := by
  induction states with
  | nil => rfl
  | cons state states ih =>
      rw [childSum, ih, List.mapM_cons]
      cases known state <;> cases states.mapM known <;> rfl

/-- The row calculation is `minimum` after removal of unavailable transitions. -/
theorem rowMinimum_filterMap (known : State → Option Nat) (edges : List (Edge State Symbol)) :
    rowMinimum known edges = (edges.filterMap (edgeMinimum known)).min? := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
      rw [rowMinimum, List.filterMap_cons, ih]
      cases present : edgeMinimum known edge with
      | none => rfl
      | some size =>
          rw [List.min?_cons]
          cases (edges.filterMap (edgeMinimum known)).min? <;> rfl

/-- Every table refines itself. -/
theorem improves_refl (value : Option Nat) : Improves value value := by
  intro size same
  exact ⟨size, same, Nat.le_refl _⟩

/-- Improvements compose. -/
theorem improves_trans {first middle last : Option Nat}
    (left : Improves first middle) (right : Improves middle last) : Improves first last := by
  intro size present
  obtain ⟨mid, hm, bound⟩ := left size present
  obtain ⟨small, hs, bound'⟩ := right mid hm
  exact ⟨small, hs, Nat.le_trans bound' bound⟩

/-- Pointwise refinements compose. -/
theorem refines_trans {first middle last : State → Option Nat}
    (left : Refines first middle) (right : Refines middle last) : Refines first last :=
  fun state => improves_trans (left state) (right state)

/-- Taking the minimum preserves or improves the first candidate. -/
theorem best_improves_left (left right : Option Nat) : Improves left (best left right) := by
  intro size present
  subst left
  cases right with
  | none => exact ⟨size, rfl, Nat.le_refl _⟩
  | some other => exact ⟨min size other, rfl, Nat.min_le_left _ _⟩

/-- Taking the minimum preserves or improves the second candidate. -/
theorem best_improves_right (left right : Option Nat) : Improves right (best left right) := by
  intro size present
  subst right
  cases left with
  | none => exact ⟨size, rfl, Nat.le_refl _⟩
  | some other => exact ⟨min other size, rfl, Nat.min_le_right _ _⟩

/-- A minimum comes from one of its candidates. -/
theorem best_source (left right : Option Nat) (size : Nat)
    (present : best left right = some size) : left = some size ∨ right = some size := by
  cases left with
  | none => exact Or.inr present
  | some left =>
      cases right with
      | none => exact Or.inl present
      | some right =>
          simp only [best, Option.some.injEq] at present
          by_cases order : left ≤ right
          · exact Or.inl (congrArg some ((Nat.min_eq_left order).symm.trans present))
          · exact Or.inr (congrArg some ((Nat.min_eq_right (by omega)).symm.trans present))

/-- A row update refines its input table. -/
theorem relax_refines [DecidableEq State] (automaton : Automaton State Symbol)
    (state : State) (known : State → Option Nat) : Refines known (relax automaton state known) := by
  intro target
  by_cases same : target = state
  · subst target
    simpa [relax] using best_improves_left (known state) _
  · simpa [relax, same] using improves_refl (known target)

/-- A full asynchronous sweep refines its input table. -/
theorem sweep_refines [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (known : State → Option Nat) : Refines known (sweep automaton states known) := by
  induction states with
  | nil => exact fun state => improves_refl _
  | cons state states ih =>
      exact refines_trans ih (relax_refines automaton state _)

/-- Every stored finite value has an accepting witness of that exact size. -/
def Sound (automaton : Automaton State Symbol) (known : State → Option Nat) : Prop :=
  ∀ state size, known state = some size →
    ∃ term, Accepts automaton state term ∧ nodeSize term = size

/-- Finite child sums have an accepted forest with the same size. -/
theorem childSum_sound (automaton : Automaton State Symbol) (known : State → Option Nat)
    (sound : Sound automaton known) (states : List State) (size : Nat)
    (present : childSum known states = some size) :
    ∃ terms, All₂ (Accepts automaton) states terms ∧ forestSize terms = size := by
  induction states generalizing size with
  | nil =>
      have same : size = 0 := by simpa [childSum] using present.symm
      exact ⟨[], .nil, same.symm⟩
  | cons state states ih =>
      cases head : known state with
      | none => simp [childSum, head] at present
      | some first =>
          cases tail : childSum known states with
          | none => simp [childSum, head, tail] at present
          | some rest =>
              have same : first + rest = size := by simpa [childSum, head, tail] using present
              obtain ⟨term, accepted, exactSize⟩ := sound state first head
              obtain ⟨terms, acceptedRest, exactRest⟩ := ih rest tail
              refine ⟨term :: terms, .cons accepted acceptedRest, ?_⟩
              change nodeSize term + forestSize terms = size
              rw [exactSize, exactRest, same]

/-- An outgoing minimum comes from an outgoing transition. -/
theorem rowMinimum_source (known : State → Option Nat) (edges : List (Edge State Symbol))
    (size : Nat) (present : rowMinimum known edges = some size) :
    ∃ edge, edge ∈ edges ∧ edgeMinimum known edge = some size := by
  induction edges with
  | nil => cases present
  | cons edge edges ih =>
      rcases best_source _ _ _ present with here | there
      · exact ⟨edge, by simp, here⟩
      · obtain ⟨other, member, value⟩ := ih there
        exact ⟨other, by simp [member], value⟩

/-- The outgoing minimum improves every available transition candidate. -/
theorem rowMinimum_improves_member (known : State → Option Nat)
    (edges : List (Edge State Symbol)) (edge : Edge State Symbol) (member : edge ∈ edges) :
    Improves (edgeMinimum known edge) (rowMinimum known edges) := by
  induction edges with
  | nil => simp at member
  | cons first edges ih =>
      rcases List.mem_cons.mp member with same | member
      · subst edge
        exact best_improves_left _ _
      · exact improves_trans (ih member) (best_improves_right _ _)

/-- Every finite row candidate has an accepted witness for a plain automaton. -/
theorem rowMinimum_sound (automaton : Automaton State Symbol) (plain : Decoder.Plain automaton)
    (known : State → Option Nat) (sound : Sound automaton known) (state : State) (size : Nat)
    (present : rowMinimum known (automaton state) = some size) :
    ∃ term, Accepts automaton state term ∧ nodeSize term = size := by
  obtain ⟨edge, member, candidate⟩ := rowMinimum_source known _ size present
  cases children : childSum known edge.children with
  | none => simp [edgeMinimum, children] at candidate
  | some count =>
      have same : count + 1 = size := by simpa [edgeMinimum, children] using candidate
      obtain ⟨terms, runs, exactSize⟩ := childSum_sound automaton known sound _ count children
      refine ⟨.node edge.label terms, .node edge terms member runs (plain state edge member _), ?_⟩
      rw [nodeSize]
      change forestSize terms + 1 = size
      rw [exactSize, same]

/-- An asynchronous row update preserves exact accepted witnesses. -/
theorem relax_sound [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (state : State) (known : State → Option Nat)
    (sound : Sound automaton known) : Sound automaton (relax automaton state known) := by
  intro target size present
  by_cases same : target = state
  · subst target
    simp only [relax, ite_true] at present
    rcases best_source _ _ _ present with old | candidate
    · exact sound state size old
    · exact rowMinimum_sound automaton plain known sound state size candidate
  · exact sound target size (by simpa [relax, same] using present)

/-- A sweep preserves exact accepted witnesses. -/
theorem sweep_sound [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (known : State → Option Nat)
    (sound : Sound automaton known) : Sound automaton (sweep automaton states known) := by
  induction states with
  | nil => exact sound
  | cons state states ih => exact relax_sound automaton plain state _ ih

/-- Two mutually improving optional sizes are equal. -/
theorem improves_antisymm (left right : Option Nat)
    (forward : Improves left right) (backward : Improves right left) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some size => obtain ⟨_, impossible, _⟩ := backward size rfl; cases impossible
  | some size =>
      obtain ⟨small, same, bound⟩ := forward size rfl
      subst right
      obtain ⟨_, equal, bound'⟩ := backward small rfl
      simp only [Option.some.injEq] at equal
      subst_vars
      congr 1
      omega

/-- Two mutually refining tables are equal. -/
theorem refines_antisymm (left right : State → Option Nat)
    (forward : Refines left right) (backward : Refines right left) : left = right := by
  funext state
  exact improves_antisymm _ _ (forward state) (backward state)

/-- A stable asynchronous sweep makes every visited row stable. -/
theorem sweep_fixed_rows [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (known : State → Option Nat) (fixed : sweep automaton states known = known)
    (state : State) (member : state ∈ states) : relax automaton state known = known := by
  induction states with
  | nil => simp at member
  | cons first states ih =>
      have middle : sweep automaton states known = known := by
        apply refines_antisymm
        · have improves := relax_refines automaton first (sweep automaton states known)
          change Refines (sweep automaton states known) (sweep automaton (first :: states) known) at improves
          rw [fixed] at improves
          exact improves
        · exact sweep_refines automaton states known
      rcases List.mem_cons.mp member with same | member
      · subst state
        change relax automaton first (sweep automaton states known) = known at fixed
        rw [middle] at fixed
        exact fixed
      · exact ih middle member

/-- Stable rows improve every outgoing transition candidate. -/
theorem fixed_improves_edge [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (known : State → Option Nat)
    (fixed : sweep automaton states known = known) (state : State) (edge : Edge State Symbol)
    (member : edge ∈ automaton state) : Improves (edgeMinimum known edge) (known state) := by
  have stable := congrFun (sweep_fixed_rows automaton states known fixed state (complete state)) state
  have result := improves_trans (rowMinimum_improves_member known _ edge member)
    (best_improves_right (known state) _)
  simp only [relax, ite_true] at stable
  rw [← stable]
  exact result

/-- Every accepted term bounds the computed value at any stable table. -/
theorem fixed_complete [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (known : State → Option Nat)
    (fixed : sweep automaton states known = known) {state : State} {term : Term Symbol}
    (accepted : Accepts automaton state term) :
    ∃ size, known state = some size ∧ size ≤ nodeSize term := by
  induction accepted using Accepts.rec
    (motive_2 := fun children terms _ =>
      ∃ size, childSum known children = some size ∧ size ≤ forestSize terms) with
  | @node state edge terms member runs guard ih =>
      obtain ⟨size, present, bound⟩ := ih
      have edgePresent : edgeMinimum known edge = some (size + 1) := by
        simp [edgeMinimum, present]
      obtain ⟨small, value, less⟩ := fixed_improves_edge automaton states complete known fixed
        state edge member (size + 1) edgePresent
      refine ⟨small, value, ?_⟩
      rw [nodeSize]
      exact Nat.le_trans less (Nat.add_le_add_right bound 1)
  | nil => exact ⟨0, rfl, Nat.le_refl _⟩
  | cons child children ih ihs =>
      obtain ⟨size, present, bound⟩ := ih
      obtain ⟨rest, presentRest, boundRest⟩ := ihs
      refine ⟨size + rest, ?_, Nat.add_le_add bound boundRest⟩
      simp [childSum, present, presentRest]

/-- Count states that have no finite entry. Repeated list entries are counted separately. -/
def missing (states : List State) (known : State → Option Nat) : Nat :=
  states.foldr (fun state count => if (known state).isNone then count + 1 else count) 0

/-- Add the stored sizes. Unknown entries contribute zero. -/
def total (states : List State) (known : State → Option Nat) : Nat :=
  states.foldr (fun state size => (known state).getD 0 + size) 0

/-- Split the missing count at the first state. -/
theorem missing_cons (state : State) (states : List State) (known : State → Option Nat) :
    missing (state :: states) known = if (known state).isNone then missing states known + 1
      else missing states known := rfl

/-- Split the stored sum at the first state. -/
theorem total_cons (state : State) (states : List State) (known : State → Option Nat) :
    total (state :: states) known = (known state).getD 0 + total states known := rfl

/-- Refinement decreases the missing count, then the sum. Equal measures force equal entries. -/
theorem measure_refines (states : List State) (before after : State → Option Nat)
    (refines : Refines before after) :
    missing states after ≤ missing states before ∧
    (missing states after = missing states before →
      total states after ≤ total states before ∧
      (total states after = total states before → ∀ state, state ∈ states → before state = after state)) := by
  induction states with
  | nil => simp [missing, total]
  | cons state states ih =>
      have head := refines state
      cases hb : before state with
      | none =>
          cases ha : after state with
          | none =>
              simp only [missing_cons, total_cons, hb, ha, Option.isNone_none,
                ite_true, Option.getD_none, Nat.zero_add]
              refine ⟨by omega, ?_⟩
              intro same
              have tailSame : missing states after = missing states before := by omega
              obtain ⟨weak, equal⟩ := ih.2 tailSame
              refine ⟨weak, ?_⟩
              intro sameTotal target member
              rcases List.mem_cons.mp member with same | member
              · subst target; rw [hb, ha]
              · exact equal sameTotal target member
          | some size =>
              simp only [missing_cons, total_cons, hb, ha, Option.isNone_none,
                Option.isNone_some, Bool.false_eq_true, ite_true, ite_false,
                Option.getD_none, Option.getD_some, Nat.zero_add]
              exact ⟨by omega, by omega⟩
      | some size =>
          obtain ⟨small, ha, bound⟩ := head size hb
          simp only [missing_cons, total_cons, hb, ha, Option.isNone_some,
            Bool.false_eq_true, ite_false, Option.getD_some]
          refine ⟨ih.1, ?_⟩
          intro same
          obtain ⟨weak, equal⟩ := ih.2 same
          refine ⟨Nat.add_le_add bound weak, ?_⟩
          intro sameTotal target member
          have headSame : size = small := by omega
          have tailSame : total states after = total states before := by omega
          rcases List.mem_cons.mp member with same | member
          · subst target; rw [hb, ha, headSame]
          · exact equal tailSame target member

/-- Every unequal sweep strictly decreases one of two natural measures. -/
theorem sweep_decreases [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (known : State → Option Nat)
    (different : sweep automaton states known ≠ known) :
    missing states (sweep automaton states known) < missing states known ∨
    (missing states (sweep automaton states known) = missing states known ∧
      total states (sweep automaton states known) < total states known) := by
  have measure := measure_refines states known (sweep automaton states known)
    (sweep_refines automaton states known)
  by_cases sameMissing : missing states (sweep automaton states known) = missing states known
  · right
    refine ⟨sameMissing, ?_⟩
    obtain ⟨weak, equal⟩ := measure.2 sameMissing
    have unequal : total states (sweep automaton states known) ≠ total states known := by
      intro sameTotal
      apply different
      funext state
      exact (equal sameTotal state (complete state)).symm
    omega
  · exact Or.inl (by omega)

/-- Compare finite tables by their complete list of keys. -/
def sameTable [DecidableEq State] (states : List State)
    (left right : State → Option Nat) : Bool :=
  states.all (fun state => decide (left state = right state))

/-- Finite table comparison is extensional equality on a complete state list. -/
theorem sameTable_correct [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (left right : State → Option Nat) :
    sameTable states left right = true ↔ left = right := by
  constructor
  · intro same
    funext state
    exact of_decide_eq_true (List.all_eq_true.mp same state (complete state))
  · intro same
    subst right
    simp [sameTable]

/-- Repeat asynchronous sweeps until the finite table stops changing. -/
def converge [DecidableEq State] (automaton : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states) (known : State → Option Nat) : State → Option Nat :=
  let next := sweep automaton states known
  if _stable : sameTable states next known = true then known
  else converge automaton states complete next
termination_by (missing states known, total states known)
decreasing_by
  have different : sweep automaton states known ≠ known := by
    intro equal
    exact _stable ((sameTable_correct states complete _ _).mpr equal)
  rcases sweep_decreases automaton states complete known different with fewer | ⟨same, smaller⟩
  · exact Prod.Lex.left _ _ fewer
  · rw [same]
    exact Prod.Lex.right _ smaller

/-- Convergence returns a stable table. -/
theorem converge_fixed [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (known : State → Option Nat) :
    sweep automaton states (converge automaton states complete known) =
      converge automaton states complete known := by
  induction known using converge.induct automaton states complete with
  | case1 known next stable =>
      dsimp only [next] at stable
      rw [converge.eq_def]
      simp only [dite_eq_left stable]
      exact (sameTable_correct states complete _ _).mp stable
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih

/-- Convergence preserves exact accepted witnesses. -/
theorem converge_sound [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (known : State → Option Nat) (sound : Sound automaton known) :
    Sound automaton (converge automaton states complete known) := by
  induction known using converge.induct automaton states complete with
  | case1 known next stable =>
      dsimp only [next] at stable
      rw [converge.eq_def]
      simpa only [dite_eq_left stable] using sound
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      rw [converge.eq_def]
      simp only [dite_eq_right unstable]
      exact ih (sweep_sound automaton plain states known sound)

/-- Execute a specified number of asynchronous sweeps. -/
def sweeps [DecidableEq State] (automaton : Automaton State Symbol) (states : List State) :
    Nat → (State → Option Nat) → State → Option Nat
  | 0, known => known
  | fuel + 1, known => sweeps automaton states fuel (sweep automaton states known)

/-- The terminating computation is reached after finitely many ordinary sweeps. -/
theorem converge_reached [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) (known : State → Option Nat) :
    ∃ fuel, sweeps automaton states fuel known = converge automaton states complete known := by
  induction known using converge.induct automaton states complete with
  | case1 known next stable =>
      dsimp only [next] at stable
      refine ⟨0, ?_⟩
      rw [converge.eq_def]
      simp only [dite_eq_left stable, sweeps]
  | case2 known next unstable ih =>
      dsimp only [next] at unstable
      obtain ⟨fuel, same⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [converge.eq_def]
      simp only [dite_eq_right unstable, sweeps]
      exact same

/-- Compute minimum sizes from the empty finite table. -/
def minimumSizes [DecidableEq State] (automaton : Automaton State Symbol) (states : List State)
    (complete : ∀ state, state ∈ states) : State → Option Nat :=
  converge automaton states complete (fun _ => none)

/-- The computed table is stable. -/
theorem minimumSizes_fixed [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) :
    sweep automaton states (minimumSizes automaton states complete) =
      minimumSizes automaton states complete :=
  converge_fixed automaton states complete _

/-- Every computed minimum has an accepted term of exactly that size. -/
theorem minimumSizes_sound [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states) :
    Sound automaton (minimumSizes automaton states complete) := by
  apply converge_sound automaton plain states complete
  intro state size impossible
  cases impossible

/-- Every accepted term has at least the computed minimum number of nodes. -/
theorem minimumSizes_complete [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) {state : State} {term : Term Symbol}
    (accepted : Accepts automaton state term) :
    ∃ size, minimumSizes automaton states complete state = some size ∧ size ≤ nodeSize term :=
  fixed_complete automaton states complete _ (minimumSizes_fixed automaton states complete) accepted

/-- A finite entry is exactly the minimum accepted node count. -/
theorem minimumSizes_correct [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) (size : Nat) :
    minimumSizes automaton states complete state = some size ↔
      (∃ term, Accepts automaton state term ∧ nodeSize term = size) ∧
      (∀ term, Accepts automaton state term → size ≤ nodeSize term) := by
  constructor
  · intro present
    refine ⟨minimumSizes_sound automaton plain states complete state size present, ?_⟩
    intro term accepted
    obtain ⟨small, computed, bound⟩ := minimumSizes_complete automaton states complete accepted
    have same : small = size := Option.some.inj (computed.symm.trans present)
    simpa only [same] using bound
  · rintro ⟨⟨term, accepted, exactSize⟩, minimal⟩
    obtain ⟨small, computed, bound⟩ := minimumSizes_complete automaton states complete accepted
    obtain ⟨witness, witnessAccepted, witnessSize⟩ :=
      minimumSizes_sound automaton plain states complete state small computed
    have reverse := minimal witness witnessAccepted
    have same : small = size := by omega
    simpa only [same] using computed

/-- A missing entry means that the state has no finite accepted term. -/
theorem minimumSizes_none_iff [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) : minimumSizes automaton states complete state = none ↔
      ∀ term, ¬Accepts automaton state term := by
  constructor
  · intro absent term accepted
    obtain ⟨size, present, _⟩ := minimumSizes_complete automaton states complete accepted
    rw [absent] at present
    cases present
  · intro empty
    cases present : minimumSizes automaton states complete state with
    | none => rfl
    | some size =>
        obtain ⟨term, accepted, _⟩ := minimumSizes_sound automaton plain states complete state size present
        exact False.elim (empty term accepted)

/-- The mathematical result does not depend on row order or duplicate key visits. -/
theorem minimumSizes_order_independent [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (left right : List State)
    (leftComplete : ∀ state, state ∈ left) (rightComplete : ∀ state, state ∈ right) :
    minimumSizes automaton left leftComplete = minimumSizes automaton right rightComplete := by
  funext state
  cases present : minimumSizes automaton left leftComplete state with
  | none =>
      exact ((minimumSizes_none_iff automaton plain right rightComplete state).mpr
        ((minimumSizes_none_iff automaton plain left leftComplete state).mp present)).symm
  | some size =>
      exact ((minimumSizes_correct automaton plain right rightComplete state size).mpr
        ((minimumSizes_correct automaton plain left leftComplete state size).mp present)).symm

/-- A finite minimum is positive because every term includes its root. -/
theorem minimumSizes_positive [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) (size : Nat) (present : minimumSizes automaton states complete state = some size) :
    0 < size := by
  obtain ⟨term, _, exactSize⟩ := minimumSizes_sound automaton plain states complete state size present
  exact exactSize ▸ nodeSize_pos term

/-- Omitting size classes below the computed minimum removes no runs. -/
theorem count_below_minimum [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) (minimum size : Nat)
    (present : minimumSizes automaton states complete state = some minimum) (smaller : size < minimum) :
    countAt automaton size state = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro positive
  obtain ⟨term, accepted, exactSize⟩ := (countAt_positive_iff automaton plain size state).mp positive
  have bound := ((minimumSizes_correct automaton plain states complete state minimum).mp present).2
    term accepted
  omega

/-- The minimum class contains at least one accepted run. -/
theorem count_at_minimum_positive [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) (size : Nat) (present : minimumSizes automaton states complete state = some size) :
    0 < countAt automaton size state :=
  (countAt_positive_iff automaton plain size state).mpr
    (minimumSizes_sound automaton plain states complete state size present)

/-- An absent state has only zero count classes, and conversely. -/
theorem minimumSizes_none_iff_zero_counts [DecidableEq State] (automaton : Automaton State Symbol)
    (plain : Decoder.Plain automaton) (states : List State) (complete : ∀ state, state ∈ states)
    (state : State) : minimumSizes automaton states complete state = none ↔
      ∀ size, countAt automaton size state = 0 := by
  rw [minimumSizes_none_iff automaton plain states complete state]
  simpa only [not_exists] using empty_iff_zero_classes automaton plain state

/-- The finite sweeps starting from empty always reach a stable table. -/
theorem minimumSizes_terminates [DecidableEq State] (automaton : Automaton State Symbol)
    (states : List State) (complete : ∀ state, state ∈ states) :
    ∃ fuel, sweep automaton states (sweeps automaton states fuel (fun _ => none)) =
      sweeps automaton states fuel (fun _ => none) := by
  obtain ⟨fuel, reached⟩ := converge_reached automaton states complete (fun _ => none)
  exact ⟨fuel, by rw [reached]; exact minimumSizes_fixed automaton states complete⟩

end MicroCFTA.MinimumSize




