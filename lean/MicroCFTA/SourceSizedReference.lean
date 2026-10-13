import MicroCFTA.SourceSizedCandidates
import MicroCFTA.DistinctRank
import MicroCFTA.RefinementValidation

/-!
# Finite exact size classes for the reference Sized worker

The input rows retain their source order. A row contains the decision of its
constraint on the complete candidate term. The class keeps each term at its
first occurrence. The recursion reads only smaller sizes, including when
the state graph contains cycles.

Sorting and the constraint interpretation are separate adapters. The class
proof needs no acyclicity, disjointness, pruning, or interned construction.
-/

namespace MicroCFTA.SourceSizedReference

open Language RecursiveSize SourceSizedCandidates

/-- Keep the first occurrence of each value, as the source `nubOrd` does. -/
def nub [DecidableEq α] (values : List α) : List α :=
  RefinementValidation.dedup [] values

/-- Removing repeated terms preserves exact membership. -/
theorem mem_nub [DecidableEq α] (values : List α) (value : α) :
    value ∈ nub values ↔ value ∈ values :=
  RefinementValidation.dedup_new_member values value

/-- First-occurrence removal leaves no duplicate term. -/
theorem nub_nodup [DecidableEq α] (values : List α) : (nub values).Nodup :=
  RefinementValidation.dedup_nodup [] values

/-- The source class worker checks each complete candidate before deduplication. -/
def classOf {State Symbol : Type} [DecidableEq Symbol]
    (classAt : State → Nat → List (Term Symbol)) (rows : List (Edge State Symbol))
    (size : Nat) : List (Term Symbol) :=
  nub (rows.flatMap fun edge =>
    (candidates classAt edge.label edge.children size).filter edge.guard)

/-- Class construction depends only on strictly smaller child classes. -/
theorem classOf_congr {State Symbol : Type} [DecidableEq Symbol]
    (first second : State → Nat → List (Term Symbol)) (rows : List (Edge State Symbol))
    (size : Nat)
    (agree : ∀ state childSize, childSize < size → first state childSize = second state childSize) :
    classOf first rows size = classOf second rows size := by
  unfold classOf
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro edge _
  rw [candidates_congr first second edge.label edge.children size agree]

/-- Construct a finite size class by well-founded node-count recursion. -/
def classes {State Symbol : Type} [DecidableEq Symbol] (A : Automaton State Symbol)
    (size : Nat) (state : State) : List (Term Symbol) :=
  match size with
  | 0 => []
  | remaining + 1 =>
      classOf (fun childState childSize =>
        if _smaller : childSize ≤ remaining then classes A childSize childState else [])
        (A state) (remaining + 1)
termination_by size

/-- The class of size zero is empty. -/
theorem classes_zero {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (state : State) : classes A 0 state = [] := by
  rw [classes]

/-- The finite recurrence satisfies the source lazy table equation exactly. -/
theorem classes_succ {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (remaining : Nat) (state : State) :
    classes A (remaining + 1) state =
      classOf (fun childState childSize => classes A childSize childState)
        (A state) (remaining + 1) := by
  rw [classes]
  apply classOf_congr
  intro childState childSize smaller
  simp only [dite_eq_left (show childSize ≤ remaining by omega)]

/-- Each class contains one copy of every accepted term of its node count. -/
theorem mem_classes_iff {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (size : Nat) (state : State) (term : Term Symbol) :
    term ∈ classes A size state ↔ Accepts A state term ∧ nodeSize term = size := by
  induction size using Nat.strongRecOn generalizing state term with
  | ind size ih =>
      cases size with
      | zero =>
          constructor
          · simp [classes_zero]
          · rintro ⟨_, exactSize⟩
            have positive := nodeSize_pos term
            omega
      | succ remaining =>
          rw [classes_succ, classOf, mem_nub]
          have childExact : ∀ childSize, childSize ≤ remaining → ∀ childState child,
              child ∈ classes A childSize childState ↔
                Accepts A childState child ∧ nodeSize child = childSize := by
            intro childSize smaller childState child
            exact ih childSize (by omega) childState child
          constructor
          · intro member
            obtain ⟨edge, edgeMember, candidateMember⟩ := List.mem_flatMap.mp member
            obtain ⟨candidateMember, guard⟩ := List.mem_filter.mp candidateMember
            obtain ⟨arguments, same, acceptedChildren, exactSize⟩ :=
              (mem_candidates_succ_iff (Accepts A)
                (fun childState childSize => classes A childSize childState)
                remaining childExact edge.label edge.children remaining (Nat.le_refl _) term).mp
                  candidateMember
            subst term
            exact ⟨.node edge arguments edgeMember acceptedChildren guard, exactSize⟩
          · rintro ⟨accepted, exactSize⟩
            cases accepted with
            | node edge arguments edgeMember acceptedChildren guard =>
                apply List.mem_flatMap.mpr
                refine ⟨edge, edgeMember, List.mem_filter.mpr ⟨?_, guard⟩⟩
                exact (mem_candidates_succ_iff (Accepts A)
                  (fun childState childSize => classes A childSize childState)
                  remaining childExact edge.label edge.children remaining (Nat.le_refl _) _).mpr
                    ⟨arguments, rfl, acceptedChildren, exactSize⟩

/-- Every constructed class has no duplicate terms, including ambiguous graphs. -/
theorem classes_nodup {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (size : Nat) (state : State) :
    (classes A size state).Nodup := by
  cases size with
  | zero => simp [classes_zero]
  | succ remaining => rw [classes_succ]; exact nub_nodup _

/-- A finite exact-size class supplies both distinct-term rank inverse laws. -/
def index {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (size : Nat) (state : State) :
    DistinctRank.Index (fun term => Accepts A state term ∧ nodeSize term = size) where
  members := classes A size state
  nodup := classes_nodup A size state
  exact := mem_classes_iff A size state

/-- Deduplication preserves a distinct list disjoint from the seen values. -/
theorem dedup_eq_self [DecidableEq α] (seen values : List α)
    (distinct : values.Nodup) (fresh : ∀ value ∈ values, value ∉ seen) :
    RefinementValidation.dedup seen values = values := by
  induction values generalizing seen with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
      have newHead := fresh first (by simp)
      simp only [RefinementValidation.dedup, newHead, ↓reduceIte]
      rw [ih (first :: seen) restDistinct]
      intro value member present
      rcases List.mem_cons.mp present with same | old
      · subst value; exact absent member
      · exact fresh value (List.mem_cons_of_mem _ member) old

/-- The source nub leaves a distinct sequence in the same order. -/
theorem nub_eq_self [DecidableEq α] (values : List α) (distinct : values.Nodup) :
    nub values = values := dedup_eq_self [] values distinct (by simp)

/-- A plain unambiguous graph has the same class sequence as the count-table recurrence. -/
theorem classes_eq_enumerate {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (plain : Decoder.Plain A)
    (unambiguous : ∀ state size, (RecursiveSize.enumerate A size state).Nodup)
    (size : Nat) (state : State) :
    classes A size state = RecursiveSize.enumerate A size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [classes_zero, enumerate_zero]
      | succ remaining =>
          rw [classes_succ, classOf]
          have same : (A state).flatMap (fun edge =>
              (candidates (fun childState childSize => classes A childSize childState)
                edge.label edge.children (remaining + 1)).filter edge.guard) =
              RecursiveSize.enumerate A (remaining + 1) state := by
            rw [RecursiveSize.enumerate]
            apply congrArg List.flatten
            apply List.map_congr_left
            intro edge member
            rw [List.filter_eq_self.mpr (fun term _ => plain state edge member term)]
            rw [candidates_congr
              (fun childState childSize => classes A childSize childState)
              (fun childState childSize =>
                if _smaller : childSize ≤ remaining then RecursiveSize.enumerate A childSize childState else [])
              edge.label edge.children (remaining + 1)]
            · exact candidates_succ _ _ _ _
            · intro childState childSize smaller
              rw [dite_eq_left (show childSize ≤ remaining by omega)]
              exact ih childSize smaller childState
          rw [same, nub_eq_self _ (unambiguous state (remaining + 1))]

/-- The source table equations determine exactly one class sequence. -/
theorem classes_unique {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (table : Nat → State → List (Term Symbol))
    (zero : ∀ state, table 0 state = [])
    (step : ∀ remaining state, table (remaining + 1) state =
      classOf (fun childState childSize => table childSize childState)
        (A state) (remaining + 1)) :
    ∀ size state, table size state = classes A size state := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro state
      cases size with
      | zero => rw [zero, classes_zero]
      | succ remaining =>
          rw [step, classes_succ]
          apply classOf_congr
          intro childState childSize smaller
          exact ih childSize smaller childState

/-- A finite class evaluation records every possible smaller child query.
The bound counts nested class evaluations, not primitive comparison costs. -/
inductive ClassEvaluation {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) : Nat → Nat → State → List (Term Symbol) → Prop where
  | zero (fuel : Nat) (state : State) : ClassEvaluation A (fuel + 1) 0 state []
  | step (fuel remaining : Nat) (state : State)
      (childClasses : State → Nat → List (Term Symbol))
      (finished : ∀ edge ∈ A state, ∀ child ∈ edge.children, ∀ childSize,
        childSize ≤ remaining → ClassEvaluation A fuel childSize child (childClasses child childSize)) :
      ClassEvaluation A (fuel + 1) (remaining + 1) state
        (classOf childClasses (A state) (remaining + 1))

/-- Every class has a finite evaluation, irrespective of graph cycles. -/
theorem classes_evaluation {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (fuel size : Nat) (within : size ≤ fuel) (state : State) :
    ClassEvaluation A (fuel + 1) size state (classes A size state) := by
  induction fuel generalizing size state with
  | zero =>
      have zero : size = 0 := by omega
      subst size
      rw [classes_zero]
      exact .zero 0 state
  | succ fuel ih =>
      cases size with
      | zero => rw [classes_zero]; exact .zero (fuel + 1) state
      | succ remaining =>
          rw [classes_succ]
          apply ClassEvaluation.step
          intro edge member child childMember childSize smaller
          exact ih childSize (by omega) child

/-- The requested node count plus one bounds the nested class evaluations. -/
theorem classes_evaluation_bound {State Symbol : Type} [DecidableEq Symbol]
    (A : Automaton State Symbol) (size : Nat) (state : State) :
    ClassEvaluation A (size + 1) size state (classes A size state) :=
  classes_evaluation A size size (Nat.le_refl _) state

end MicroCFTA.SourceSizedReference
