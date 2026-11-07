import MicroCFTA.SourceSizedRootQueryLaws
import MicroCFTA.GraphTrim

/-!
# Structural trimming preserves every root run position

Raw size enumeration does not inspect guards. Erasing guards leaves its
ordered sequence unchanged. A structurally unproductive child has no raw
run at any size. Structural trimming therefore removes only empty branches.

The resulting root enumeration has the same order and multiplicity as the
original enumeration. Root-local uniqueness of the trimmed graph transfers
to the original graph. No original global uniqueness is assumed.

The finite state inventory is complete for this graph calculation. Explicit
source tables must derive that inventory from their actual finite map keys.
This module does not prove native storage or execution resource bounds.
-/
namespace MicroCFTA.SourceSizedTrimRunClasses
open Language RecursiveSize Productivity SourceSizedCandidates

private theorem enumerate_candidates {State Symbol : Type} (rows : Automaton State Symbol)
    (remaining : Nat) (state : State) :
    RecursiveSize.enumerate rows (remaining + 1) state =
      (rows state).flatMap fun edge =>
        candidates (fun child childSize => RecursiveSize.enumerate rows childSize child)
          edge.label edge.children (remaining + 1) := by
  rw [TablePosition.enumerate_rootForests]
  apply TablePosition.flatMap_congr
  intro edge _
  rw [candidates_succ, TablePosition.rootForests_eq, TablePosition.rooted]

private theorem erased_plain {State Symbol : Type} (rows : Automaton State Symbol) :
    Decoder.Plain (eraseGuards rows) := by
  intro state edge member term
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem flatMap_filter_eq {A B : Type} (items : List A) (keep : A → Bool)
    (generate : A → List B) (empty : ∀ item ∈ items, keep item = false → generate item = []) :
    (items.filter keep).flatMap generate = items.flatMap generate := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      have tail := ih (fun value present => empty value (List.mem_cons_of_mem item present))
      by_cases selected : keep item = true
      · rw [List.filter_cons, ite_eq_left selected, List.flatMap_cons, List.flatMap_cons, tail]
      · rw [List.filter_cons, ite_eq_right selected, List.flatMap_cons,
          empty item (by simp) (Bool.eq_false_iff.mpr selected), List.nil_append]
        exact tail

/-- Guard erasure preserves the order and multiplicity of every raw size class. -/
theorem enumerate_eraseGuards {State Symbol : Type} (rows : Automaton State Symbol)
    (size : Nat) (state : State) :
    RecursiveSize.enumerate (eraseGuards rows) size state = RecursiveSize.enumerate rows size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [enumerate_zero, enumerate_zero]
      | succ remaining =>
          rw [enumerate_candidates, enumerate_candidates]
          simp only [eraseGuards, List.flatMap_map]
          apply TablePosition.flatMap_congr
          intro edge _
          apply candidates_congr
          intro child childSize smaller
          exact ih childSize smaller child

/-- An unproductive original state has no raw run in any subgraph at any size. -/
theorem unproductive_enumerate {State Symbol : Type}
    (states : List State) (complete : ∀ state, state ∈ states)
    (original part : Automaton State Symbol)
    (subset : ∀ state edge, edge ∈ part state → edge ∈ original state)
    (state : State) (empty : productive states original state ≠ true) (size : Nat) :
    RecursiveSize.enumerate part size state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro term present
  have erasedMember : term ∈ RecursiveSize.enumerate (eraseGuards part) size state := by
    rw [enumerate_eraseGuards]
    exact present
  have accepted := ((RecursiveSize.mem_enumerate_iff (eraseGuards part) (erased_plain part)
    size state term).mp erasedMember).1
  have erasedSubset : ∀ state edge, edge ∈ eraseGuards part state → edge ∈ eraseGuards original state := by
    intro state edge member
    obtain ⟨raw, stored, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨raw, subset state raw stored, rfl⟩
  have source := FTAValidation.accepts_transfer (eraseGuards part) (eraseGuards original) erasedSubset accepted
  exact empty ((productive_correct states complete original state).mpr ⟨term, source⟩)

/-- Productivity filtering removes only empty branches from each raw run class. -/
theorem live_enumerate {State Symbol : Type}
    (states : List State) (complete : ∀ state, state ∈ states)
    (rows : Automaton State Symbol) (size : Nat) (state : State) :
    RecursiveSize.enumerate (GraphTrim.live states rows) size state =
      RecursiveSize.enumerate rows size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [enumerate_zero, enumerate_zero]
      | succ remaining =>
          by_cases marked : productive states rows state = true
          · rw [enumerate_candidates, enumerate_candidates]
            have liveRows : GraphTrim.live states rows state =
                (rows state).filter (fun edge => edge.children.all (productive states rows)) := by
              rw [GraphTrim.live, ite_eq_left marked]
            rw [liveRows]
            have sameCandidates :
                ((rows state).filter (fun edge => edge.children.all (productive states rows))).flatMap
                  (fun edge => candidates
                    (fun child childSize => RecursiveSize.enumerate (GraphTrim.live states rows) childSize child)
                    edge.label edge.children (remaining + 1)) =
                ((rows state).filter (fun edge => edge.children.all (productive states rows))).flatMap
                  (fun edge => candidates
                    (fun child childSize => RecursiveSize.enumerate rows childSize child)
                    edge.label edge.children (remaining + 1)) := by
              apply TablePosition.flatMap_congr
              intro edge _
              apply candidates_congr
              intro child childSize smaller
              exact ih childSize smaller child
            rw [sameCandidates]
            apply flatMap_filter_eq
            intro edge _ rejected
            obtain ⟨child, present, empty⟩ := List.all_eq_false.mp rejected
            exact candidates_nil_of_child _ _ _ child present
              (unproductive_enumerate states complete rows rows (fun _ _ stored => stored) child empty)
              (remaining + 1)
          · rw [unproductive_enumerate states complete rows (GraphTrim.live states rows)
                (GraphTrim.live_subset states rows) state marked,
              unproductive_enumerate states complete rows rows (fun _ _ stored => stored) state marked]

/-- Reachability filtering preserves every raw class at each reached live state. -/
theorem reachable_enumerate {State Symbol : Type} [DecidableEq State]
    (states : List State) (complete : ∀ state, state ∈ states)
    (rows : Automaton State Symbol) (root : State) (size : Nat) (state : State)
    (reached : Reachable (successors (GraphTrim.live states rows)) [root] state) :
    RecursiveSize.enumerate (GraphTrim.trim states rows root) size state =
      RecursiveSize.enumerate (GraphTrim.live states rows) size state := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [enumerate_zero, enumerate_zero]
      | succ remaining =>
          rw [enumerate_candidates, enumerate_candidates]
          have bit := (reachClosure_correct states complete _ _ state).mpr reached
          have sameRows : GraphTrim.trim states rows root state = GraphTrim.live states rows state := by
            rw [GraphTrim.trim, ite_eq_left bit]
          rw [sameRows]
          apply TablePosition.flatMap_congr
          intro edge member
          apply candidates_congr_children
          intro child present childSize smaller
          exact ih childSize smaller child
            (reachable_child (GraphTrim.live states rows) [root] reached member present)

/-- Structural trimming preserves the complete original root sequence, including repeated runs. -/
theorem trim_enumerate {State Symbol : Type} [DecidableEq State]
    (states : List State) (complete : ∀ state, state ∈ states)
    (rows : Automaton State Symbol) (root : State) (size : Nat) :
    RecursiveSize.enumerate (GraphTrim.trim states rows root) size root =
      RecursiveSize.enumerate rows size root :=
  (reachable_enumerate states complete rows root size root (.seed (by simp))).trans
    (live_enumerate states complete rows size root)

/-- Root-only uniqueness after actual trimming gives root-only uniqueness before trimming. -/
theorem root_unique_of_trim {State Symbol : Type} [DecidableEq State]
    (states : List State) (complete : ∀ state, state ∈ states)
    (rows : Automaton State Symbol) (root : State)
    (unique : ∀ size, (RecursiveSize.enumerate (GraphTrim.trim states rows root) size root).Nodup) :
    ∀ size, (RecursiveSize.enumerate rows size root).Nodup := by
  intro size
  rw [← trim_enumerate states complete rows root size]
  exact unique size

/-- A plain original graph needs only its trimmed root's uniqueness for exact optimized queries. -/
theorem optimized_exact {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
    (states : List State) (complete : ∀ state, state ∈ states)
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State)
    (unique : ∀ size, (RecursiveSize.enumerate (GraphTrim.trim states rows root) size root).Nodup)
    (language : Term Symbol → Prop) (correct : ∀ term, Accepts rows root term ↔ language term) :
    SourceSizedApiLaws.Exact (SourceSizedDispatcher.optimizedApi rows root) language :=
  SourceSizedRootQueryLaws.optimized_exact rows plain root
    (root_unique_of_trim states complete rows root unique) language correct

end MicroCFTA.SourceSizedTrimRunClasses
