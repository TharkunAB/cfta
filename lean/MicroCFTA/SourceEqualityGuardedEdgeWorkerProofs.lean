import MicroCFTA.SourceEqualityGuardedEdgeWorker

/-!
# Guarded-edge function and graph agreement

Every complete graph derives six stable stage bounds. All larger tuples
retain the exact edge and full native state. Successful bounded workers
recover the graph at the actual reached native word checks.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeWorkerProofs
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityGuardedEdgeGraph
open SourceEqualityGuardedEdgeWorker
variable {Formula : Type}
local notation "Symbol" => Label Formula
local notation "Guard" => Constraint Formula
variable [DecidableEq (Label Formula)] [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))] {width : Nat}
variable (unconstrained : Value (Label Formula) (Constraint Formula) → Bool) (emptyGuard : Constraint Formula)
variable (conjoin : Constraint Formula → Constraint Formula → Constraint Formula) (clear : Constraint Formula → Bool) (top : Constraint Formula)

/-- Each complete edge graph derives a finite stable result for its actual source entry. -/
theorem stable {edge inherited before result after}
    (trace : Graph unconstrained emptyGuard conjoin clear top edge inherited (before : NativeState width Symbol Guard) result after) :
    StableRun (fun g e p h c n => SourceEqualityGuardedEdgeWorker.run unconstrained emptyGuard conjoin clear top g e p h c n edge inherited before) (.ok result) after := by
  cases trace with
  | done physical pass =>
      obtain ⟨g, e, p, h, c, n, complete⟩ := SourceEqualityOnePassAPI.stable unconstrained emptyGuard conjoin clear top pass
      refine ⟨g, e, p, h, c, n, ?_⟩
      intro gg ee pp hh cc nn eg ee' ep eh ec en
      simp only [SourceEqualityGuardedEdgeWorker.run, physical, complete gg ee pp hh cc nn eg ee' ep eh ec en, finish]

/-- Actual bounded parent-array entries retain the same stable complete edge at all sufficient work bounds. -/
theorem array_stable {edge inherited before result after}
    (trace : Graph unconstrained emptyGuard conjoin clear top edge inherited (before : NativeState width Symbol Guard) result after) :
    ∃ arrayBound, ∀ work, arrayBound ≤ work →
      StableRun (fun g e p h c n => runArray unconstrained emptyGuard conjoin clear top work g e p h c n edge inherited before) (.ok result) after := by
  cases trace with
  | done physical pass =>
      obtain ⟨bound, actual⟩ := SourceEqualityOnePassAPI.array_stable unconstrained emptyGuard conjoin clear top pass
      refine ⟨bound, ?_⟩
      intro work enough
      obtain ⟨g, e, p, h, c, n, complete⟩ := actual work enough
      refine ⟨g, e, p, h, c, n, ?_⟩
      intro gg ee pp hh cc nn eg ee' ep eh ec en
      simp only [runArray, physical, complete gg ee pp hh cc nn eg ee' ep eh ec en, finish]

/-- Every successful bounded edge worker has the complete source graph at its actual range checks. -/
theorem graph (g e p h c n : Nat) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (before : NativeState width Symbol Guard) (ranges : Ranges unconstrained emptyGuard conjoin clear top edge inherited before)
    (result : EdgeValue Symbol Guard) (after : NativeState width Symbol Guard)
    (done : SourceEqualityGuardedEdgeWorker.run unconstrained emptyGuard conjoin clear top g e p h c n edge inherited before = .done (.ok result) after) :
    Graph unconstrained emptyGuard conjoin clear top edge inherited before result after := by
  unfold SourceEqualityGuardedEdgeWorker.run at done
  cases physical : SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | error message => simp [physical] at done
  | ok payload =>
      rw [physical] at done
      cases observed : SourceEqualityOnePassWorker.run unconstrained emptyGuard conjoin clear top g e p h c n payload inherited edge.children before with
      | selection observation state | required observation state | narrowing observation => simp [observed, finish] at done
      | done answer middle =>
          cases answer with
          | error message => simp [observed, finish] at done
          | ok results =>
              have pass := (SourceEqualityOnePassAPI.execution_iff unconstrained emptyGuard conjoin clear top payload inherited edge.children before
                (ranges payload physical) (.ok results) middle).mpr ⟨g, e, p, h, c, n, observed⟩
              have equal := Result.done.inj (by simpa only [observed, finish] using done)
              have edgeEq := Except.ok.inj equal.1
              rw [← edgeEq, ← equal.2]
              exact .done physical pass

/-- Complete edge graphs and successful bounded workers agree in both directions. -/
theorem execution_iff (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint)
    (before : NativeState width Symbol Guard) (ranges : Ranges unconstrained emptyGuard conjoin clear top edge inherited before)
    (result : EdgeValue Symbol Guard) (after : NativeState width Symbol Guard) :
    Graph unconstrained emptyGuard conjoin clear top edge inherited before result after ↔
      ∃ g e p h c n, SourceEqualityGuardedEdgeWorker.run unconstrained emptyGuard conjoin clear top g e p h c n edge inherited before = .done (.ok result) after := by
  constructor
  · intro trace
    obtain ⟨g, e, p, h, c, n, complete⟩ := stable unconstrained emptyGuard conjoin clear top trace
    exact ⟨g, e, p, h, c, n, complete g e p h c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨g, e, p, h, c, n, done⟩
    exact graph unconstrained emptyGuard conjoin clear top g e p h c n edge inherited before ranges result after done

/-- Complete edge graphs have one exact rebuilt edge and full native state. -/
theorem unique {edge inherited before first second afterFirst afterSecond}
    (left : Graph unconstrained emptyGuard conjoin clear top edge inherited (before : NativeState width Symbol Guard) first afterFirst)
    (right : Graph unconstrained emptyGuard conjoin clear top edge inherited before second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨a, b, d, f, g, h, one⟩ := stable unconstrained emptyGuard conjoin clear top left
  obtain ⟨aa, bb, dd, ff, gg, hh, two⟩ := stable unconstrained emptyGuard conjoin clear top right
  have same := Result.done.inj ((one (max a aa) (max b bb) (max d dd) (max f ff) (max g gg) (max h hh)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (two (max a aa) (max b bb) (max d dd) (max f ff) (max g gg) (max h hh)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  exact ⟨Except.ok.inj same.1, same.2⟩

end MicroCFTA.SourceEqualityGuardedEdgeWorkerProofs
