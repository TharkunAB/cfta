import MicroCFTA.SourceEqualityOnePassLanguage
import MicroCFTA.SourceEqualityOnePassWorkerProofs

/-!
# Public guarded one-pass execution contracts

The source guards, actual selected stage receipts, and complete worker
agree at checked native word ranges. Complete answers and full native
states are unique. Actual parent-array normalization gives the same entry
at every sufficient array bound and every sufficient stage tuple.
-/
namespace MicroCFTA.SourceEqualityOnePassAPI
open InternedConstructorTemplates SourceEqualityClassFoldGraph SourceEqualityOnePassGraph
open SourceEqualityOnePassWorker SourceEqualityOnePassWorkerProofs

/-- Stable one-pass executions determine one exact answer and complete native state. -/
theorem stable_unique {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard}
    {first second : Except String (List (Value Symbol Guard))} {afterFirst afterSecond : NativeState width Symbol Guard}
    (left : StableRun evaluation first afterFirst) (right : StableRun evaluation second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨a, b, d, f, g, h, one⟩ := left
  obtain ⟨aa, bb, dd, ff, gg, hh, two⟩ := right
  exact Result.done.inj ((one (max a aa) (max b bb) (max d dd) (max f ff) (max g gg) (max h hh)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (two (max a aa) (max b bb) (max d dd) (max f ff) (max g gg) (max h hh)
        (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Checked one-pass source graphs have unique answers and complete native states. -/
theorem unique {checked values before first second afterFirst afterSecond}
    (left : Graph unconstrained emptyGuard conjoin clear top checked values (before : NativeState width Symbol Guard) first afterFirst)
    (right : Graph unconstrained emptyGuard conjoin clear top checked values before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (checked_stable unconstrained emptyGuard conjoin clear top left) (checked_stable unconstrained emptyGuard conjoin clear top right)

/-- Checked source graphs and successful bounded complete workers agree in both directions. -/
theorem checked_execution_iff (checked : Except String SourceEqualityPrecheck.Branch) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : Ranges unconstrained emptyGuard conjoin clear top checked values before)
    (answer : Except String (List (Value Symbol Guard))) (after : NativeState width Symbol Guard) :
    Graph unconstrained emptyGuard conjoin clear top checked values before answer after ↔
      ∃ g e p h c n, runChecked unconstrained emptyGuard conjoin clear top g e p h c n checked values before = .done answer after := by
  constructor
  · intro trace
    obtain ⟨g, e, p, h, c, n, stable⟩ := checked_stable unconstrained emptyGuard conjoin clear top trace
    exact ⟨g, e, p, h, c, n, stable g e p h c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨g, e, p, h, c, n, done⟩
    exact checked_graph unconstrained emptyGuard conjoin clear top g e p h c n checked values before ranges answer after done

/-- Actual prechecks retain complete graph and successful bounded source-worker agreement. -/
theorem execution_iff (own inherited : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard)
    (ranges : Ranges unconstrained emptyGuard conjoin clear top (SourceEqualityPrecheck.precheck own inherited) values before)
    (answer : Except String (List (Value Symbol Guard))) (after : NativeState width Symbol Guard) :
    Execution unconstrained emptyGuard conjoin clear top own inherited values before answer after ↔
      ∃ g e p h c n, SourceEqualityOnePassWorker.run unconstrained emptyGuard conjoin clear top g e p h c n own inherited values before = .done answer after :=
  checked_execution_iff unconstrained emptyGuard conjoin clear top _ values before ranges answer after

/-- Every complete guarded source graph has stable finite execution of the actual precheck entry. -/
theorem stable {own inherited values before answer after}
    (trace : Execution unconstrained emptyGuard conjoin clear top own inherited values (before : NativeState width Symbol Guard) answer after) :
    StableRun (fun g e p h c n => SourceEqualityOnePassWorker.run unconstrained emptyGuard conjoin clear top g e p h c n own inherited values before) answer after :=
  checked_stable unconstrained emptyGuard conjoin clear top trace

/-- The actual bounded array entry has the same stable source answer at every sufficient array bound. -/
theorem array_stable {own inherited values before answer after}
    (trace : Execution unconstrained emptyGuard conjoin clear top own inherited values (before : NativeState width Symbol Guard) answer after) :
    ∃ arrayBound, ∀ work, arrayBound ≤ work →
      StableRun (fun g e p h c n => runArray unconstrained emptyGuard conjoin clear top work g e p h c n own inherited values before) answer after := by
  obtain ⟨arrayBound, agrees⟩ := array_eventual (width := width) unconstrained emptyGuard conjoin clear top own inherited
  obtain ⟨g, e, p, h, c, n, complete⟩ := stable unconstrained emptyGuard conjoin clear top trace
  exact ⟨arrayBound, by intro work enough; exact ⟨g, e, p, h, c, n,
    by intro a b d f j k eg ee ep eh ec en; exact (agrees work enough a b d f j k values before).trans (complete a b d f j k eg ee ep eh ec en)⟩⟩

end MicroCFTA.SourceEqualityOnePassAPI
