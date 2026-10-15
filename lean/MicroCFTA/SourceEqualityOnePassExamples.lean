import MicroCFTA.SourceEqualityOnePassSource
import MicroCFTA.SourceEqualitySharedEditExamples

/-!
# Kernel checks for complete guarded native equality passes

Immediate unchanged and contradiction returns consume no stage bounds.
An empty live class list still runs final propagation. The ordinary live
fixture uses proved normalization and executes physical record selection, required
paths, target forcing, native narrowing, and final propagation.
-/
namespace MicroCFTA.SourceEqualityOnePassExamples
open InternedConstructorTemplates
open InternedNestedConstruction (Outcome)
open SourceEqualityClassFoldGraph SourceEqualityOnePassWorker
open SourceEqualitySharedEditExamples (record)

/-- The unchanged source guard preserves a preexisting mixed empty forest at zero bounds. -/
theorem unchanged (before : NativeState width Nat Unit) :
    SourceEqualityOnePassWorker.run (fun _ => true) () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 0 (some []) (some [])
      [.empty, .reference .depth] before = .done (.ok [.empty, .reference .depth]) before := rfl

/-- Contradiction erases every original position without selection or native work. -/
theorem contradiction (before : NativeState width Nat Unit) :
    SourceEqualityOnePassWorker.run (fun _ => true) () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 0 none (some [])
      [.empty, .reference .depth] before = .done (.ok [.empty, .empty]) before := rfl

/-- A live empty class list still runs final empty propagation, unlike the unchanged source guard. -/
theorem live_empty (before : NativeState width Nat Unit) :
    runChecked (fun _ => true) () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 0 (.ok (.classes []))
      [.empty, .reference .depth] before = .done (.ok [.empty, .empty]) before := by cbv

/-- Checked source errors retain their exact text and original full native state. -/
theorem checked_error (before : NativeState width Nat Unit) (message : String) :
    runChecked (fun _ => true) () (fun _ _ => ()) (fun _ => true) () 0 0 0 0 0 0 (.error message)
      [.reference .depth] before = .done (.error message) before := rfl

private theorem fixture_precheck : SourceEqualityPrecheck.precheck (some [record]) (some []) = .ok (.classes [record]) := by
  let witness : Language.Term Unit := .node () [.node () [.node () []], .node () [.node () []]]
  have first : SourceEqualityPrecheck.Sat witness (some [record]) := by
    simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies, EqualityNormalize.ClassSat, Language.PathsEqual,
      witness, record, Language.Term.atPath]
  have second : SourceEqualityPrecheck.Sat witness (some []) := by simp [SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]
  have accepted := (SourceEqualityPrecheck.combine_exact (some [record]) (some []) witness).mpr ⟨first, second⟩
  have notRejected : SourceEqualityPrecheck.rejects (SourceEqualityPrecheck.combine (some [record]) (some [])) = false := by
    cases result : SourceEqualityPrecheck.combine (some [record]) (some []) <;>
      simp_all only [EqualityNormalize.RunSat, SourceEqualityPrecheck.rejects]
  simp only [SourceEqualityPrecheck.precheck, SourceEqualityPrecheck.isEmpty, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    notRejected, SourceEqualityPrecheck.unsafeOrdered, Except.map]
  rfl

private noncomputable def fixtureRun (g e p h c n : Nat) (values : List (Value Nat Unit)) (before : NativeState 8 Nat Unit) : Result 8 Nat Unit :=
  SourceEqualityOnePassWorker.run (fun _ => true) () (fun _ _ => ()) (fun _ => true) () g e p h c n (some [record]) (some []) values before

private theorem fixtureRun_checked (g e p h c n : Nat) (values : List (Value Nat Unit)) (before : NativeState 8 Nat Unit) :
    fixtureRun g e p h c n values before = runChecked (fun _ => true) () (fun _ _ => ()) (fun _ => true) () g e p h c n (.ok (.classes [record])) values before := by
  simp only [fixtureRun, SourceEqualityOnePassWorker.run, fixture_precheck]

attribute [local cbv_eval] fixtureRun_checked

/-- Observe every actual stage of a complete ordinary guarded native pass. -/
def CompleteResults : Outcome Nat Unit (Value Nat Unit) → Prop
  | .pending .. => False
  | .done root heap =>
      let values := [root, root]
      let before := SourceEqualityNativeInitial.cold 8 heap
      match fixtureRun 4 2 2 0 0 16 values before with
      | .done (.ok results) after => results = values ∧ after.machine.heap = heap ∧ after.nodes.next = 1 ∧ after.edges.next = 0 ∧
          fixtureRun 5 3 3 1 2 20 values before = .done (.ok values) after ∧
          fixtureRun 4 2 2 0 0 16 values after = .done (.ok values) after
      | _ => False

/-- The complete source entry retains one warm native cell and identical full states at larger bounds. -/
theorem complete_source : CompleteResults (InternedFreshOrdinaryConstruction.build
    (.node [.mk 31 () [.node [.mk 11 () []]], .mk 32 () [.node [.mk 11 () []]]]) [] empty) := by
  set_option maxRecDepth 20000 in
  set_option cbv.maxSteps 30000000 in cbv

end MicroCFTA.SourceEqualityOnePassExamples
