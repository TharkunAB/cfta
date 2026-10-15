import MicroCFTA.SourceEqualityPartialMemoSound
import MicroCFTA.SourceEqualityPartialGraphLaws

/-!
# Actual ready hits and completion of the stored request

Ready hits use the current physical cell invariant and exact key links.
Completion retains the original running request through the actual body.
Neither proof replays the native effects of a previous execution.
-/
namespace MicroCFTA.SourceEqualityPartialMemoReuse
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialMemoWorker SourceEqualityPartialMemoFrame SourceEqualityPartialMemoSound
open SourceEqualityPartialKeyTransport SourceEqualityPartialGraphLaws SourceEqualityPartialScope
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol)
local notation "holds" => acceptsConstraint formulas solver

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- A stored physical constraint identity makes repeat preparation leave the complete state unchanged. -/
theorem prepare_linked (candidate : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (key : SourceEqualityPartialMemoWorker.Key) (linked : KeyOf before.constraints candidate key) :
    prepare candidate before = (key, before) := by
  rcases key with ⟨identity, node⟩
  rcases linked with ⟨recorded, reference⟩
  cases identity with
  | none =>
      cases payload : candidate.inherited with
      | none => simp only [prepare, payload, SourceEqualityPartialConstraintKey.identify, reference]
      | some records => simp [Recorded, payload] at recorded
  | some identity =>
      cases payload : candidate.inherited with
      | none => simp [Recorded, payload] at recorded
      | some records =>
          obtain ⟨entry, stored, same⟩ := (show Recorded before.constraints (some records) (some identity) from by simpa only [payload] using recorded)
          simp only [prepare, payload, SourceEqualityPartialConstraintKey.identify, Cache.intern, stored, same, reference]

/-- Repeating a complete original request returns its full stored value and identical full state at any bound. -/
theorem run_ready (g e p h c n fuel : Nat) (original : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (key : SourceEqualityPartialMemoWorker.Key) (handle : Nat) (result : Value Symbol Guard)
    (valid : Valid (stateTables before)) (published : before.memo.table key = some handle)
    (returned : before.memo.cells handle = some ⟨original, .returned result⟩) :
    SourceEqualityPartialMemoWorker.run g e p h c n fuel original.inherited original.value before = .done (.ok result) before := by
  obtain ⟨cell, stored, linked⟩ := valid.2.linked key handle published
  have same := Option.some.inj (stored.symm.trans returned)
  subst cell
  have preparation := prepare_linked original before key linked
  cases fuel with
  | zero =>
      exact request_ready (fun handle original state => .incomplete (.exhausted original handle state))
        original original before before key handle result preparation published returned
  | succ fuel =>
      exact request_ready (fun _ => step (SourceEqualityPartialMemoWorker.run g e p h c n fuel) g e p h c n)
        original original before before key handle result preparation published returned

/-- Actual ready lookup returns its stored result and derives its current scoped language law. -/
theorem ready (body : Nat → Request → SourceEqualityPartialMemoWorker.State width → Result width (Value Symbol Guard))
    (candidate original : Request) (before : SourceEqualityPartialMemoWorker.State width) (handle : Nat) (result : Value Symbol Guard)
    (sound : Sound holds ambient before) (wellFormed : SourceEqualityDescend.WellFormed candidate.inherited)
    (published : (prepare candidate before).2.memo.table (prepare candidate before).1 = some handle)
    (returned : (prepare candidate before).2.memo.cells handle = some ⟨original, .returned result⟩) :
    request body candidate before = .done (.ok result) (prepare candidate before).2 ∧
      NodeLaw formulas solver ambient candidate.inherited candidate.value before.native result (prepare candidate before).2.native := by
  have prepared := prepare_sound holds ambient candidate before sound
  obtain ⟨cell, stored, linked⟩ := prepared.valid.2.linked (prepare candidate before).1 handle published
  have same := Option.some.inj (stored.symm.trans returned)
  subst cell
  have good := prepared.cells handle ⟨original, .returned result⟩ returned
  have candidateKey := prepare_key candidate before sound.valid
  refine ⟨request_ready body candidate original before _ _ handle result rfl published returned, ?_⟩
  intro scope available closed
  have semantic := cached_identity_meaning holds ambient before.native.machine.heap
    scope.native.semantic.ready.semantic.1.normal.facts.coherent
    (prepare candidate before).2.constraints prepared.valid.1 original.inherited candidate.inherited
    (prepare candidate before).1.1 original.value candidate.value result good.2.2.1 wellFormed
    linked.1 candidateKey.1 good.1 available (linked.2.trans candidateKey.2.symm) good.2.2.2.2.2
  exact ⟨scope, SourceEqualityRequiredCache.pure_keeps _ scope.native.semantic.ready,
    good.2.2.2.1, good.2.2.2.2.1, semantic⟩

/-- The actual body frame and language law justify the exact newly returned cell. -/
theorem completed_cell (handle : Nat) (original : Request)
    (before after : SourceEqualityPartialMemoWorker.State width) (result : Value Symbol Guard)
    (sound : Sound holds ambient before) (running : before.memo.cells handle = some ⟨original, .evaluating⟩)
    (scope : Scope before.native)
    (frame : Framed before (.done (.ok result) after))
    (law : NodeLaw formulas solver ambient original.inherited original.value before.native result after.native) :
    (FlatMemoThunk.finish handle result after.memo).cells handle = some ⟨original, .returned result⟩ ∧
      CellGood holds ambient after.native.machine.heap ⟨original, .returned result⟩ := by
  have good := sound.cells handle ⟨original, .evaluating⟩ running
  have checked := law scope good.1 good.2.1
  exact ⟨FlatMemoThunk.finish_evaluating handle result after.memo original (frame.running handle original running),
    checked.2.1.available _ good.1, good.2.1, good.2.2.1,
    checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2⟩

end MicroCFTA.SourceEqualityPartialMemoReuse
