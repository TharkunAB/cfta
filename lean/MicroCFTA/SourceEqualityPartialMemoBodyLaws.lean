import MicroCFTA.SourceEqualityPartialMemoWorker
import MicroCFTA.SourceEqualityPartialGraphProofs
import MicroCFTA.SourceEqualityGuardedEdgeWorkerProofs

/-!
# Actual memo-aware body composition

Check plans follow the full states returned by actual child calls and native
prefixes. The child premise supplies the semantic conclusion for those calls.
The body proof composes existing constructor laws at the actual native states.
It does not replay a nonmemoized worker or identify different heap effects.
-/
namespace MicroCFTA.SourceEqualityPartialMemoBodyLaws
open Cache Language InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped SourceEqualityPartialGraphLaws
open SourceEqualityPartialMemoWorker
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A callback receives and returns the complete actual memo-aware state. -/
abbrev Callback (width : Nat) :=
  SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Result width (Value Symbol Guard)

/-- Indexed checks advance only after the actual earlier child succeeds. -/
def WalkChecked (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Prop)
    (payload : SourceEqualityPrecheck.Constraint) : Nat → List (Value Symbol Guard) → State width → Prop
  | _, [], _ => True
  | index, value :: values, before =>
      check (SourceEqualityDescend.descend payload index) value before ∧
      ∀ result middle, call (SourceEqualityDescend.descend payload index) value before = .done (.ok result) middle →
        WalkChecked call check payload (index + 1) values middle

/-- Contradiction needs no child check; live payloads use their actual indexed walk. -/
def ChildrenChecked (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Prop)
    (payload : SourceEqualityPrecheck.Constraint) (values : List (Value Symbol Guard)) (before : State width) : Prop :=
  match payload with
  | none => True
  | some records => WalkChecked call check (some records) 0 values before

/-- Row checks retain reached native ranges and the full returned continuation states. -/
def RowsChecked (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Prop)
    (g e p h c n : Nat) (inherited : SourceEqualityPrecheck.Constraint) : List (EdgeValue Symbol Guard) → State width → Prop
  | [], _ => True
  | edge :: edges, before =>
      SourceEqualityPCSNativeEdge.Ranges edge inherited before.native ∧
      (∀ narrowed middle, SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top
        g e p h c n edge inherited before.native = .done (.ok narrowed) middle →
        ∀ own, SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint = .ok own →
        ∀ payload, SourceEqualityInheritedPayload.combine inherited own = .ok payload →
          ChildrenChecked call check payload narrowed.children { before with native := middle }) ∧
      ∀ result middle, SourceEqualityPartialMemoWorker.edge call g e p h c n edge inherited before = .done (.ok result) middle →
        RowsChecked call check g e p h c n inherited edges middle

/-- Only an ordinary body reaches row range checks or recursive child checks. -/
def Checked (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Prop)
    (g e p h c n : Nat) (request : Request) (before : State width) : Prop :=
  match request.value with
  | .node _ edges _ _ => RowsChecked call check g e p h c n request.inherited edges before
  | _ => True

/-- Successful actual checked child calls supply their native semantic conclusion. -/
def CallbackLaw (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → State width → Prop) : Prop :=
  ∀ inherited value before result after, check inherited value before → SourceEqualityDescend.WellFormed inherited →
    call inherited value before = .done (.ok result) after →
      NodeLaw formulas solver ambient inherited value before.native result after.native

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_done {first : Result width Input} {next : Input → State width → Result width Output}
    {output : Output} {after : State width} (done : first.bind next = .done (.ok output) after) :
    ∃ input middle, first = .done (.ok input) middle ∧ next input middle = .done (.ok output) after := by
  cases first with
  | incomplete => cases done
  | done answer middle =>
      cases answer with
      | error => cases done
      | ok input => exact ⟨input, middle, rfl, done⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem done_ok_inj {first second : Output} {before after : State width}
    (same : (Result.done (.ok first) before : Result width Output) = .done (.ok second) after) :
    first = second ∧ before = after := by
  cases same
  exact ⟨rfl, rfl⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (ambient : InternedGuardedLanguage.Env Symbol)

/-- Actual memo-aware child receipts compose at their exact returned native heaps. -/
theorem walk {call : Callback width} {check} (node : CallbackLaw formulas solver ambient call check)
    {payload index values before results after}
    (wellFormed : SourceEqualityDescend.WellFormed payload)
    (plan : WalkChecked call check payload index values before)
    (done : childrenWalk call payload index values before = .done (.ok results) after) :
    WalkLaw formulas solver ambient payload index values before.native results after.native := by
  induction values generalizing index before results after with
  | nil =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact SourceEqualityPartialGraphProofs.walk formulas solver ambient .nil
  | cons value values ih =>
      obtain ⟨result, middle, first, remaining⟩ := bind_done done
      obtain ⟨tail, final, rest, finished⟩ := bind_done remaining
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      exact walk_cons formulas solver ambient
        (node _ _ _ _ _ plan.1 (SourceEqualityDescend.descend_wellFormed payload wellFormed index) first)
        (ih (plan.2 _ _ first) rest)

/-- Actual contradiction and live adapters derive the existing parent-contextual child law. -/
theorem children {call : Callback width} {check} (node : CallbackLaw formulas solver ambient call check)
    {payload values before results after}
    (plan : ChildrenChecked call check payload values before)
    (done : SourceEqualityPartialMemoWorker.children call payload values before = .done (.ok results) after) :
    ChildrenLaw formulas solver ambient payload values before.native results after.native := by
  cases payload with
  | none =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact SourceEqualityPartialGraphProofs.children formulas solver ambient .contradiction
  | some records =>
      intro scope available closed wellFormed
      exact live_children formulas solver ambient (walk formulas solver ambient node wellFormed plan done)
        scope available closed wellFormed

private theorem edge_parts {call : Callback width} {g e p h c n edge inherited before result after}
    (done : SourceEqualityPartialMemoWorker.edge call g e p h c n edge inherited before = .done (.ok result) after) :
    ∃ narrowed middle own payload values childAfter,
      SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top g e p h c n edge inherited before.native =
        .done (.ok narrowed) middle ∧
      SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint = .ok own ∧
      SourceEqualityInheritedPayload.combine inherited own = .ok payload ∧
      SourceEqualityPartialMemoWorker.children call payload narrowed.children { before with native := middle } =
        .done (.ok values) childAfter ∧
      result = (run (makeEdge narrowed.entry.key.symbol narrowed.entry.key.constraint values) childAfter.native.machine.heap).1 ∧
      after = { childAfter with native := (advanceHeap childAfter.native
        (run (makeEdge narrowed.entry.key.symbol narrowed.entry.key.constraint values) childAfter.native.machine.heap).2) } := by
  cases localPass : SourceEqualityGuardedEdgeWorker.run source top conjoin SourceMemoGate.plain top
      g e p h c n edge inherited before.native with
  | children => simp only [SourceEqualityPartialMemoWorker.edge, localPass] at done; cases done
  | done answer middle =>
      cases answer with
      | error => simp only [SourceEqualityPartialMemoWorker.edge, localPass] at done; cases done
      | ok narrowed =>
          simp only [SourceEqualityPartialMemoWorker.edge, localPass, descendants] at done
          cases physical : SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint with
          | error => simp only [physical] at done; cases done
          | ok own =>
              simp only [physical] at done
              cases combined : SourceEqualityInheritedPayload.combine inherited own with
              | error => simp only [combined] at done; cases done
              | ok payload =>
                  simp only [combined] at done
                  obtain ⟨values, childAfter, childrenDone, finished⟩ := bind_done done
                  have equal := done_ok_inj finished
                  exact ⟨narrowed, middle, own, payload, values, childAfter,
                    rfl, physical, combined, childrenDone, equal.1.symm, equal.2.symm⟩

/-- Actual ordered row execution composes the native prefix and memo-aware child laws. -/
theorem rows {call : Callback width} {check} (node : CallbackLaw formulas solver ambient call check)
    (g e p h c n : Nat) {inherited edges before results after}
    (plan : RowsChecked call check g e p h c n inherited edges before)
    (done : SourceEqualityPartialMemoWorker.rows call g e p h c n inherited edges before = .done (.ok results) after) :
    RowsLaw formulas solver ambient inherited edges before.native results after.native := by
  induction edges generalizing before results after with
  | nil =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact SourceEqualityPartialGraphProofs.rows formulas solver ambient .nil
  | cons edge edges ih =>
      obtain ⟨result, middle, first, remaining⟩ := bind_done done
      obtain ⟨tail, final, rest, finished⟩ := bind_done remaining
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      have tailLaw := ih (plan.2.2 _ _ first) rest
      obtain ⟨narrowed, nativeMiddle, own, payload, values, childAfter,
        localPass, physical, combined, childrenDone, rfl, rfl⟩ := edge_parts first
      have native := SourceEqualityGuardedEdgeWorkerProofs.graph source top conjoin SourceMemoGate.plain top
        g e p h c n edge inherited before.native plan.1 narrowed nativeMiddle localPass
      exact rows_cons formulas solver ambient native physical combined
        (children formulas solver ambient node (plan.2.1 _ _ localPass _ physical _ combined) childrenDone) tailLaw

/-- The actual successful memo-aware body derives scope, physical preservation, and contextual exactness. -/
theorem step {call : Callback width} {check} (node : CallbackLaw formulas solver ambient call check)
    (g e p h c n : Nat) (request : Request) (before : State width) (result : Value Symbol Guard) (after : State width)
    (plan : Checked call check g e p h c n request before)
    (done : SourceEqualityPartialMemoWorker.step call g e p h c n request before = .done (.ok result) after) :
    NodeLaw formulas solver ambient request.inherited request.value before.native result after.native := by
  rcases request with ⟨inherited, value⟩
  cases value with
  | empty =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact identity_node formulas solver ambient inherited .empty before.native
  | reference => cases done
  | union entry members depth free =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact identity_node formulas solver ambient inherited (.union entry members depth free) before.native
  | mu entry body depth ordinary =>
      cases actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap with
      | pending => simp only [SourceEqualityPartialMemoWorker.step, actual] at done; cases done
      | done value heap =>
          simp only [SourceEqualityPartialMemoWorker.step, actual] at done
          have equal := done_ok_inj done
          rcases equal with ⟨rfl, rfl⟩
          exact binder_node formulas solver ambient actual
  | node entry edges depth free =>
      obtain ⟨results, middle, rowsDone, finished⟩ := bind_done done
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      exact ordinary_node formulas solver ambient (rows formulas solver ambient node g e p h c n plan rowsDone)

end MicroCFTA.SourceEqualityPartialMemoBodyLaws
