import MicroCFTA.SourceEqualityPartialMemoBodyLaws
import MicroCFTA.SourceEqualityPartialMemoSound

/-!
# Current soundness through actual memo-aware body execution

Each child premise uses its current Sound, native Scope, and available closed
input. Check plans contain only reached checks. Actual native prefixes and
constructor receipts supply the heap preservation used between child calls.
-/
namespace MicroCFTA.SourceEqualityPartialMemoBodySound
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph SourceEqualityNativeScoped
open SourceEqualityPartialScope SourceEqualityPartialGraphLaws SourceEqualityPartialMemoWorker
open SourceEqualityPartialMemoSound SourceEqualityPartialMemoBodyLaws
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "source" => SourceMemoGate.unconstrained
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Smaller actual calls use current physical and semantic provenance before their receipt. -/
def CallbackSound (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (call : Callback width)
    (check : SourceEqualityPrecheck.Constraint → Value Symbol Guard → SourceEqualityPartialMemoWorker.State width → Prop) : Prop :=
  ∀ inherited value before result after, check inherited value before →
    Sound (acceptsConstraint formulas solver) ambient before → Scope before.native →
    Available before.native.machine.heap value → value.free = [] → SourceEqualityDescend.WellFormed inherited →
    call inherited value before = .done (.ok result) after →
      Sound (acceptsConstraint formulas solver) ambient after ∧
        NodeLaw formulas solver ambient inherited value before.native result after.native

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem bind_done {first : Result width Input}
    {next : Input → SourceEqualityPartialMemoWorker.State width → Result width Output}
    {output : Output} {after : SourceEqualityPartialMemoWorker.State width}
    (done : first.bind next = .done (.ok output) after) :
    ∃ input middle, first = .done (.ok input) middle ∧ next input middle = .done (.ok output) after := by
  cases first with
  | incomplete => cases done
  | done answer middle => cases answer with
    | error => cases done
    | ok input => exact ⟨input, middle, rfl, done⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem done_ok_inj {first second : Output} {before after : SourceEqualityPartialMemoWorker.State width}
    (same : (Result.done (.ok first) before : Result width Output) = .done (.ok second) after) :
    first = second ∧ before = after := by
  cases same
  exact ⟨rfl, rfl⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (ambient : InternedGuardedLanguage.Env Symbol)
local notation "holds" => acceptsConstraint formulas solver

/-- Actual child traversal threads current Sound and composes the native indexed law. -/
theorem walk {call : Callback width} {check} (node : CallbackSound formulas solver ambient call check)
    {payload index values before results after}
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (wellFormed : SourceEqualityDescend.WellFormed payload)
    (plan : WalkChecked call check payload index values before)
    (done : childrenWalk call payload index values before = .done (.ok results) after) :
    Sound holds ambient after ∧ WalkLaw formulas solver ambient payload index values before.native results after.native := by
  induction values generalizing index before results after with
  | nil =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨sound, SourceEqualityPartialGraphProofs.walk formulas solver ambient .nil⟩
  | cons value values ih =>
      obtain ⟨result, middle, first, remaining⟩ := bind_done done
      obtain ⟨tail, final, rest, finished⟩ := bind_done remaining
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      have head := node _ _ _ _ _ plan.1 sound scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
        (SourceEqualityDescend.descend_wellFormed payload wellFormed index) first
      have headFacts := head.2 scope (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have tailFacts := ih head.1 headFacts.1
        (fun child member => headFacts.2.1.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member)) (plan.2 _ _ first) rest
      exact ⟨tailFacts.1, walk_cons formulas solver ambient head.2 tailFacts.2⟩

/-- Actual child adapters retain current Sound and their parent-contextual language law. -/
theorem children {call : Callback width} {check} (node : CallbackSound formulas solver ambient call check)
    {payload values before results after}
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (available : Values before.native.machine.heap values) (closed : ClosedValues values)
    (wellFormed : SourceEqualityDescend.WellFormed payload)
    (plan : ChildrenChecked call check payload values before)
    (done : SourceEqualityPartialMemoWorker.children call payload values before = .done (.ok results) after) :
    Sound holds ambient after ∧ ChildrenLaw formulas solver ambient payload values before.native results after.native := by
  cases payload with
  | none =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨sound, SourceEqualityPartialGraphProofs.children formulas solver ambient .contradiction⟩
  | some records =>
      have traversed := walk formulas solver ambient node sound scope available closed wellFormed plan done
      exact ⟨traversed.1, live_children formulas solver ambient traversed.2⟩

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

/-- Actual native prefixes, child calls, and literal edge allocation preserve current Sound. -/
theorem rows {call : Callback width} {check} (node : CallbackSound formulas solver ambient call check)
    (g e p h c n : Nat) {inherited edges before results after}
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (resident : Edges before.native.machine.heap edges) (closed : ClosedEdges edges)
    (plan : RowsChecked call check g e p h c n inherited edges before)
    (done : SourceEqualityPartialMemoWorker.rows call g e p h c n inherited edges before = .done (.ok results) after) :
    Sound holds ambient after ∧ RowsLaw formulas solver ambient inherited edges before.native results after.native := by
  induction edges generalizing before results after with
  | nil =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨sound, SourceEqualityPartialGraphProofs.rows formulas solver ambient .nil⟩
  | cons edge edges ih =>
      obtain ⟨result, middle, first, remaining⟩ := bind_done done
      obtain ⟨tail, final, rest, finished⟩ := bind_done remaining
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      have tailPlan := plan.2.2 _ _ first
      obtain ⟨narrowed, nativeMiddle, own, payload, values, childAfter,
        localPass, physical, combined, childrenDone, rfl, rfl⟩ := edge_parts first
      have native := SourceEqualityGuardedEdgeWorkerProofs.graph source top conjoin SourceMemoGate.plain top
        g e p h c n edge inherited before.native plan.1 narrowed nativeMiddle localPass
      have localFacts := scope.narrow native (resident _ List.mem_cons_self) (closed _ List.mem_cons_self) formulas solver ambient
      have localSound : Sound holds ambient { before with native := nativeMiddle } :=
        sound.keeps holds ambient rfl localFacts.2.1
      have childAvailable := localFacts.1.native.semantic.ready.semantic.1.normal.facts.cached.edges
        narrowed.entry.key narrowed localFacts.2.2.1
      have payloadWellFormed := (@SourceEqualityInheritedPayload.combine_exact Symbol inherited own payload combined).1
      have child := children formulas solver ambient node localSound localFacts.1 childAvailable localFacts.2.2.2.1
        payloadWellFormed (plan.2.1 _ _ localPass _ physical _ combined) childrenDone
      have childFacts := child.2 localFacts.1 childAvailable localFacts.2.2.2.1 payloadWellFormed
      have guardValid := localFacts.1.annotations narrowed.entry.key narrowed localFacts.2.2.1
      have built := Scope.edge childAfter.native childFacts.1 narrowed.entry.key.symbol narrowed.entry.key.constraint values
        guardValid childFacts.2.2.1
      have builtSound : Sound holds ambient { childAfter with native := (advanceHeap childAfter.native
          (run (makeEdge narrowed.entry.key.symbol narrowed.entry.key.constraint values) childAfter.native.machine.heap).2) } :=
        child.1.keeps holds ambient rfl built.2.1
      have head := edge_continuation formulas solver ambient physical combined child.2
        localFacts.1 localFacts.2.2.1 localFacts.2.2.2.1
      have headKeeps := localFacts.2.1.trans head.2.1
      have tailFacts := ih builtSound head.1
        (fun other member => edge_grows _ _ headKeeps.growth other (resident other (List.mem_cons_of_mem _ member)))
        (fun other member => closed other (List.mem_cons_of_mem _ member)) tailPlan rest
      exact ⟨tailFacts.1, rows_cons formulas solver ambient native physical combined child.2 tailFacts.2⟩

/-- The actual successful body preserves current Sound and derives its complete native NodeLaw. -/
theorem step {call : Callback width} {check} (node : CallbackSound formulas solver ambient call check)
    (g e p h c n : Nat) (request : Request) (before : SourceEqualityPartialMemoWorker.State width)
    (result : Value Symbol Guard) (after : SourceEqualityPartialMemoWorker.State width)
    (sound : Sound holds ambient before) (scope : Scope before.native)
    (available : Available before.native.machine.heap request.value) (closed : request.value.free = [])
    (_wellFormed : SourceEqualityDescend.WellFormed request.inherited)
    (plan : Checked call check g e p h c n request before)
    (done : SourceEqualityPartialMemoWorker.step call g e p h c n request before = .done (.ok result) after) :
    Sound holds ambient after ∧ NodeLaw formulas solver ambient request.inherited request.value before.native result after.native := by
  rcases request with ⟨inherited, value⟩
  cases value with
  | empty =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨sound, identity_node formulas solver ambient inherited .empty before.native⟩
  | reference => cases done
  | union entry members depth free =>
      have equal := done_ok_inj done
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨sound, identity_node formulas solver ambient inherited (.union entry members depth free) before.native⟩
  | mu entry body depth ordinary =>
      cases actual : SourceEqualityMuReconstruction.rebuild entry body depth ordinary before.native.machine.heap with
      | pending => simp only [SourceEqualityPartialMemoWorker.step, actual] at done; cases done
      | done value heap =>
          simp only [SourceEqualityPartialMemoWorker.step, actual] at done
          have equal := done_ok_inj done
          rcases equal with ⟨rfl, rfl⟩
          have law := binder_node formulas solver ambient (inherited := inherited) actual
          exact ⟨sound.keeps holds ambient rfl (law scope available closed).2.1, law⟩
  | node entry edges depth free =>
      obtain ⟨results, middle, rowsDone, finished⟩ := bind_done done
      have equal := done_ok_inj finished
      rcases equal with ⟨rfl, rfl⟩
      have facts := scope.native.semantic.ready.semantic.1.normal.facts
      have resident := resident_edges _ facts.linked _ available.resident
      have rowsClosed := SourceEqualityPartialStepProofs.closed_rows before.native scope.native entry edges depth free available closed
      have traversed := rows formulas solver ambient node g e p h c n sound scope resident rowsClosed plan rowsDone
      have rowFacts := traversed.2 scope resident rowsClosed
      have built := Scope.modify entry edges results depth free middle.native rowFacts.1
        (rowFacts.2.1.available _ available) closed rowFacts.2.2.1 rowFacts.2.2.2.1 holds ambient
      exact ⟨traversed.1.keeps holds ambient rfl built.2.1, ordinary_node formulas solver ambient traversed.2⟩

end MicroCFTA.SourceEqualityPartialMemoBodySound
