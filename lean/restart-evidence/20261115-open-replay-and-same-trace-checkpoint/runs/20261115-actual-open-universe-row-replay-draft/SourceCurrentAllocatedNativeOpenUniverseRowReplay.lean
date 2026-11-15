import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
import MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
import MicroCFTA.SourceEqualityOriginalFieldOrigins
import MicroCFTA.SourceSynthesisUniverseRowTransform

/-!
# Actual checked replay of open source universe rows

An earlier original field allocation derives the actual checked prefix.
The ordered child results use their actual smaller query traces.
The constructor retains the literal substitution cutoff and all cache effects.
No profile or semantic model is assigned to the open auxiliary row.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowReplay
open Cache InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open InternedStoredSubstitution (input)
open InternedStoredSubstitutionRebind (replacement)
open SourceRecursiveIntersectionControl (pair repeatedValue)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

set_option autoImplicit false

private theorem source_top_ready (arity : Nat) :
    SourceEqualityIntersectionEdgeAllocation.source GuardStructuralOrder.le top top arity arity =
      .ready top := by
  unfold SourceEqualityIntersectionEdgeAllocation.source
  rw [if_neg (by intro different; exact different rfl)]
  rfl

/-- An earlier Top field allocation derives the actual ready body prefix and reached operations. -/
theorem original_top_self_body_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state : Checked width)
    (self : request.right = request.left)
    (sourceTop : request.left.entry.key.constraint = top)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (origin : SourceEqualityOriginalFieldOrigins.Origin state.operations.constraints
      request.left.entry.key.constraint) :
    ∃ loaded combined : Allocated,
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints =
        .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = top ∧
      (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined) ∧
      SourceEqualityConjoinAllocation.readback combined = top ∧
      SourceEqualityConstraintMemoAllocation.Valid
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
          request.left.children.length request.right.children.length state.operations).2 ∧
      SourceEqualityConstraintMemoAllocation.Grows state.operations
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
          request.left.children.length request.right.children.length state.operations).2 ∧
      SourceEqualityNativeDemand.body request .pure state =
        .yielded (.code (SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined))
          {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
            request.left.children.length request.right.children.length state.operations).2} := by
  have cached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities := by
    simpa only [sourceTop] using SourceEqualityConstraintConstructors.top_cached (Formula := FullSyntax.Formula)
  obtain ⟨loaded, actualLoad, readback, ready, _physicalRead⟩ :=
    SourceEqualityOriginalFieldOrigins.Origin.load request.left.entry.key.constraint
      state.operations.constraints cached origin
  have loadedTop : SourceEqualityConjoinAllocation.readback loaded = top := readback.trans sourceTop
  have arity : request.left.children.length = request.right.children.length := by rw [self]
  obtain ⟨branch, actual, semantic, afterValid, growth, _ready⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le loaded loaded
      request.left.children.length request.right.children.length state.operations valid ready ready
  have topBranch : branch.map SourceEqualityConjoinAllocation.readback = .ready top := by
    simpa only [loadedTop, self, source_top_ready] using semantic
  cases branch with
  | mismatch | rejected => cases topBranch
  | ready combined =>
      have combinedTop := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj topBranch
      have rightLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
          state.operations.constraints = .ok (some loaded) := by rw [self]; exact actualLoad
      have one := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        state arity loaded loaded combined actualLoad rightLoad actual
      simp only [code_bind_pure] at one
      exact ⟨loaded, combined, actualLoad, loadedTop, actual, combinedTop, afterValid, growth, one⟩

private theorem self_pairs_map {A B : Type} (values : List A) (read : A → B) :
    (values.zip values).map (fun pair => read pair.1) = values.map read := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.zip_cons_cons, List.map_cons, ih]

/-- An actual ordered child walk retains its literal outputs under the same body prefix. -/
private theorem walk_values
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (read : Value Symbol Guard → Value Symbol Guard)
    (fuel : Nat) (request : EdgeRequest Symbol Guard) (state : Checked width)
    (pairs : List Pair) (before : Checked width) (values : List (Value Symbol Guard))
    (after : Checked width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk
      (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs before values after count)
    (stepsBefore : Nat) (next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard))
    (origin : Steps stepsBefore (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind next)) before)
    (positive : 0 < stepsBefore) (bounded : stepsBefore + count < fuel)
    (included : ∀ pair ∈ pairs, pair ∈ request.left.children.zip request.right.children)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps stepsBefore (.edgeBody request .pure) state
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first =
        .done value last → value = read pair.1) :
    values = pairs.map (fun pair => read pair.1) := by
  induction walked generalizing stepsBefore next with
  | nil current => rfl
  | cons pair rest before middle after value values firstFuel restFuel called tail ih =>
      let childNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
        fun value => (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
          (fun values => next (value :: values))
      have atChild : Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have same := children stepsBefore (firstFuel + 1) positive (by omega) (by omega)
        pair (included pair List.mem_cons_self) childNext before middle value atChild
        (trace_done firstFuel _ before middle value called)
      have advanced := called.bind _ _ _ _ _ childNext
      have tailOrigin : Steps (stepsBefore + firstFuel) (.edgeBody request .pure) state
          (.code ((SourceRecursiveIntersectionCode.walk
            (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
            (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have later := ih (stepsBefore + firstFuel) (fun values => next (value :: values)) tailOrigin
        (by omega) (by omega) (by intro candidate member; exact included candidate (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, same, later]

/-- Actual open-row replay retains both laws at all fuels and derives its exact ordered constructor inputs. -/
theorem open_row_replay_and_returned_of_children
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (sourceName cutoffLeft cutoffRight : Nat)
    (request : EdgeRequest Symbol Guard) (state : Checked width) (fuel : Nat)
    (self : request.right = request.left) (sourceTop : request.left.entry.key.constraint = top)
    (valid : SourceEqualityConstraintMemoAllocation.Valid state.operations)
    (fieldOrigin : SourceEqualityOriginalFieldOrigins.Origin state.operations.constraints
      request.left.entry.key.constraint)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (childrenReturned : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
      Steps stepsBefore (.edgeBody request .pure) state
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode request.domain pair.1 pair.2)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode request.domain pair.1 pair.2)) first).state.native.edges)
    (childrenReplay : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : Checked width) (value : Value Symbol Guard),
      Steps stepsBefore (.edgeBody request .pure) state
        (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
      SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first =
        .done value last →
      value = input (replacement (.interned sourceName)
        (repeatedValue (SourceRecursiveIntersectionControl.pair cutoffLeft cutoffRight))) pair.1) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state).state.native.edges ∧
    ∀ (result : EdgeValue Symbol Guard) (after : Checked width),
      SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done result after →
      ∃ (loaded combined : Allocated) (values : List (Value Symbol Guard)) (middle : Checked width) (count : Nat),
        SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint state.operations.constraints =
          .ok (some loaded) ∧
        (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
          request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined) ∧
        SourceEqualityConjoinAllocation.readback combined = top ∧
        count + 1 < fuel ∧
        SourceEqualityNativeDemandWalkExecution.Walk (fun pair => requestNode request.domain pair.1 pair.2)
          (request.left.children.zip request.right.children)
          {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
            request.left.children.length request.right.children.length state.operations).2} values middle count ∧
        values = request.left.children.map
          (input (replacement (.interned sourceName) (repeatedValue (pair cutoffLeft cutoffRight)))) ∧
        result = (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).1 ∧
        after = {middle with native := advance middle.native {middle.native.machine with heap :=
          (run (makeEdge request.left.entry.key.symbol top values) middle.native.machine.heap).2}} := by
  have retained := SourceCurrentAllocatedNativeEdgeBodyReturned.edge_body_returned_all_fuels
    nodeLaw edgeLaw request state fuel nodes edges childrenReturned
  refine ⟨retained.1, retained.2, ?_⟩
  intro result after done
  obtain ⟨loaded, combined, actualLoad, _loadedTop, actualAllocation, combinedTop, _afterValid, _growth, one⟩ :=
    original_top_self_body_prefix request state self sourceTop valid fieldOrigin
  have arity : request.left.children.length = request.right.children.length := by rw [self]
  have rightLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
      state.operations.constraints = .ok (some loaded) := by rw [self]; exact actualLoad
  obtain ⟨values, middle, count, bounded, walked, sameResult, sameAfter⟩ :=
    SourceEqualityNativeDemandAcceptedReadback.body_observation request state after loaded loaded combined fuel result
      arity actualLoad rightLoad actualAllocation done
  let next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard) :=
    fun values => .work (makeEdge request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values) .pure
  have origin : Steps 1 (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk (fun pair : Pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)).bind next))
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le loaded loaded
        request.left.children.length request.right.children.length state.operations).2} :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have valuesRead := walk_values
    (input (replacement (.interned sourceName) (repeatedValue (pair cutoffLeft cutoffRight))))
    fuel request state (request.left.children.zip request.right.children) _ values middle count walked
    1 next origin (by decide) (by omega) (by intro candidate member; exact member) childrenReplay
  have ordered : values = request.left.children.map
      (input (replacement (.interned sourceName) (repeatedValue (pair cutoffLeft cutoffRight)))) := by
    simpa only [self, self_pairs_map] using valuesRead
  rw [combinedTop] at sameResult sameAfter
  exact ⟨loaded, combined, values, middle, count, actualLoad, actualAllocation, combinedTop,
    bounded, walked, ordered, sameResult, sameAfter⟩

end MicroCFTA.SourceCurrentAllocatedNativeOpenUniverseRowReplay
