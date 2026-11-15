import MicroCFTA.SourceEqualityNativeDemandAcceptedReadback
import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.InternedBoundaryAtoms
import MicroCFTA.MergedPhysicalGroupEdges

/-!
# Footprints from the actual checked edge body

The accepted branch derives each child from its actual shorter execution.
The final constructor retains the actual allocated constraint and endpoint.
The sentinel branches have no recursive child call.
The child induction hypothesis is a local proof obligation.
This file does not derive that hypothesis for the whole native worker.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyFootprints
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open InternedBoundaryAtoms (atoms)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
variable {width : Nat}

set_option autoImplicit false

private theorem walk_footprints
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (universeIdentity fuel : Nat) (request : EdgeRequest Symbol Guard) (state : State width)
    (pairs : List Pair) (before : State width) (values : List (Value Symbol Guard))
    (after : State width) (count : Nat)
    (walked : SourceEqualityNativeDemandWalkExecution.Walk
      (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs before values after count)
    (stepsBefore : Nat) (next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard))
    (origin : Steps stepsBefore (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind next)) before)
    (positive : 0 < stepsBefore) (bounded : stepsBefore + count < fuel) (physical : Physical before.native)
    (included : ∀ pair ∈ pairs, pair ∈ request.left.children.zip request.right.children)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : State width) (value : Value Symbol Guard),
        Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
        Physical first.native →
        SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first = .done value last →
        Physical last.native ∧ Extension first.native.machine last.native.machine ∧
          Available last.native.machine.heap value ∧
          ∀ atom ∈ atoms value, atom = .mu universeIdentity) :
    Physical after.native ∧ Extension before.native.machine after.native.machine ∧
      InternedNestedProvenance.Values after.native.machine.heap values ∧
      ∀ value ∈ values, ∀ atom ∈ atoms value, atom = .mu universeIdentity := by
  induction walked generalizing stepsBefore next with
  | nil current =>
      exact ⟨physical, Extension.refl _, (by intro value member; cases member),
        (by intro value member; cases member)⟩
  | cons pair rest before middle after value values firstFuel restFuel called tail ih =>
      let childNext : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
        fun value => (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
          (fun values => next (value :: values))
      have atChild : Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind childNext)) before := by
        simpa only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, childNext] using origin
      have completed := trace_done firstFuel _ before middle value called
      have first := children stepsBefore (firstFuel + 1) positive (by omega) (by omega)
        pair (included pair List.mem_cons_self) childNext before middle value atChild physical completed
      have advanced := called.bind _ _ _ _ _ childNext
      have tailOrigin : Steps (stepsBefore + firstFuel) (.edgeBody request .pure) state
          (.code ((SourceRecursiveIntersectionCode.walk
            (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
            (fun values => next (value :: values)))) middle :=
        atChild.trans _ _ _ _ _ _ _ _ advanced
      have restIncluded : ∀ candidate ∈ rest,
          candidate ∈ request.left.children.zip request.right.children := by
        intro candidate member
        exact included candidate (List.mem_cons_of_mem _ member)
      have later := ih (stepsBefore + firstFuel) (fun values => next (value :: values))
        tailOrigin (by omega) (by omega) first.1 restIncluded
      refine ⟨later.1, first.2.1.trans later.2.1, ?_, ?_⟩
      · intro child member
        cases member with
        | head => exact later.2.1.available value first.2.2.1
        | tail _ member => exact later.2.2.1 child member
      · intro child member atom occurrence
        cases member with
        | head => exact first.2.2.2 atom occurrence
        | tail _ member => exact later.2.2.2 child member atom occurrence

/-- Actual accepted child executions derive the result footprint and exact allocated endpoint. -/
theorem accepted_body_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (universeIdentity : Nat) (request : EdgeRequest Symbol Guard)
    (state after : State width) (first second combined : Allocated)
    (fuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical state.native)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint
      state.operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
      state.operations.constraints = .ok (some second))
    (accepted : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined))
    (done : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done result after)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : State width) (value : Value Symbol Guard),
        Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
        Physical first.native →
        SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first = .done value last →
        Physical last.native ∧ Extension first.native.machine last.native.machine ∧
          Available last.native.machine.heap value ∧
          ∀ atom ∈ atoms value, atom = .mu universeIdentity) :
    ∃ values middle count,
      count + 1 < fuel ∧
      SourceEqualityNativeDemandWalkExecution.Walk
        (fun pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)
        {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
          first second request.left.children.length request.right.children.length state.operations).2}
        values middle count ∧
      result = (run (makeEdge request.left.entry.key.symbol
        (SourceEqualityConjoinAllocation.readback combined) values) middle.native.machine.heap).1 ∧
      after = {middle with native := advance middle.native {middle.native.machine with heap :=
        (run (makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined)
          values) middle.native.machine.heap).2}} ∧
      result.children = values ∧
      ∀ child ∈ result.children, ∀ atom ∈ atoms child, atom = .mu universeIdentity := by
  obtain ⟨values, middle, count, bounded, walked, sameResult, sameAfter⟩ :=
    SourceEqualityNativeDemandAcceptedReadback.body_observation
      request state after first second combined fuel result arity left right accepted done
  let next : List (Value Symbol Guard) → Code Symbol Guard (EdgeValue Symbol Guard) :=
    fun values => .work (makeEdge request.left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values) .pure
  have one := body_ready request (.pure : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
    state arity first second combined left right accepted
  simp only [code_bind_pure] at one
  have origin : Steps 1 (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2)
        (request.left.children.zip request.right.children)).bind next))
      {state with operations := (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
        first second request.left.children.length request.right.children.length state.operations).2} :=
    .cons _ _ _ _ _ _ _ one (.refl _ _)
  have effects := walk_footprints universeIdentity fuel request state
    (request.left.children.zip request.right.children) _ values middle count walked
    1 next origin (by decide) (by omega) physical (by intro pair member; exact member) children
  have fields := MergedPhysicalGroupEdges.makeEdge_fields middle.native.machine.heap effects.1.machine.1
    request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values effects.2.2.1
  have sameChildren : result.children = values := by rw [sameResult]; exact fields.2.2
  refine ⟨values, middle, count, bounded, walked, sameResult, sameAfter, sameChildren, ?_⟩
  rw [sameChildren]
  exact effects.2.2.2

private theorem sentinel_body_footprint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (universeIdentity : Nat) (request : EdgeRequest Symbol Guard)
    (state reached after : State width) (fuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical state.native)
    (one : SourceEqualityNativeDemand.body request .pure state = sentinel request .pure reached)
    (sameNative : reached.native = state.native)
    (done : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done result after) :
    result.children = [.empty] ∧
      ∀ child ∈ result.children, ∀ atom ∈ atoms child, atom = .mu universeIdentity := by
  let built := run (makeEdge request.left.entry.key.symbol
    SourceEqualityConstraintConstructors.top [.empty]) reached.native.machine.heap
  let final : State width :=
    ⟨advance reached.native {reached.native.machine with heap := built.2},
      SourceEqualityMkEdgeAllocation.emptyField reached.operations⟩
  have canonical : SourceEqualityNativeDemand.execute 3 (.edgeBody request .pure) state = .done built.1 final := by
    simp only [SourceEqualityNativeDemand.execute, step, one]
    rfl
  have first := done_stable fuel 3 _ state after result done
  have second := done_stable 3 fuel _ state final built.1 canonical
  rw [Nat.add_comm 3 fuel] at second
  have sameResult := (Outcome.done.inj (first.symm.trans second)).1
  have heapFacts : InternedNestedFacts.Facts reached.native.machine.heap := by
    rw [sameNative]
    exact physical.machine.1
  have fields := MergedPhysicalGroupEdges.makeEdge_fields reached.native.machine.heap heapFacts
    request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    (by intro value member; rw [List.mem_singleton.mp member]; exact empty_available _)
  have sameChildren : result.children = [.empty] := by rw [sameResult]; exact fields.2.2
  refine ⟨sameChildren, ?_⟩
  intro child member atom occurrence
  rw [sameChildren] at member
  rw [List.mem_singleton.mp member] at occurrence
  have impossible : atom ∈ ([] : List _) := by simpa only [atoms] using occurrence
  cases impossible

private theorem completed_body_cases
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : EdgeRequest Symbol Guard) (state after : State width)
    (fuel : Nat) (result : EdgeValue Symbol Guard)
    (done : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done result after) :
    (∃ reached, SourceEqualityNativeDemand.body request .pure state = sentinel request .pure reached ∧
      reached.native = state.native) ∨
    ∃ first second combined,
      request.left.children.length = request.right.children.length ∧
      SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint
        state.operations.constraints = .ok (some first) ∧
      SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
        state.operations.constraints = .ok (some second) ∧
      (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
        request.left.children.length request.right.children.length state.operations).1 = .ok (.ready combined) := by
  cases fuel with
  | zero => cases done
  | succ fuel =>
      by_cases arity : request.left.children.length = request.right.children.length
      · cases left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint
          state.operations.constraints with
        | error message =>
            simp only [SourceEqualityNativeDemand.execute, step, SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left] at done
            cases done
        | ok found =>
            cases found with
            | none =>
                simp only [SourceEqualityNativeDemand.execute, step, SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left] at done
                cases done
            | some first =>
                cases right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint
                    state.operations.constraints with
                | error message =>
                    simp only [SourceEqualityNativeDemand.execute, step, SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left, right] at done
                    cases done
                | ok found =>
                    cases found with
                    | none =>
                        simp only [SourceEqualityNativeDemand.execute, step, SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left, right] at done
                        cases done
                    | some second =>
                        cases allocation : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le
                            first second request.left.children.length request.right.children.length state.operations).1 with
                        | error message =>
                            simp only [SourceEqualityNativeDemand.execute, step, SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left, right, allocation] at done
                            cases done
                        | ok decision =>
                            cases decision with
                            | mismatch =>
                                refine .inl ⟨{state with operations :=
                                  (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                                    request.left.children.length request.right.children.length state.operations).2}, ?_, rfl⟩
                                simp only [SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left, right, allocation]
                            | rejected =>
                                refine .inl ⟨{state with operations :=
                                  (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                                    request.left.children.length request.right.children.length state.operations).2}, ?_, rfl⟩
                                simp only [SourceEqualityNativeDemand.body, not_not_intro arity, ite_false, left, right, allocation]
                            | ready combined => exact .inr ⟨first, second, combined, arity, rfl, rfl, allocation⟩
      · exact .inl ⟨state, body_mismatch request _ state arity, rfl⟩

/-- Every completed actual edge body inherits only-U atoms from its shorter actual child calls. -/
theorem body_footprint_of_smaller_nodes
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (universeIdentity : Nat) (request : EdgeRequest Symbol Guard)
    (state after : State width) (fuel : Nat) (result : EdgeValue Symbol Guard)
    (physical : Physical state.native)
    (done : SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state = .done result after)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard))
        (first last : State width) (value : Value Symbol Guard),
        Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
        Physical first.native →
        SourceEqualityNativeDemand.execute childFuel (.code (requestNode request.domain pair.1 pair.2)) first = .done value last →
        Physical last.native ∧ Extension first.native.machine last.native.machine ∧
          Available last.native.machine.heap value ∧
          ∀ atom ∈ atoms value, atom = .mu universeIdentity) :
    ∀ child ∈ result.children, ∀ atom ∈ atoms child, atom = .mu universeIdentity := by
  rcases completed_body_cases request state after fuel result done with
    ⟨reached, one, sameNative⟩ | ⟨first, second, combined, arity, left, right, accepted⟩
  · exact (sentinel_body_footprint universeIdentity request state reached after fuel result
      physical one sameNative done).2
  · obtain ⟨values, middle, count, bounded, walked, sameResult, sameAfter, sameChildren, footprint⟩ :=
      accepted_body_footprint universeIdentity request state after first second combined fuel result
        physical arity left right accepted done children
    exact footprint

end MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyFootprints
