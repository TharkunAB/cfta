import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceEqualityNativeCheckedCode
import MicroCFTA.SourceEqualityNativeDemandContinuation
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Mass bounds at literal checked edge assembly prefixes

Initial resident operands bound the original zip width. An earlier actual
child walk supplies the ordered returned list and its current availability.
The causal store bound at that reached prefix supplies every child mass.
No child size law or completed final edge is a premise. This is a local
assembler bound. It does not produce a store bound for the whole query.
-/
namespace MicroCFTA.SourceEqualityNativeCheckedMass
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open InternedFreshOrdinaryResultMass (inflate)
local notation "Stored" => InternedValueMassHeap.Stored
local notation "Mass" => InternedValueMass.value
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint Formula

/-- An original resident row obtains its literal width from the causal initial store. -/
theorem operand_width (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) : edge.children.length ≤ bound := by
  have measured := InternedValueMassHeap.resident state stored edge resident
  rw [InternedValueMass.edge_children, InternedValueMass.values_eq_length_sum] at measured
  omega

/-- The accepted ordered zip uses no more positions than the original resident operand. -/
theorem zip_width (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (left right : EdgeValue Symbol Guard) (resident : EdgeResident state left) :
    (left.children.zip right.children).length ≤ bound := by
  have width := operand_width state bound stored left resident
  rw [List.length_zip]
  exact Nat.le_trans (Nat.min_le_left _ _) width

/-- The literal earlier child prefix retains ordered available outputs at its own returned heap. -/
theorem children_prefix (nodes : NodeCall Symbol Guard)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (before current : Machine Symbol Guard) (values : List (Value Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before) (known : Domain before domain)
    (leftResident : EdgeResident before.heap left) (rightResident : EdgeResident before.heap right)
    (actual : WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
      (left.children.zip right.children) before values current) :
    SourceRecursiveIntersectionKernel.Valid current ∧ Values current.heap values ∧
      values.length = (left.children.zip right.children).length := by
  have checked := children_checked (fun domain left right => nodes ⟨domain, left, right⟩)
    calls domain (left.children.zip right.children) before valid known (by
      intro pair member
      have inside := List.of_mem_zip member
      exact ⟨valid.1.cached.edges _ _ leftResident _ inside.1,
        valid.1.cached.edges _ _ rightResident _ inside.2⟩)
  have done := (walk_done_iff _ _ _ _ _).mpr actual
  exact ⟨by simpa only [done, Result.state] using checked.valid,
    checked.result values current done, actual.length⟩

/-- Current availability and the current causal store bound the actual accumulated child list. -/
theorem accumulated_mass (state : State Symbol Guard) (bound : Nat) (stored : Stored bound state)
    (values : List (Value Symbol Guard)) (available : Values state values) :
    InternedValueMass.values values ≤ values.length * (1 + bound) :=
  SourceRecursiveIntersectionWorkMass.values_le values bound
    (fun value member => InternedValueMassHeap.available state stored value (available value member))

/-- Accepted assembly uses the actual earlier walk and a store bound at that reached prefix. -/
theorem children_assembled [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard) (combined : Allocated)
    (before current : Machine Symbol Guard) (values : List (Value Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before) (known : Domain before domain)
    (leftResident : EdgeResident before.heap left) (rightResident : EdgeResident before.heap right)
    (initialBound currentBound : Nat) (initialStored : Stored initialBound before.heap)
    (prefixStored : Stored currentBound current.heap)
    (actual : WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
      (left.children.zip right.children) before values current) :
    let made := run (makeEdge left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) current.heap
    interpret nodes edges (SourceEqualityNativeCheckedCode.children domain left right combined) before =
        .done made.1 {current with heap := made.2} ∧
      values.length = (left.children.zip right.children).length ∧
      made.1.entry.key.symbol = left.entry.key.symbol ∧
      made.1.entry.key.constraint = SourceEqualityConjoinAllocation.readback combined ∧ made.1.children = values ∧
      Stored (inflate initialBound currentBound) made.2 ∧ InternedValueMass.edge made.1 ≤ inflate initialBound currentBound ∧
      made.2.nodes.next = current.heap.nodes.next ∧ made.2.edges.next ≤ current.heap.edges.next + 1 := by
  obtain ⟨currentValid, available, length⟩ := children_prefix nodes calls domain left right before current values
    valid known leftResident rightResident actual
  have width : values.length ≤ initialBound := by
    rw [length]
    exact zip_width before.heap initialBound initialStored left right leftResident
  have made := SourceRecursiveIntersectionWorkMass.edge left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values current.heap prefixStored
    (fun value member => InternedValueMassHeap.available current.heap prefixStored value (available value member))
  have increase : inflate values.length currentBound ≤ inflate initialBound currentBound := by
    have product := Nat.mul_le_mul_right (1 + currentBound) width
    simp only [inflate]
    omega
  have fields := MergedPhysicalGroupEdges.makeEdge_fields current.heap currentValid.1 left.entry.key.symbol
    (SourceEqualityConjoinAllocation.readback combined) values available
  refine ⟨?_, length, fields.1, fields.2.1, fields.2.2,
    made.1.mono increase, Nat.le_trans made.2.1 increase, made.2.2.1, made.2.2.2⟩
  rw [SourceEqualityNativeCheckedCode.children_exact, (walk_done_iff _ _ _ _ _).mpr actual]
  rfl

/-- Rejection constructs its own sentinel with no child call or child result premise. -/
theorem sentinel_assembled [DecidableEq (EdgeKey Symbol Guard)]
    (nodes : NodeCall Symbol Guard) (edges : EdgeCall Symbol Guard) (left : EdgeValue Symbol Guard)
    (before : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid before)
    (bound : Nat) (stored : Stored bound before.heap) :
    let made := run (makeEdge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) before.heap
    interpret nodes edges (SourceEqualityNativeCheckedCode.sentinel left) before =
        .done made.1 {before with heap := made.2} ∧
      made.1.entry.key.symbol = left.entry.key.symbol ∧
      made.1.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧ made.1.children = [.empty] ∧
      Stored (max bound 3) made.2 ∧ InternedValueMass.edge made.1 ≤ max bound 3 ∧
      made.2.nodes.next = before.heap.nodes.next ∧ made.2.edges.next ≤ before.heap.edges.next + 1 := by
  have available : Values before.heap [.empty] := by
    intro value member
    cases List.mem_singleton.mp member
    exact empty_available _
  have made := InternedValueMassConstructors.edge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] before.heap stored
  have counts := SourceRecursiveIntersectionWorkMass.edge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] before.heap stored
    (fun value member => InternedValueMassHeap.available before.heap stored value (available value member))
  have fields := MergedPhysicalGroupEdges.makeEdge_fields before.heap valid.1 left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty] available
  refine ⟨?_, fields.1, fields.2.1, fields.2.2, ?_, ?_, counts.2.2.1, counts.2.2.2⟩
  · rw [SourceEqualityNativeCheckedCode.sentinel_exact]
    rfl
  · simpa only [InternedValueMass.values, InternedValueMass.value] using made.1
  · simpa only [InternedValueMass.values, InternedValueMass.value] using made.2

section Checked
local notation "SourceSymbol" => SourceObservations.Label FullSyntax.Formula
local notation "SourceGuard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- A literal checked edge Work retains native tables, domains, and equality operations at its exact yield. -/
theorem checked_edge_step [DecidableEq SourceSymbol] [DecidableEq (EdgeKey SourceSymbol SourceGuard)]
    (symbol : SourceSymbol) (guard : SourceGuard) (values : List (Value SourceSymbol SourceGuard))
    (before : Checked width) (bound : Nat) (stored : Stored bound before.native.machine.heap)
    (available : Values before.native.machine.heap values)
    (next : EdgeValue SourceSymbol SourceGuard → Code SourceSymbol SourceGuard Output) :
    let made := run (makeEdge symbol guard values) before.native.machine.heap
    let after : Checked width := ⟨advance before.native {before.native.machine with heap := made.2}, before.operations⟩
    SourceEqualityNativeDemand.step (.code (.work (makeEdge symbol guard values) next)) before =
        .yielded (.code (next made.1)) after ∧
      Stored (inflate values.length bound) after.native.machine.heap ∧
      InternedValueMass.edge made.1 ≤ inflate values.length bound ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  have made := SourceRecursiveIntersectionWorkMass.edge symbol guard values before.native.machine.heap stored
    (fun value member => InternedValueMassHeap.available _ stored value (available value member))
  exact ⟨rfl, made⟩

/-- A checked body only chooses its literal accepted or sentinel code and retains the whole native state. -/
theorem body_choice (request : EdgeRequest SourceSymbol SourceGuard) (before after : Checked width)
    (code : Code SourceSymbol SourceGuard (EdgeValue SourceSymbol SourceGuard))
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    after.native = before.native ∧
      (code = SourceEqualityNativeCheckedCode.sentinel request.left ∨
        ∃ combined, request.left.children.length = request.right.children.length ∧
          code = SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined) := by
  have same := SourceEqualityNativeDemandOperations.body_native request .pure before
  have unchanged : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using same
  refine ⟨unchanged, ?_⟩
  by_cases mismatch : request.left.children.length ≠ request.right.children.length
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left mismatch, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact .inl rfl
  · simp only [SourceEqualityNativeDemand.body, ite_eq_right mismatch] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    cases checked : SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
                      request.left.children.length request.right.children.length before.operations with
                    | mk result operations =>
                        simp only [checked] at yielded
                        cases result with
                        | error message => cases yielded
                        | ok branch =>
                            cases branch with
                            | mismatch | rejected =>
                                simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
                                cases yielded
                                exact .inl rfl
                            | ready combined =>
                                simp only [SourceEqualityNativeDemand.code_bind_pure] at yielded
                                cases yielded
                                exact .inr ⟨combined, by omega, rfl⟩
end Checked
end MicroCFTA.SourceEqualityNativeCheckedMass
