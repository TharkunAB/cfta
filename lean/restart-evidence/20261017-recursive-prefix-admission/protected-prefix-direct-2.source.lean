import MicroCFTA.SourceEqualityNativeDemandRunning
import MicroCFTA.SourceEqualityNativeDemandPrefixSplit
import MicroCFTA.SourceCurrentAllocatedNativePhysicalExecution
import MicroCFTA.SourceCurrentAllocatedNativeRequestBounds
import MicroCFTA.SourceCurrentAllocatedNativeDomainTrace

/-!
# Protected owners at actual checked finish prefixes

A crossed body prefix supplies its actual completed inner trace.
That trace retains the captured evaluating owner until its finish step.
The remaining prefix either stops at the frame or consumes it once.
-/

namespace MicroCFTA.SourceEqualityNativeDemandProtectedPrefix

open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand SourceEqualityNativeDemandBodyCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {Output : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A raw node-frame prefix stops before the frame or executes its one literal finish step. -/
theorem finish_node_cases (fuel handle : Nat) (value : Value Symbol Guard)
    (next : Code Symbol Guard Output) (before after : Checked width) (remaining : Control Output)
    (actual : Steps fuel (.code (.finishNode handle value next)) before remaining after) :
    (fuel = 0 ∧ remaining = .code (.finishNode handle value next) ∧ after = before) ∨
      (∃ rest, fuel = rest + 1 ∧ Steps rest (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishNode handle value before.native}
        remaining after) := by
  cases fuel with
  | zero =>
    obtain ⟨same, retained⟩ := steps_zero _ _ _ _ actual
    exact Or.inl ⟨rfl, same.symm, retained.symm⟩
  | succ fuel =>
    obtain ⟨rest, current, one, tail⟩ := steps_succ fuel _ _ _ _ actual
    obtain ⟨same, retained⟩ := Outcome.yielded.inj one
    rcases same with rfl
    rcases retained with rfl
    exact Or.inr ⟨fuel, rfl, tail⟩

/-- A raw edge-frame prefix stops before the frame or executes its one literal finish step. -/
theorem finish_edge_cases (fuel handle : Nat) (value : EdgeValue Symbol Guard)
    (next : Code Symbol Guard Output) (before after : Checked width) (remaining : Control Output)
    (actual : Steps fuel (.code (.finishEdge handle value next)) before remaining after) :
    (fuel = 0 ∧ remaining = .code (.finishEdge handle value next) ∧ after = before) ∨
      (∃ rest, fuel = rest + 1 ∧ Steps rest (.code next)
        {before with native := SourceRecursiveIntersectionThunks.finishEdge handle value before.native}
        remaining after) := by
  cases fuel with
  | zero =>
    obtain ⟨same, retained⟩ := steps_zero _ _ _ _ actual
    exact Or.inl ⟨rfl, same.symm, retained.symm⟩
  | succ fuel =>
    obtain ⟨rest, current, one, tail⟩ := steps_succ fuel _ _ _ _ actual
    obtain ⟨same, retained⟩ := Outcome.yielded.inj one
    rcases same with rfl
    rcases retained with rfl
    exact Or.inr ⟨fuel, rfl, tail⟩

/-- An actual compiled body trace retains its exact evaluating node owner before publication. -/
theorem node_body_owner (fuel handle : Nat) (request : NodeRequest Symbol Guard)
    (before after : Checked width) (value : Value Symbol Guard)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (actual : Steps fuel (.code (compileNode request)) before (.code (.pure value)) after) :
    after.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value after.native).nodes.cells handle =
        some ⟨request, .returned value⟩ := by
  exact SourceEqualityNativeDemandRunning.node_body_cell (fuel + 1) handle request before after value
    shape running (trace_done fuel _ before after value actual)

/-- An actual checked edge-body trace retains its exact evaluating edge owner before publication. -/
theorem edge_body_owner (fuel handle : Nat) (request : EdgeRequest Symbol Guard)
    (before after : Checked width) (value : EdgeValue Symbol Guard)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (actual : Steps fuel (.edgeBody request .pure) before (.code (.pure value)) after) :
    after.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishEdge handle value after.native).edges.cells handle =
        some ⟨request, .returned value⟩ := by
  exact SourceEqualityNativeDemandRunning.edge_body_cell (fuel + 1) handle request before after value
    shape running (trace_done fuel _ before after value actual)

/-- A node wrapper prefix exposes a shorter actual body trace and the captured finish owner. -/
theorem node_cases (fuel handle : Nat) (request : NodeRequest Symbol Guard)
    (next : Value Symbol Guard → Code Symbol Guard Output)
    (before after : Checked width) (remaining : Control Output)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (actual : Steps fuel ((.code (compileNode request) : Control (Value Symbol Guard)).bind
      (fun value => .finishNode handle value (next value))) before remaining after) :
    (∃ inner, Steps fuel (.code (compileNode request)) before inner after ∧
      (∀ value, inner ≠ .code (.pure value)) ∧
      remaining = inner.bind (fun value => .finishNode handle value (next value))) ∨
    (∃ bodyFuel frameFuel value middle, bodyFuel + frameFuel = fuel ∧ bodyFuel < fuel + 1 ∧
      Steps bodyFuel (.code (compileNode request)) before (.code (.pure value)) middle ∧
      middle.native.nodes.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishNode handle value middle.native).nodes.cells handle =
        some ⟨request, .returned value⟩ ∧
      ((frameFuel = 0 ∧ remaining = .code (.finishNode handle value (next value)) ∧ after = middle) ∨
        (∃ rest, frameFuel = rest + 1 ∧ Steps rest (.code (next value))
          {middle with native := SourceRecursiveIntersectionThunks.finishNode handle value middle.native}
          remaining after))) := by
  rcases steps_bind_cases fuel (.code (compileNode request))
      (fun value => .finishNode handle value (next value)) before after remaining actual with
    inside | ⟨bodyFuel, frameFuel, value, middle, count, bodyTrace, frameTrace⟩
  · exact Or.inl inside
  · have owner := node_body_owner bodyFuel handle request before middle value shape running bodyTrace
    exact Or.inr ⟨bodyFuel, frameFuel, value, middle, count, by omega, bodyTrace, owner.1, owner.2,
      finish_node_cases frameFuel handle value (next value) middle after remaining frameTrace⟩

/-- An edge wrapper prefix retains the checked body state and the captured finish owner. -/
theorem edge_cases (fuel handle : Nat) (request : EdgeRequest Symbol Guard)
    (next : EdgeValue Symbol Guard → Code Symbol Guard Output)
    (before after : Checked width) (remaining : Control Output)
    (shape : SourceRecursiveIntersectionNative.Shape before.native)
    (running : before.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (actual : Steps fuel ((.edgeBody request .pure : Control (EdgeValue Symbol Guard)).bind
      (fun value => .finishEdge handle value (next value))) before remaining after) :
    (∃ inner, Steps fuel (.edgeBody request .pure) before inner after ∧
      (∀ value, inner ≠ .code (.pure value)) ∧
      remaining = inner.bind (fun value => .finishEdge handle value (next value))) ∨
    (∃ bodyFuel frameFuel value middle, bodyFuel + frameFuel = fuel ∧ bodyFuel < fuel + 1 ∧
      Steps bodyFuel (.edgeBody request .pure) before (.code (.pure value)) middle ∧
      middle.native.edges.cells handle = some ⟨request, .evaluating⟩ ∧
      (SourceRecursiveIntersectionThunks.finishEdge handle value middle.native).edges.cells handle =
        some ⟨request, .returned value⟩ ∧
      ((frameFuel = 0 ∧ remaining = .code (.finishEdge handle value (next value)) ∧ after = middle) ∨
        (∃ rest, frameFuel = rest + 1 ∧ Steps rest (.code (next value))
          {middle with native := SourceRecursiveIntersectionThunks.finishEdge handle value middle.native}
          remaining after))) := by
  rcases steps_bind_cases fuel (.edgeBody request .pure)
      (fun value => .finishEdge handle value (next value)) before after remaining actual with
    inside | ⟨bodyFuel, frameFuel, value, middle, count, bodyTrace, frameTrace⟩
  · exact Or.inl inside
  · have owner := edge_body_owner bodyFuel handle request before middle value shape running bodyTrace
    exact Or.inr ⟨bodyFuel, frameFuel, value, middle, count, by omega, bodyTrace, owner.1, owner.2,
      finish_edge_cases frameFuel handle value (next value) middle after remaining frameTrace⟩

/-- Appending code retains the current physical check before an inner pure return. -/
theorem inputs_bind {A B : Type} (control : Control A) (next : A → Code Symbol Guard B)
    (state : Checked width) (nonpure : ∀ value, control ≠ .code (.pure value))
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control state) :
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (control.bind next) state := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact inputs | exact False.elim (nonpure _ rfl)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Appending code retains the current word check before an inner pure return. -/
theorem words_bind {A B : Type} (control : Control A) (next : A → Code Symbol Guard B)
    (nonpure : ∀ value, control ≠ .code (.pure value))
    (words : SourceCurrentAllocatedNativeRequestBounds.Words width control) :
    SourceCurrentAllocatedNativeRequestBounds.Words width (control.bind next) := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact words | exact False.elim (nonpure _ rfl)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Appending code retains the current enter admission before an inner pure return. -/
theorem entered_bind {A B : Type} (inventory : List IntersectionFlatMemoKeyDomain.DomainKey)
    (control : Control A) (next : A → Code Symbol Guard B)
    (nonpure : ∀ value, control ≠ .code (.pure value))
    (admitted : SourceCurrentAllocatedNativeDomainTrace.Entered inventory control) :
    SourceCurrentAllocatedNativeDomainTrace.Entered inventory (control.bind next) := by
  cases control with
  | edgeBody => trivial
  | code code => cases code <;> first | exact admitted | exact False.elim (nonpure _ rfl)

end MicroCFTA.SourceEqualityNativeDemandProtectedPrefix
