import MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned

/-!
# Returned laws through actual source reference reads

Missing bindings and missing payloads retain their real failure controls.
A successful physical read fixes the ordered child query.
Its actual smaller run supplies both memo laws and the same result law.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeReferenceBodyReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat}

set_option autoImplicit false

/-- A failure control retains the exact state at every supplied budget. -/
private theorem fail_endpoint_state
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (failure : SourceRecursiveIntersectionKernel.Failure)
    (state : Checked width) :
    (SourceEqualityNativeDemand.execute fuel
      (.code (.fail failure : Code Symbol Guard (Value Symbol Guard))) state).state = state := by
  cases fuel <;> rfl

/-- A real failure control cannot yield a pure result trace. -/
private theorem fail_no_pure_trace
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (failure : SourceRecursiveIntersectionKernel.Failure)
    (state after : Checked width) (value : Value Symbol Guard)
    (actual : Steps fuel (.code (.fail failure)) state (.code (.pure value)) after) : False := by
  cases fuel with
  | zero => cases (steps_zero _ _ _ _ actual).1
  | succ fuel =>
      obtain ⟨rest, middle, one, _tail⟩ := steps_succ fuel _ _ _ _ actual
      cases one

/-- The source reference compiler starts with a read or a failure, never a pure return. -/
private theorem reference_not_pure
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (value : Value Symbol Guard) :
    compileReference domain name other left ≠ .pure value := by
  intro impossible
  unfold compileReference at impossible
  split at impossible <;> cases impossible

/-- Remove one real observed source step from a pure-result trace. -/
private theorem tail_of_step
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control next : Control (Value Symbol Guard))
    (state middle after : Checked width) (value : Value Symbol Guard)
    (one : SourceEqualityNativeDemand.step control state = .yielded next middle)
    (actual : Steps (fuel + 1) control state (.code (.pure value)) after) :
    Steps fuel next middle (.code (.pure value)) after := by
  obtain ⟨rest, reached, observed, tail⟩ := steps_succ fuel _ _ _ _ actual
  obtain ⟨sameControl, sameState⟩ := Outcome.yielded.inj (one.symm.trans observed)
  subst rest
  subst reached
  exact tail

/-- Actual physical reference reads retain both laws and the same smaller child result law. -/
theorem reference_body_returned_of_child_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (resultLaw : Value Symbol Guard → Prop)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Checked width) (fuel : Nat)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (children : ∀ bound : Value Symbol Guard,
      SourcePreparedSharedRows.read state.native.machine.heap name = some bound →
      ∀ childFuel, childFuel < fuel →
      Steps 1 (.code (compileReference domain name other left)) state
        (.code (if left then requestNode domain bound other else requestNode domain other bound)) state →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (if left then requestNode domain bound other else requestNode domain other bound)) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (if left then requestNode domain bound other else requestNode domain other bound)) state).state.native.edges ∧
      (∀ (value : Value Symbol Guard) (after : Checked width),
        Steps childFuel (.code (if left then requestNode domain bound other else requestNode domain other bound))
          state (.code (.pure value)) after → resultLaw value)) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (compileReference domain name other left)) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (compileReference domain name other left)) state).state.native.edges ∧
    (∀ count, count ≤ fuel → ∀ (value : Value Symbol Guard) (after : Checked width),
      Steps count (.code (compileReference domain name other left)) state (.code (.pure value)) after →
      resultLaw value) ∧
    (∀ (value : Value Symbol Guard) (after : Checked width),
      SourceEqualityNativeDemand.execute fuel (.code (compileReference domain name other left)) state =
        .done value after → resultLaw value) := by
  have pureResults : ∀ count, count ≤ fuel → ∀ (value : Value Symbol Guard) (after : Checked width),
      Steps count (.code (compileReference domain name other left)) state (.code (.pure value)) after →
      resultLaw value := by
    intro count bounded value after actual
    cases count with
    | zero =>
        have same := (steps_zero _ _ _ _ actual).1
        exact False.elim (reference_not_pure domain name other left value (Control.code.inj same))
    | succ count =>
        by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
        · cases reading : SourcePreparedSharedRows.read state.native.machine.heap name with
          | none =>
              have one : SourceEqualityNativeDemand.step (.code (compileReference domain name other left)) state =
                  .yielded (.code (.fail (.missingPayload name))) state := by
                simp [compileReference, member, SourceEqualityNativeDemand.step,
                  SourceRecursiveIntersectionNative.step, reading, SourceEqualityNativeDemand.lift]
              exact False.elim (fail_no_pure_trace count (.missingPayload name) state after value
                (tail_of_step count _ _ state state after value one actual))
          | some bound =>
              have one : SourceEqualityNativeDemand.step (.code (compileReference domain name other left)) state =
                  .yielded (.code (if left then requestNode domain bound other else requestNode domain other bound)) state := by
                cases left <;> simp [compileReference, member, SourceEqualityNativeDemand.step,
                  SourceRecursiveIntersectionNative.step, reading, SourceEqualityNativeDemand.lift]
              have origin : Steps 1 (.code (compileReference domain name other left)) state
                  (.code (if left then requestNode domain bound other else requestNode domain other bound)) state :=
                .cons _ _ _ _ _ _ _ one (.refl _ _)
              have child := children bound reading count (by omega) origin
              exact child.2.2 value after (tail_of_step count _ _ state state after value one actual)
        · have compiled : compileReference domain name other left = .fail (.missingBinder name) := by
            simp [compileReference, member]
          rw [compiled] at actual
          exact False.elim (fail_no_pure_trace (count + 1) (.missingBinder name) state after value actual)
  have returned :
      Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
        (.code (compileReference domain name other left)) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
        (.code (compileReference domain name other left)) state).state.native.edges := by
    cases fuel with
    | zero => exact ⟨nodes, edges⟩
    | succ fuel =>
        by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
        · cases reading : SourcePreparedSharedRows.read state.native.machine.heap name with
          | none =>
              have one : SourceEqualityNativeDemand.step (.code (compileReference domain name other left)) state =
                  .yielded (.code (.fail (.missingPayload name))) state := by
                simp [compileReference, member, SourceEqualityNativeDemand.step,
                  SourceRecursiveIntersectionNative.step, reading, SourceEqualityNativeDemand.lift]
              simpa only [SourceEqualityNativeDemand.execute, one, fail_endpoint_state] using And.intro nodes edges
          | some bound =>
              have one : SourceEqualityNativeDemand.step (.code (compileReference domain name other left)) state =
                  .yielded (.code (if left then requestNode domain bound other else requestNode domain other bound)) state := by
                cases left <;> simp [compileReference, member, SourceEqualityNativeDemand.step,
                  SourceRecursiveIntersectionNative.step, reading, SourceEqualityNativeDemand.lift]
              have origin : Steps 1 (.code (compileReference domain name other left)) state
                  (.code (if left then requestNode domain bound other else requestNode domain other bound)) state :=
                .cons _ _ _ _ _ _ _ one (.refl _ _)
              have child := children bound reading fuel (by omega) origin
              simpa only [SourceEqualityNativeDemand.execute, one] using And.intro child.1 child.2.1
        · have compiled : compileReference domain name other left = .fail (.missingBinder name) := by
            simp [compileReference, member]
          simpa only [compiled, fail_endpoint_state] using And.intro nodes edges
  refine ⟨returned.1, returned.2, pureResults, ?_⟩
  intro value after done
  obtain ⟨count, shorter, actual⟩ := done_trace fuel _ state after value done
  exact pureResults count (Nat.le_of_lt shorter) value after actual

end MicroCFTA.SourceCurrentAllocatedNativeReferenceBodyReturned

#print axioms MicroCFTA.SourceCurrentAllocatedNativeReferenceBodyReturned.reference_body_returned_of_child_induction
