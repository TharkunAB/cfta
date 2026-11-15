import MicroCFTA.SourceEqualityNativeDemandPrefixSplit
import MicroCFTA.SourceEqualityNativeDemandBodyYield
import MicroCFTA.SourceEqualityNativeDemandOperations
import MicroCFTA.SourceCurrentAllocatedNativeContextCache

/-!
# Returned properties at every actual edge-body endpoint

An appended execution retains an inner endpoint or reaches its continuation.
The accepted child walk uses that operational split at each actual child.
Every child hypothesis retains the parent execution prefix and original fuel.
Field checks, sentinel code and final edge construction retain both memo tables.
This file does not derive child hypotheses from initialized source history.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Pair" => Value Symbol Guard × Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A B : Type}

set_option autoImplicit false

/-- Every appended endpoint comes from the inner execution or its actual reached continuation. -/
theorem bind_endpoint_state_cases
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (control : Control A) (next : A → Code Symbol Guard B) (state : Checked width) :
    (SourceEqualityNativeDemand.execute fuel (control.bind next) state).state =
      (SourceEqualityNativeDemand.execute fuel control state).state ∨
    ∃ steps value middle, steps < fuel ∧
      Steps steps control state (.code (.pure value)) middle ∧
      (SourceEqualityNativeDemand.execute fuel (control.bind next) state).state =
        (SourceEqualityNativeDemand.execute (fuel - steps) (.code (next value)) middle).state := by
  induction fuel generalizing control state with
  | zero => exact .inl rfl
  | succ fuel ih =>
      have appended := step_bind control next state
      cases one : SourceEqualityNativeDemand.step control state with
      | yielded rest reached =>
          rw [one, appendStep] at appended
          rcases ih rest reached with same | ⟨steps, value, middle, bounded, called, same⟩
          · exact .inl (by
              simpa only [SourceEqualityNativeDemand.execute, appended, one] using same)
          · refine .inr ⟨steps + 1, value, middle, by omega,
              .cons _ _ _ _ _ _ _ one called, ?_⟩
            have sameBudget : (fuel + 1) - (steps + 1) = fuel - steps := by omega
            simpa only [SourceEqualityNativeDemand.execute, appended, sameBudget] using same
      | done value reached =>
          obtain ⟨pure, retained⟩ := (step_done_iff control state reached value).mp one
          subst control
          subst reached
          exact .inr ⟨0, value, state, by omega, .refl _ _, by
            simp only [Control.bind, Code.bind, Nat.sub_zero]⟩
      | failed failure reached | constraintError message reached | blocked reason rest reached =>
          rw [one, appendStep] at appended
          exact .inl (by
            simp only [SourceEqualityNativeDemand.execute, appended, one, Outcome.state])

private theorem work_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (job : Work Symbol Guard (EdgeValue Symbol Guard)) (state : Checked width)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (fuel : Nat) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel (.code (.work job .pure)) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel (.code (.work job .pure)) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      let built := run job state.native.machine.heap
      let after : Checked width :=
        ⟨advance state.native {state.native.machine with heap := built.2}, state.operations⟩
      have one : SourceEqualityNativeDemand.step (.code (.work job .pure)) state =
          .yielded (.code (.pure built.1)) after := by rfl
      have endpoint : (SourceEqualityNativeDemand.execute (fuel + 1)
          (.code (.work job .pure)) state).state = after := by
        rw [SourceEqualityNativeDemand.execute, one]
        cases fuel <;> rfl
      rw [endpoint]
      exact ⟨nodes, edges⟩

private theorem walk_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (state : Checked width) (fuel : Nat)
    (pairs : List Pair) (before : Checked width) (remaining stepsBefore : Nat)
    (build : List (Value Symbol Guard) → Work Symbol Guard (EdgeValue Symbol Guard))
    (origin : Steps stepsBefore (.edgeBody request .pure) state
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind
        (fun values => .work (build values) .pure))) before)
    (positive : 0 < stepsBefore) (bounded : stepsBefore + remaining ≤ fuel)
    (included : ∀ pair ∈ pairs, pair ∈ request.left.children.zip request.right.children)
    (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
        Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
        Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
        Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode request.domain pair.1 pair.2)) first).state.native.nodes ∧
        Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode request.domain pair.1 pair.2)) first).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute remaining
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind
        (fun values => .work (build values) .pure))) before).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute remaining
      (.code ((SourceRecursiveIntersectionCode.walk
        (fun pair : Pair => requestNode request.domain pair.1 pair.2) pairs).bind
        (fun values => .work (build values) .pure))) before).state.native.edges := by
  induction pairs generalizing before remaining stepsBefore build with
  | nil =>
      simpa only [SourceRecursiveIntersectionCode.walk, Code.bind] using
        work_returned nodeLaw edgeLaw (build []) before nodes edges remaining
  | cons pair rest ih =>
      let next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
        fun value => (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
          (fun values => .work (build (value :: values)) .pure)
      have sameCode : (SourceRecursiveIntersectionCode.walk
          (fun pair : Pair => requestNode request.domain pair.1 pair.2) (pair :: rest)).bind
          (fun values => .work (build values) .pure) =
          (requestNode request.domain pair.1 pair.2).bind next := by
        simp only [SourceRecursiveIntersectionCode.walk, Code.bind_assoc, Code.bind, next]
      have atChild : Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) before := by
        simpa only [sameCode] using origin
      rw [sameCode]
      rcases bind_endpoint_state_cases remaining (.code (requestNode request.domain pair.1 pair.2)) next before with
        same | ⟨steps, value, middle, shorter, called, same⟩
      · rw [same]
        exact children stepsBefore remaining positive bounded (by omega)
          pair (included pair List.mem_cons_self) next before atChild nodes edges
      · have completed := trace_done steps _ before middle value called
        have atMiddle := children stepsBefore (steps + 1) positive (by omega) (by omega)
          pair (included pair List.mem_cons_self) next before atChild nodes edges
        rw [completed] at atMiddle
        have advanced := called.bind _ _ _ _ _ next
        have tailOrigin : Steps (stepsBefore + steps) (.edgeBody request .pure) state
            (.code ((SourceRecursiveIntersectionCode.walk
              (fun pair : Pair => requestNode request.domain pair.1 pair.2) rest).bind
              (fun values => .work (build (value :: values)) .pure))) middle :=
          atChild.trans _ _ _ _ _ _ _ _ advanced
        have restIncluded : ∀ candidate ∈ rest,
            candidate ∈ request.left.children.zip request.right.children := by
          intro candidate member
          exact included candidate (List.mem_cons_of_mem _ member)
        have later := ih middle (remaining - steps) (stepsBefore + steps)
          (fun values => build (value :: values)) tailOrigin (by omega) (by omega)
          restIncluded atMiddle.1 atMiddle.2
        rw [same]
        exact later

private theorem yielded_body_code
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    code = SourceEqualityNativeCheckedCode.sentinel request.left ∨
      ∃ combined, code = SourceEqualityNativeCheckedCode.children request.domain request.left request.right combined := by
  unfold SourceEqualityNativeDemand.body at yielded
  split at yielded
  · simp only [sentinel, code_bind_pure] at yielded
    cases yielded
    exact .inl rfl
  · split at yielded
    · cases yielded
    · cases yielded
    · split at yielded
      · cases yielded
      · cases yielded
      · dsimp only at yielded
        split at yielded
        · cases yielded
        · simp only [sentinel, code_bind_pure] at yielded
          cases yielded
          exact .inl rfl
        · simp only [sentinel, code_bind_pure] at yielded
          cases yielded
          exact .inl rfl
        · simp only [code_bind_pure] at yielded
          cases yielded
          exact .inr ⟨_, rfl⟩

/-- Every supplied-fuel edge-body endpoint retains both prior returned laws through its actual smaller children. -/
theorem edge_body_returned_all_fuels
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (state : Checked width) (fuel : Nat)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (children : ∀ stepsBefore childFuel, 0 < stepsBefore → stepsBefore + childFuel ≤ fuel → childFuel < fuel →
      ∀ pair ∈ request.left.children.zip request.right.children,
      ∀ (next : Value Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
        Steps stepsBefore (.edgeBody request .pure) state
          (.code ((requestNode request.domain pair.1 pair.2).bind next)) first →
        Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
        Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode request.domain pair.1 pair.2)) first).state.native.nodes ∧
        Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
          (.code (requestNode request.domain pair.1 pair.2)) first).state.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel (.edgeBody request .pure) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      have nativeSame := SourceEqualityNativeDemandOperations.body_native request .pure state
      cases one : SourceEqualityNativeDemand.body request .pure state with
      | yielded control reached =>
          simp only [one, Outcome.state] at nativeSame
          have priorNodes : Returned nodeLaw reached.native.nodes := by rw [nativeSame]; exact nodes
          have priorEdges : Returned edgeLaw reached.native.edges := by rw [nativeSame]; exact edges
          obtain ⟨code, rfl⟩ := SourceEqualityNativeDemandBodyYield.pure_yielded_code request state reached control one
          have origin : Steps 1 (.edgeBody request .pure) state (.code code) reached :=
            .cons _ _ _ _ _ _ _ one (.refl _ _)
          simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, one]
          rcases yielded_body_code request state reached code one with rfl | ⟨combined, rfl⟩
          · exact work_returned nodeLaw edgeLaw _ reached priorNodes priorEdges fuel
          · exact walk_returned nodeLaw edgeLaw request state (fuel + 1)
              (request.left.children.zip request.right.children) reached fuel 1
              (fun values => makeEdge request.left.entry.key.symbol
                (SourceEqualityConjoinAllocation.readback combined) values)
              origin (by decide) (by omega) (by intro pair member; exact member)
              priorNodes priorEdges children
      | done value reached | failed failure reached | constraintError message reached | blocked reason control reached =>
          simp only [one, Outcome.state] at nativeSame
          simp only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step, one, Outcome.state]
          rw [nativeSame]
          exact ⟨nodes, edges⟩

end MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
