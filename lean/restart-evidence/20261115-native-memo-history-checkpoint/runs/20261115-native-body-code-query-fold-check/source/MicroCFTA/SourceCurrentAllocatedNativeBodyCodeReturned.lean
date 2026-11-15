import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
import MicroCFTA.SourceRecursiveIntersectionBodyCode

/-!
# Returned laws through actual source bodies

BodyCode excludes explicit native finish instructions.
Every recursive request retains its actual outer prefix and continuation.
The child budget decreases from the original parent budget.
No result law or semantic model is required for a source body.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable {width : Nat} {A ParentOutput : Type}

set_option autoImplicit false

/-- An actual source step extends the same outer prefix with its real continuation. -/
private theorem prefix_yield
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (original : Control ParentOutput) (initial : Checked width)
    (code reached : Code Symbol Guard A) (finalNext : A → Code Symbol Guard ParentOutput)
    (before after : Checked width) (stepsBefore : Nat)
    (origin : Steps stepsBefore original initial (.code (code.bind finalNext)) before)
    (one : step (.code code) before = .yielded (.code reached) after) :
    Steps (stepsBefore + 1) original initial (.code (reached.bind finalNext)) after := by
  have lifted := step_bind (.code code) finalNext before
  rw [one, appendStep] at lifted
  have actual : step (.code (code.bind finalNext)) before =
      .yielded (.code (reached.bind finalNext)) after := lifted
  exact origin.trans _ _ _ _ _ _ _ _
    (.cons _ _ _ _ _ _ _ actual (.refl _ _))

/-- Source bodies preserve both returned laws through genuine smaller actual queries. -/
theorem body_code_returned_of_outer_query_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (original : Control ParentOutput) (initial : Checked width) (parentFuel : Nat)
    (nodeQueries : ∀ (request : NodeRequest Symbol Guard)
      (next : Value Symbol Guard → Code Symbol Guard ParentOutput) (before : Checked width)
      (stepsBefore childFuel : Nat),
      0 < stepsBefore → stepsBefore + childFuel ≤ parentFuel → childFuel < parentFuel →
      Steps stepsBefore original initial
        (.code ((requestNode request.domain request.left request.right).bind next)) before →
      Returned nodeLaw before.native.nodes → Returned edgeLaw before.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode request.domain request.left request.right)) before).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestNode request.domain request.left request.right)) before).state.native.edges)
    (edgeQueries : ∀ (request : EdgeRequest Symbol Guard)
      (next : EdgeValue Symbol Guard → Code Symbol Guard ParentOutput) (before : Checked width)
      (stepsBefore childFuel : Nat),
      0 < stepsBefore → stepsBefore + childFuel ≤ parentFuel → childFuel < parentFuel →
      Steps stepsBefore original initial
        (.code ((requestEdge request.domain request.left request.right).bind next)) before →
      Returned nodeLaw before.native.nodes → Returned edgeLaw before.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestEdge request.domain request.left request.right)) before).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute childFuel
        (.code (requestEdge request.domain request.left request.right)) before).state.native.edges)
    (code : Code Symbol Guard A) (body : BodyCode code) :
    ∀ (finalNext : A → Code Symbol Guard ParentOutput) (before : Checked width)
      (stepsBefore remaining : Nat),
      0 < stepsBefore → stepsBefore + remaining ≤ parentFuel →
      Steps stepsBefore original initial (.code (code.bind finalNext)) before →
      Returned nodeLaw before.native.nodes → Returned edgeLaw before.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute remaining
        (.code code) before).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute remaining
        (.code code) before).state.native.edges := by
  induction code with
  | pure value | fail failure =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      cases remaining <;> exact ⟨nodes, edges⟩
  | finishNode | finishEdge => cases body
  | work job resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      cases remaining with
      | zero => exact ⟨nodes, edges⟩
      | succ remaining =>
          let built := run job before.native.machine.heap
          let reached : Checked width :=
            ⟨advance before.native {before.native.machine with heap := built.2}, before.operations⟩
          have one : step (.code (.work job resume)) before =
              .yielded (.code (resume built.1)) reached := rfl
          have nextOrigin := prefix_yield original initial _ _ finalNext before reached stepsBefore origin one
          have later := ih built.1 (body built.1) finalNext reached (stepsBefore + 1) remaining
            (by omega) (by omega) nextOrigin nodes edges
          simpa only [SourceEqualityNativeDemand.execute, one] using later
  | enter domain left right first second resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      cases remaining with
      | zero => exact ⟨nodes, edges⟩
      | succ remaining =>
          let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains
            domain.key left right first second
          let reached : Checked width :=
            ⟨advance before.native {before.native.machine with domains := entered.2}, before.operations⟩
          have one : step (.code (.enter domain left right first second resume)) before =
              .yielded (.code (resume entered.1)) reached := rfl
          have nextOrigin := prefix_yield original initial _ _ finalNext before reached stepsBefore origin one
          have later := ih entered.1 (body entered.1) finalNext reached (stepsBefore + 1) remaining
            (by omega) (by omega) nextOrigin nodes edges
          simpa only [SourceEqualityNativeDemand.execute, one] using later
  | read name resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      cases remaining with
      | zero => exact ⟨nodes, edges⟩
      | succ remaining =>
          let found := SourcePreparedSharedRows.read before.native.machine.heap name
          have one : step (.code (.read name resume)) before = .yielded (.code (resume found)) before := rfl
          have nextOrigin := prefix_yield original initial _ _ finalNext before before stepsBefore origin one
          have later := ih found (body found) finalNext before (stepsBefore + 1) remaining
            (by omega) (by omega) nextOrigin nodes edges
          simpa only [SourceEqualityNativeDemand.execute, one] using later
  | optionalBinder key stored resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      cases remaining with
      | zero => exact ⟨nodes, edges⟩
      | succ remaining =>
          cases built : SourceRecursiveIntersectionMaybeMu.maybeMu key stored before.native.machine.heap with
          | pending pending heap =>
              simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
                SourceRecursiveIntersectionNative.step, built, SourceEqualityNativeDemand.lift,
                Outcome.state, advance] using And.intro nodes edges
          | done value heap =>
              let reached : Checked width :=
                ⟨advance before.native {before.native.machine with heap := heap}, before.operations⟩
              have one : step (.code (.optionalBinder key stored resume)) before =
                  .yielded (.code (resume value)) reached := by
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                  built, SourceEqualityNativeDemand.lift, reached]
              have nextOrigin := prefix_yield original initial _ _ finalNext before reached stepsBefore origin one
              have later := ih value (body value) finalNext reached (stepsBefore + 1) remaining
                (by omega) (by omega) nextOrigin nodes edges
              simpa only [SourceEqualityNativeDemand.execute, one] using later
  | node request resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      let lifted : Value Symbol Guard → Code Symbol Guard ParentOutput :=
        fun value => (resume value).bind finalNext
      have atQuery : Steps stepsBefore original initial
          (.code ((requestNode request.domain request.left request.right).bind lifted)) before := by
        simpa only [requestNode, Code.bind, lifted] using origin
      rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases remaining
          (.code (requestNode request.domain request.left request.right)) resume before with
        same | ⟨steps, value, middle, shorter, called, same⟩
      · simp only [Control.bind, requestNode, Code.bind] at same
        rw [same]
        exact nodeQueries request lifted before stepsBefore remaining positive bounded (by omega)
          atQuery nodes edges
      · simp only [Control.bind, requestNode, Code.bind] at same
        have completed := trace_done steps _ before middle value called
        have atMiddle := nodeQueries request lifted before stepsBefore (steps + 1)
          positive (by omega) (by omega) atQuery nodes edges
        rw [completed] at atMiddle
        have appended := called.bind _ _ _ _ _ lifted
        have tailOrigin : Steps (stepsBefore + steps) original initial
            (.code ((resume value).bind finalNext)) middle :=
          atQuery.trans _ _ _ _ _ _ _ _ appended
        have later := ih value (body value) finalNext middle (stepsBefore + steps) (remaining - steps)
          (by omega) (by omega) tailOrigin atMiddle.1 atMiddle.2
        rw [same]
        exact later
  | edge request resume ih =>
      intro finalNext before stepsBefore remaining positive bounded origin nodes edges
      let lifted : EdgeValue Symbol Guard → Code Symbol Guard ParentOutput :=
        fun value => (resume value).bind finalNext
      have atQuery : Steps stepsBefore original initial
          (.code ((requestEdge request.domain request.left request.right).bind lifted)) before := by
        simpa only [requestEdge, Code.bind, lifted] using origin
      rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases remaining
          (.code (requestEdge request.domain request.left request.right)) resume before with
        same | ⟨steps, value, middle, shorter, called, same⟩
      · simp only [Control.bind, requestEdge, Code.bind] at same
        rw [same]
        exact edgeQueries request lifted before stepsBefore remaining positive bounded (by omega)
          atQuery nodes edges
      · simp only [Control.bind, requestEdge, Code.bind] at same
        have completed := trace_done steps _ before middle value called
        have atMiddle := edgeQueries request lifted before stepsBefore (steps + 1)
          positive (by omega) (by omega) atQuery nodes edges
        rw [completed] at atMiddle
        have appended := called.bind _ _ _ _ _ lifted
        have tailOrigin : Steps (stepsBefore + steps) original initial
            (.code ((resume value).bind finalNext)) middle :=
          atQuery.trans _ _ _ _ _ _ _ _ appended
        have later := ih value (body value) finalNext middle (stepsBefore + steps) (remaining - steps)
          (by omega) (by omega) tailOrigin atMiddle.1 atMiddle.2
        rw [same]
        exact later

end MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned

#print axioms MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned.body_code_returned_of_outer_query_induction
#check MicroCFTA.SourceCurrentAllocatedNativeBodyCodeReturned.body_code_returned_of_outer_query_induction
