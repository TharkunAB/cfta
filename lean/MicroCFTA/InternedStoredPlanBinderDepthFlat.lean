import MicroCFTA.InternedFreshOrdinaryFirstOrderCompletion
import MicroCFTA.InternedStoredPlanBinderDepthNormalization
import MicroCFTA.InternedShallowValues

/-!
# Open stored-plan depth bounds for binder-free source bodies

Ordinary constructors and unions retain an upper bound on the open depth of their actual
inputs. Removing dead edges and root self references cannot increase that
bound. The proofs follow source effects and canonical payload readback.
-/
namespace MicroCFTA.InternedStoredPlanBinderDepthFlat
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts
open InternedNestedProvenance InternedProbeProvenance InternedEdgeResidency
open InternedStoredShallowCompletion InternedStoredPlanBinderDepth
open InternedBinderProtocol (Reference)

mutual
/-- Every completed binder-free body retains its input open stored-plan depth bound. -/
theorem build_bound [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (free : BinderFree expression) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (bound : Nat) (depths : ∀ value ∈ environment, valueDepth value ≤ bound)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) : valueDepth value ≤ bound := by
  cases expression with
  | empty => rw [build] at done; cases done; simp [valueDepth, Value.free]
  | var index =>
      simp only [build, Outcome.done.injEq] at done
      rw [← done.1]
      cases found : environment[index]? with
      | none => simp [valueDepth, Value.free]
      | some value => exact depths value (List.mem_of_getElem? found)
  | binder => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      have checked := buildEdges_verified edges environment state facts inputs
      rw [build] at done
      cases built : buildEdges edges environment state with
      | pending key stopped => simp only [built, Outcome.bind] at done; cases done
      | done values beforeNode =>
          have beforeFacts : Facts beforeNode := by simpa only [built, Outcome.state] using checked.facts
          have children := buildEdges_bound edges free environment state facts inputs bound depths values beforeNode built
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at done
          rw [← done.1]
          exact makeNode_le values beforeNode beforeFacts.coherent beforeFacts.linked
            (checked.result values beforeNode built) bound children
  | union members =>
      simp only [BinderFree] at free
      have checked := buildMany_verified members environment state facts inputs
      rw [build] at done
      cases built : buildMany members environment state with
      | pending key stopped => simp only [built, Outcome.bind] at done; cases done
      | done values beforeUnion =>
          have beforeFacts : Facts beforeUnion := by simpa only [built, Outcome.state] using checked.facts
          have membersDepth := buildMany_bound members free environment state facts inputs bound depths values beforeUnion built
          simp only [built, Outcome.bind, work, Outcome.done.injEq] at done
          rw [← done.1]
          exact makeUnion_le values beforeUnion beforeFacts.coherent beforeFacts.cached beforeFacts.linked
            (checked.result values beforeUnion built) bound membersDepth
termination_by sizeOf expression

/-- Ordered child evaluation retains the same bound through all previous sibling effects. -/
theorem buildMany_bound [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (free : ManyBinderFree expressions) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (bound : Nat) (depths : ∀ value ∈ environment, valueDepth value ≤ bound)
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : buildMany expressions environment state = .done values after) : ∀ value ∈ values, valueDepth value ≤ bound := by
  cases expressions with
  | nil => rw [buildMany] at done; cases done; simp
  | cons first rest =>
      simp only [ManyBinderFree] at free
      have checked := build_verified first environment state facts inputs
      rw [buildMany] at done
      cases head : build first environment state with
      | pending key stopped => simp only [head, Outcome.bind] at done; cases done
      | done value middle =>
          have middleFacts : Facts middle := by simpa only [head, Outcome.state] using checked.facts
          have laterInputs : Values middle environment := fun item member => by
            simpa only [head, Outcome.state] using checked.available item (inputs item member)
          have firstDepth := build_bound first free.1 environment state facts inputs bound depths value middle head
          simp only [head, Outcome.bind] at done
          cases tail : buildMany rest environment middle with
          | pending key stopped => simp only [tail] at done; cases done
          | done remaining final =>
              have restDepth := buildMany_bound rest free.2 environment middle middleFacts laterInputs bound depths remaining final tail
              simp only [tail, Outcome.done.injEq] at done
              rw [← done.1]
              intro item member
              rcases List.mem_cons.mp member with rfl | member
              · exact firstDepth
              · exact restDepth item member
termination_by sizeOf expressions

/-- Canonical edge payloads retain the bound of the actual ordered child values. -/
theorem buildEdges_bound [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (free : EdgesBinderFree expressions) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (bound : Nat) (depths : ∀ value ∈ environment, valueDepth value ≤ bound)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : buildEdges expressions environment state = .done edges after) :
    ∀ value ∈ edges.flatMap EdgeValue.children, valueDepth value ≤ bound := by
  cases expressions with
  | nil => rw [buildEdges] at done; cases done; simp
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          have checked := buildMany_verified children environment state facts inputs
          rw [buildEdges] at done
          cases built : buildMany children environment state with
          | pending key stopped => simp only [built, Outcome.bind] at done; cases done
          | done values middle =>
              have middleFacts : Facts middle := by simpa only [built, Outcome.state] using checked.facts
              have available := checked.result values middle built
              have childrenDepth := buildMany_bound children free.1 environment state facts inputs bound depths values middle built
              let edge := run (makeEdge symbol constraint values) middle
              have edgeChecked := edge_verified symbol constraint values middle middleFacts available
              have edgeDepth : ∀ value ∈ edge.1.children, valueDepth value ≤ bound := by
                rw [InternedShallowValues.makeEdge_children symbol constraint values middle middleFacts.coherent middleFacts.cached available]
                exact childrenDepth
              have laterInputs : Values edge.2 environment := fun item member => by
                have before : Available middle item := by
                  simpa only [built, Outcome.state] using checked.available item (inputs item member)
                exact edgeChecked.available item before
              simp only [built, Outcome.bind, work] at done
              change (buildEdges rest environment edge.2).bind _ = _ at done
              cases tail : buildEdges rest environment edge.2 with
              | pending key stopped => simp only [tail, Outcome.bind] at done; cases done
              | done remaining final =>
                  have restDepth := buildEdges_bound rest free.2 environment edge.2 edgeChecked.facts laterInputs bound depths remaining final tail
                  simp only [tail, Outcome.bind, Outcome.done.injEq] at done
                  rw [← done.1]
                  intro item member
                  have present : item ∈ edge.1.children ∨ item ∈ remaining.flatMap EdgeValue.children := by
                    simpa only [List.flatMap_cons, List.mem_append] using member
                  exact present.elim (edgeDepth item) (restDepth item)
termination_by sizeOf expressions
end

/-- The repaired normalized callback retains any input depth bound. -/
theorem callback_bound [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (free : BinderFree body) (environment : List (Value Symbol Guard)) (name : Reference)
    (state : State Symbol Guard) (facts : Facts state)
    (inputs : Values state (.reference name :: environment)) (bound : Nat)
    (depths : ∀ value ∈ environment, valueDepth value ≤ bound)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryFacts.callback body environment name state = .done value after) : valueDepth value ≤ bound := by
  have checked := build_verified body (.reference name :: environment) state facts inputs
  unfold InternedFreshOrdinaryFacts.callback at done
  rw [InternedFreshOrdinaryStoredSubstitution.build_eq body _ state free] at done
  cases built : build body (.reference name :: environment) state with
  | pending key stopped => simp only [built, Outcome.bind] at done; cases done
  | done actual middle =>
      have middleFacts : Facts middle := by simpa only [built, Outcome.state] using checked.facts
      have bodyDepth := build_bound body free (.reference name :: environment) state facts inputs bound
        (by intro item member; rcases List.mem_cons.mp member with rfl | member; simp [valueDepth, Value.free]; exact depths item member)
        actual middle built
      have filterBound := filter_le name actual middle middleFacts.coherent middleFacts.cached middleFacts.linked
        (checked.result actual middle built)
      simp only [built, Outcome.bind, work, Outcome.done.injEq] at done
      rw [← done.1]
      exact Nat.le_trans filterBound bodyDepth

end MicroCFTA.InternedStoredPlanBinderDepthFlat
