import MicroCFTA.SourceCurrentGatePlainRegion
import MicroCFTA.SourceCurrentConstrainedCap
import MicroCFTA.InternedValueMass
import MicroCFTA.EndpointStatefulGateTrace

/-!
# Finite selected endpoint caps from the actual primary policy

The endpoint descendant test excludes a constrained Mu. Coherent cached
depth fields retain this fact at every original child. A plain Mu uses
the actual source predicate to derive hereditary annotations. The result
has a finite cap bounded by its complete payload mass. Other forest
values need no cap or closure condition.
-/
namespace MicroCFTA.SourceCurrentPrimaryEndpointCap
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceCurrentConstrainedCap (Cap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "mass" => InternedValueMass.value

private theorem node_child_clear (heap : Heap) (coherent : Coherent heap)
    (entry) (rows : List (EdgeValue Symbol Guard)) (level free)
    (available : Available heap (.node entry rows level free))
    (clear : reaches (.node entry rows level free) = false)
    (row : EdgeValue Symbol Guard) (member : row ∈ rows) (child : Value Symbol Guard)
    (inside : child ∈ row.children) : reaches child = false := by
  by_cases zero : level = 0
  · obtain ⟨actual, _stored, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
    have depth : level = maximumDepth (rows.flatMap EdgeValue.children) := fields.2.2.1
    have bounded := (maximumDepth_exact (rows.flatMap EdgeValue.children) 0).mp
      (by omega) child (List.mem_flatMap.mpr ⟨row, member, inside⟩)
    exact SourceEndpointReachability.zero_clear source child (by omega)
  · cases found : reaches child with
    | false => rfl
    | true =>
        have reached := (SourceEndpointReachability.reaches_iff source _).mpr
          (.node zero member inside ((SourceEndpointReachability.reaches_iff source child).mp found))
        rw [clear] at reached
        cases reached

private theorem union_child_clear (heap : Heap) (coherent : Coherent heap)
    (entry) (members : List (Value Symbol Guard)) (level free)
    (available : Available heap (.union entry members level free))
    (clear : reaches (.union entry members level free) = false)
    (child : Value Symbol Guard) (member : child ∈ members) : reaches child = false := by
  by_cases zero : level = 0
  · obtain ⟨actual, _stored, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
    have depth : level = maximumDepth members := fields.2.2.1
    have bounded := (maximumDepth_exact members 0).mp (by omega) child member
    exact SourceEndpointReachability.zero_clear source child (by omega)
  · cases found : reaches child with
    | false => rfl
    | true =>
        have reached := (SourceEndpointReachability.reaches_iff source _).mpr
          (.union zero member ((SourceEndpointReachability.reaches_iff source child).mp found))
        rw [clear] at reached
        cases reached

/-- Initial source reachability derives a finite cap without an input cap or closure premise. -/
theorem reaches_cap (heap : Heap) (coherent : Coherent heap) (value : Value Symbol Guard)
    (available : Available heap value) (clear : reaches value = false) : Cap Plain (mass value) value := by
  revert clear
  induction available with
  | intro value resident issued children ih =>
      intro clear
      have available : Available heap value := .intro value resident issued children
      cases value with
      | empty => exact .plain _ .empty
      | reference name => exact .plain _ (.reference name)
      | node entry rows level free =>
          change Cap Plain (1 + InternedValueMass.edges rows) (.node entry rows level free)
          rw [Nat.add_comm 1]
          apply Cap.node
          intro child member
          obtain ⟨row, selected, inside⟩ := List.mem_flatMap.mp member
          have childClear := node_child_clear heap coherent entry rows level free available clear row selected child inside
          have bounded := ih child member childClear
          apply bounded.mono
          have smaller := InternedValueMass.node_child_lt entry rows level free row selected child inside
          simp only [InternedValueMass.value] at smaller
          omega
      | union entry members level free =>
          apply Cap.union
          intro child member
          have childClear := union_child_clear heap coherent entry members level free available clear child member
          apply (ih child member childClear).mono
          exact Nat.le_of_lt (InternedValueMass.union_member_lt entry members level free child member)
      | mu entry body depth ordinary =>
          have plain : source (.mu entry body depth ordinary) = true := by
            simpa only [SourceEndpointReachability.binder, Bool.not_eq_false'] using clear
          exact .plain _ (SourceCurrentGatePlainRegion.annotations heap _ coherent available plain)

/-- The source endpoint test supplies its own finite depth witness. -/
theorem reaches_finite (heap : Heap) (coherent : Coherent heap) (value : Value Symbol Guard)
    (available : Available heap value) (clear : reaches value = false) : ∃ depth, Cap Plain depth value :=
  ⟨mass value, reaches_cap heap coherent value available clear⟩

private theorem trace_clear [DecidableEq (EdgeKey Symbol Guard)]
    {path value before answer after}
    (actual : EndpointStatefulGateTrace.NodeTrace source reaches path value before answer after) :
    path = [] → answer = false → reaches value = false := by
  cases actual with
  | empty => intro _ _; rfl
  | reference => intro _ impossible; cases impossible
  | union => intro _ impossible; cases impossible
  | finite fast =>
      intro _ _
      exact SourceEndpointReachability.zero_clear source _
        (by simpa only [Value.depth, Bool.and_eq_true, beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1)
  | endpoint slow =>
      intro _ cleared
      exact (Bool.or_eq_false_iff.mp cleared).2
  | branches => intro impossible; cases impossible
  | constrained => intro _ impossible; cases impossible
  | closed plain closed =>
      intro _ _
      simp only [SourceEndpointReachability.binder, plain, Bool.not_true]
  | unfold plain opened run next =>
      intro _ _
      simp only [SourceEndpointReachability.binder, plain, Bool.not_true]

/-- An actual false primary endpoint trace retains the exact descendant exclusion. -/
theorem endpoint_clear [DecidableEq (EdgeKey Symbol Guard)]
    {value : Value Symbol Guard} {before after : Heap}
    (actual : EndpointStatefulGateTrace.NodeTrace source reaches [] value before false after) :
    reaches value = false := trace_clear actual rfl rfl

/-- The actual false primary endpoint certifies its input at the original physical heap. -/
theorem endpoint_cap [DecidableEq (EdgeKey Symbol Guard)]
    (heap : Heap) (coherent : Coherent heap) (value : Value Symbol Guard) (available : Available heap value)
    {after : Heap} (actual : EndpointStatefulGateTrace.NodeTrace source reaches [] value heap false after) :
    Cap Plain (mass value) value := reaches_cap heap coherent value available (endpoint_clear actual)

end MicroCFTA.SourceCurrentPrimaryEndpointCap
