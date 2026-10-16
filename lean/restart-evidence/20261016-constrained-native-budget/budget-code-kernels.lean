import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode

namespace MicroCFTA.NativeBudgetCodeKernels
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedFiniteOrdinaryNativeBudgetCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq (EdgeKey Symbol Guard)]

theorem checked_children_budget (scheme : Scheme Symbol Guard)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (left right : EdgeValue Symbol Guard) (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (perChild : Nat)
    (inputs : ∀ pair ∈ left.children.zip right.children, scheme.nodeInputs ⟨domain, pair.1, pair.2⟩)
    (costs : ∀ pair ∈ left.children.zip right.children, scheme.nodeCost ⟨domain, pair.1, pair.2⟩ ≤ perChild) :
    Bound scheme (SourceEqualityNativeCheckedCode.children domain left right combined)
      (perChild * (left.children.zip right.children).length + 1) := by
  have calls : ∀ pair ∈ left.children.zip right.children,
      Bound scheme (requestNode domain pair.1 pair.2) perChild := by
    intro pair member
    have one := Bound.node (inputs pair member) (fun value => Bound.pure scheme value 0)
    exact one.weaken (by simpa only [Nat.add_zero] using costs pair member)
  have children := Bound.walk _ _ perChild calls
  have edge : ∀ values, Bound scheme
      (.work (makeEdge left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) .pure) 1 := by
    intro values
    simpa only [Nat.add_zero] using Bound.work_makeEdge left.entry.key.symbol
      (SourceEqualityConjoinAllocation.readback combined) values (fun result => Bound.pure scheme result 0)
  exact children.bind edge

theorem rejected_has_no_child_budget (left : EdgeValue Symbol Guard) :
    let scheme : Scheme Symbol Guard := ⟨fun _ => False, fun _ => False, fun _ => 999, fun _ => 999⟩
    Bound scheme (SourceEqualityNativeCheckedCode.sentinel left) 1 := by
  dsimp
  exact Bound.work_makeEdge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    (fun result => Bound.pure _ result 0)

theorem edge_then_node_budget (scheme : Scheme Symbol Guard) (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) :
    Bound scheme (.work (makeEdge symbol guard values) (fun edge =>
      .work (makeNode [edge]) .pure)) 2 := by
  exact Bound.work_makeEdge symbol guard values (fun edge => Bound.work_makeNode [edge]
    (fun value => Bound.pure scheme value 0))

theorem no_unchecked_read (scheme : Scheme Symbol Guard) (name budget : Nat) :
    ¬ Bound scheme (.read name (fun value => .pure value)) budget := fun impossible => impossible

#check @checked_children_budget
#print axioms checked_children_budget
#check @rejected_has_no_child_budget
#print axioms rejected_has_no_child_budget
#check @edge_then_node_budget
#print axioms edge_then_node_budget
#check @no_unchecked_read
#print axioms no_unchecked_read
end MicroCFTA.NativeBudgetCodeKernels
