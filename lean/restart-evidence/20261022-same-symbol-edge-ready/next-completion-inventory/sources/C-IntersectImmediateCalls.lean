import MicroCFTA.IntersectRequiredFuel
import MicroCFTA.SourceRecursiveIntersectionStep

/-!
# Immediate requests of the actual semantic branch

The request list retains source order, canonical swaps, original Mu bodies,
union members, matched rows, and paired children. Successful parent
execution supplies successful child execution at the preceding bound.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage SourceRecursiveIntersectionControl SourceRecursiveIntersectionSchedule

/-- Read the exact recursive requests of one selected source node branch. -/
def branchCalls [DecidableEq Symbol] (view : View Symbol) (domain : Domain) (left right : Input) : Branch → List (Call Symbol)
  | .reset => [.node {} left right]
  | .swap => [.node domain right left]
  | .bothMu => match left, right with
    | .mu first, .mu second => [.node (extend domain [(first, left), (second, right)] (pair left right)) (view.body first) (view.body second)]
    | _, _ => []
  | .leftMu => match left with
    | .mu first => [.node (extend domain [(first, left)] (pair left right)) (view.body first) right]
    | _ => []
  | .rightMu => match right with
    | .mu second => [.node (extend domain [(second, right)] (pair left right)) left (view.body second)]
    | _ => []
  | .leftUnion => match left with
    | .union first => (view.members first).map (fun member => .node domain member right)
    | _ => []
  | .rightUnion => match right with
    | .union second => (view.members second).map (fun member => .node domain left member)
    | _ => []
  | .leftReference => match left with
    | .ref name => (lookup domain name).toList.map (fun binder => .node domain binder right)
    | _ => []
  | .rightReference => match right with
    | .ref name => (lookup domain name).toList.map (fun binder => .node domain left binder)
    | _ => []
  | .ordinary => match left, right with
    | .node first, .node second => (joined (view.rows first) (view.rows second)).map (fun rows => .edge domain rows.1 rows.2)
    | _, _ => []
  | .empty | .self | .repeated _ | .unsupported => []

/-- An immediate source request follows the actual selected node branch or ordered edge child list. -/
inductive Immediate [DecidableEq Symbol] (view : View Symbol) : Call Symbol → Call Symbol → Prop where
  | node (domain : Domain) (left right : Input) (child : Call Symbol) (member : child ∈ branchCalls view domain left right
      (inputDecision domain (closed view left) (closed view right) left right)) : Immediate view (.node domain left right) child
  | edge (domain : Domain) (left right : Row Symbol) (children : Input × Input)
      (sameArity : left.children.length = right.children.length) (member : children ∈ left.children.zip right.children) :
      Immediate view (.edge domain left right) (.node domain children.1 children.2)

/-- Every request of a successful selected branch succeeds at the branch's supplied bound. -/
theorem branch_child_success [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (domain : Domain)
    (left right : Input) (branch : Branch) (result : Shape (Payload Symbol))
    (done : SourceRecursiveIntersectionStep.action view fuel domain left right branch = some (.ok result))
    (child : Call Symbol) (member : child ∈ branchCalls view domain left right branch) :
    ∃ output, execute view fuel child = .ok output := by
  cases branch with
  | empty | self | repeated key | unsupported => simp [branchCalls] at member
  | reset | swap =>
      simp only [branchCalls, List.mem_singleton] at member
      subst child
      exact ⟨result, Option.some.inj done⟩
  | bothMu =>
      cases left <;> cases right <;> simp only [branchCalls, List.mem_nil_iff, List.mem_singleton] at member <;> try contradiction
      subst child
      obtain ⟨output, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact ⟨output, done⟩
  | leftMu =>
      cases left <;> simp only [branchCalls, List.mem_nil_iff, List.mem_singleton] at member <;> try contradiction
      subst child
      obtain ⟨output, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact ⟨output, done⟩
  | rightMu =>
      cases right <;> simp only [branchCalls, List.mem_nil_iff, List.mem_singleton] at member <;> try contradiction
      subst child
      obtain ⟨output, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact ⟨output, done⟩
  | leftUnion =>
      cases left <;> simp only [branchCalls, List.mem_nil_iff] at member <;> try contradiction
      obtain ⟨input, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨outputs, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact walk_member_success _ _ outputs done input inside
  | rightUnion =>
      cases right <;> simp only [branchCalls, List.mem_nil_iff] at member <;> try contradiction
      obtain ⟨input, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨outputs, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact walk_member_success _ _ outputs done input inside
  | leftReference =>
      cases left <;> simp only [branchCalls, List.mem_nil_iff] at member <;> try contradiction
      rename_i name
      cases found : lookup domain name with
      | none => simp [found] at member
      | some binder =>
          simp only [found, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at member
          subst child
          exact ⟨result, by simpa only [SourceRecursiveIntersectionStep.action, found, execute] using Option.some.inj done⟩
  | rightReference =>
      cases right <;> simp only [branchCalls, List.mem_nil_iff] at member <;> try contradiction
      rename_i name
      cases found : lookup domain name with
      | none => simp [found] at member
      | some binder =>
          simp only [found, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at member
          subst child
          exact ⟨result, by simpa only [SourceRecursiveIntersectionStep.action, found, execute] using Option.some.inj done⟩
  | ordinary =>
      cases left <;> cases right <;> simp only [branchCalls, List.mem_nil_iff] at member <;> try contradiction
      obtain ⟨rows, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨outputs, done, _⟩ := map_success _ _ result (Option.some.inj done)
      exact walk_member_success _ _ outputs done rows inside

/-- Every immediate child of a successful parent succeeds at the preceding semantic bound. -/
theorem immediate_success [DecidableEq Symbol] (view : View Symbol) (fuel : Nat) (parent child : Call Symbol)
    (result : Shape (Payload Symbol)) (done : execute view (fuel + 1) parent = .ok result)
    (immediate : Immediate view parent child) : ∃ output, execute view fuel child = .ok output := by
  cases immediate with
  | @node domain left right child member =>
      apply branch_child_success view fuel domain left right _ result ?_ child member
      rw [SourceRecursiveIntersectionStep.run_selected]
      exact congrArg some done
  | @edge domain left right children sameArity member =>
      change edge view (fuel + 1) domain left right = .ok result at done
      rw [edge.eq_2] at done
      simp only [sameArity, ne_eq, not_true_eq_false, ite_false] at done
      obtain ⟨outputs, done, _⟩ := map_success _ _ result done
      exact walk_member_success _ _ outputs done children member

/-- Every actual immediate child has a strictly smaller least successful request bound. -/
theorem immediate_requiredFuel [DecidableEq Symbol] (view : View Symbol) (parent child : Call Symbol)
    (complete : Completes view parent) (immediate : Immediate view parent child) :
    ∃ childComplete : Completes view child,
      requiredFuel view child childComplete < requiredFuel view parent complete := by
  obtain ⟨result, done⟩ := requiredFuel_success view parent complete
  have positive := requiredFuel_positive view parent complete
  have predecessor : requiredFuel view parent complete - 1 + 1 = requiredFuel view parent complete := by omega
  rw [← predecessor] at done
  obtain ⟨output, childDone⟩ := immediate_success view _ parent child result done immediate
  exact requiredFuel_child view parent child complete output childDone

end MicroCFTA.IntersectSchedule
