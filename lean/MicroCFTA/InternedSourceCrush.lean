import MicroCFTA.InternedNodeIdentityFootprint

/-!
# The source visited-node Boolean crush

The source skips empty records and bare references. It marks each ordinary,
union, or Mu identity before visiting its children. Mu traversal visits only
the stored body. Neither probe participates. The traversal has no constructor
cache effect and does not unfold a recursive record.
-/
namespace MicroCFTA.InternedSourceCrush
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance

mutual
/-- Execute the source Boolean fold with its actual visited-identity set. -/
def visit (plain : Guard → Bool) (value : Value Symbol Guard) (seen : List Nat) : Bool × List Nat :=
  match value with
  | .empty | .reference _ => (true, seen)
  | .node entry edges _ _ =>
      if entry.identity ∈ seen then (true, seen) else
      let children := visitEdges plain edges (entry.identity :: seen)
      ((edges.all fun edge => plain edge.entry.key.constraint) && children.1, children.2)
  | .union entry values _ _ =>
      if entry.identity ∈ seen then (true, seen) else visitMany plain values (entry.identity :: seen)
  | .mu entry body _ _ =>
      if entry.identity ∈ seen then (true, seen) else visit plain body (entry.identity :: seen)
termination_by sizeOf value

/-- Traverse all source children in their original order and share the visited set. -/
def visitMany (plain : Guard → Bool) (values : List (Value Symbol Guard)) (seen : List Nat) : Bool × List Nat :=
  match values with
  | [] => (true, seen)
  | first :: rest =>
      let head := visit plain first seen
      let tail := visitMany plain rest head.2
      (head.1 && tail.1, tail.2)
termination_by sizeOf values

/-- Flatten original edge children in source order without visiting edge records as nodes. -/
def visitEdges (plain : Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (seen : List Nat) : Bool × List Nat :=
  match edges with
  | [] => (true, seen)
  | .mk _ children :: rest =>
      let head := visitMany plain children seen
      let tail := visitEdges plain rest head.2
      (head.1 && tail.1, tail.2)
termination_by sizeOf edges
end

/-- The source Boolean read starts with the empty visited set. -/
def unconstrained (plain : Guard → Bool) (value : Value Symbol Guard) : Bool := (visit plain value []).1

/-- A previously visited canonical node returns the monoid identity without visiting its children. -/
theorem visit_seen (plain : Guard → Bool) (value : Value Symbol Guard) (seen : List Nat)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (record : entryOf value = some entry)
    (visited : entry.identity ∈ seen) : visit plain value seen = (true, seen) := by
  cases value with
  | empty | reference => simp [entryOf] at record
  | node | union | mu => cases record; simp [visit, visited]

mutual
/-- Every source visit retains every earlier visited identity. -/
theorem visit_grows (plain : Guard → Bool) (value : Value Symbol Guard) (seen : List Nat) :
    seen ⊆ (visit plain value seen).2 := by
  cases value with
  | empty | reference => simp [visit]
  | node entry edges depth free =>
      rw [visit]
      split
      · exact List.Subset.refl _
      · exact fun identity member => visitEdges_grows plain edges _ (List.mem_cons_of_mem _ member)
  | union entry values depth free =>
      rw [visit]
      split
      · exact List.Subset.refl _
      · exact fun identity member => visitMany_grows plain values _ (List.mem_cons_of_mem _ member)
  | mu entry body depth ordinary =>
      rw [visit]
      split
      · exact List.Subset.refl _
      · exact fun identity member => visit_grows plain body _ (List.mem_cons_of_mem _ member)
termination_by sizeOf value

/-- Each ordered child passes the complete visited set to its successor. -/
theorem visitMany_grows (plain : Guard → Bool) (values : List (Value Symbol Guard)) (seen : List Nat) :
    seen ⊆ (visitMany plain values seen).2 := by
  cases values with
  | nil => simp [visitMany]
  | cons first rest =>
      rw [visitMany]
      exact List.Subset.trans (visit_grows plain first seen) (visitMany_grows plain rest _)
termination_by sizeOf values

/-- Edge flattening preserves the shared visited set through every child. -/
theorem visitEdges_grows (plain : Guard → Bool) (edges : List (EdgeValue Symbol Guard)) (seen : List Nat) :
    seen ⊆ (visitEdges plain edges seen).2 := by
  cases edges with
  | nil => simp [visitEdges]
  | cons first rest =>
      cases first with
      | mk entry children =>
          rw [visitEdges]
          exact List.Subset.trans (visitMany_grows plain children seen) (visitEdges_grows plain rest _)
termination_by sizeOf edges
end

end MicroCFTA.InternedSourceCrush
