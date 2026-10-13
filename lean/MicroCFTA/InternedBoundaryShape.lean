import MicroCFTA.InternedBoundaryProvenance

/-!
# Canonical records from shapes with ordinary identities removed

The shape retains symbols, guards, child order, union member order, literal
references, and Mu identities. It removes ordinary node and edge identities.
Equal shapes in one coherent source cache identify the same complete record.
-/
namespace MicroCFTA.InternedBoundaryShape
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedEdgeResidency
open InternedBinderProtocol (Reference NodeRef NodeKey)

mutual
/-- The structural shape stops at Mu identities and retains every ordinary constructor field. -/
inductive Shape (Symbol Guard : Type) where
  | empty
  | reference (name : Reference)
  | node (edges : List (EdgeShape Symbol Guard))
  | union (members : List (Shape Symbol Guard))
  | mu (identity : Nat)

/-- An edge shape retains its symbol, guard, and exact ordered child shapes. -/
inductive EdgeShape (Symbol Guard : Type) where
  | mk (symbol : Symbol) (constraint : Guard) (children : List (Shape Symbol Guard))
end

mutual
/-- Remove ordinary identities from a complete source value. -/
def shape : Value Symbol Guard → Shape Symbol Guard
  | .empty => .empty
  | .reference name => .reference name
  | .node _ edges _ _ => .node (edgeShapes edges)
  | .union _ members _ _ => .union (manyShapes members)
  | .mu entry _ _ _ => .mu entry.identity
termination_by value => sizeOf value

/-- Retain the exact source order of child or member shapes. -/
def manyShapes : List (Value Symbol Guard) → List (Shape Symbol Guard)
  | [] => []
  | first :: rest => shape first :: manyShapes rest
termination_by values => sizeOf values

/-- Retain every field of each source edge except its interned identity. -/
def edgeShapes : List (EdgeValue Symbol Guard) → List (EdgeShape Symbol Guard)
  | [] => []
  | .mk entry children :: rest => .mk entry.key.symbol entry.key.constraint (manyShapes children) :: edgeShapes rest
termination_by edges => sizeOf edges
end

/-- An ordinary source payload stores the key formed from its actual ordered edges. -/
theorem node_key (entry : Interned NodeKey) (edges : List (EdgeValue Symbol Guard)) (depth : Nat) (free : List Reference)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state (.node entry edges depth free)) :
    entry.key = .node (edges.map (fun edge => edge.entry.identity)) := by
  obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
  exact fields.2.1

/-- A union source payload stores the key formed from its actual ordered members. -/
theorem union_key (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (depth : Nat) (free : List Reference)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state (.union entry members depth free)) :
    entry.key = .union (members.map Value.referenceOf) := by
  obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key _ (available.resident entry rfl)
  exact fields.2.1

mutual
/-- Shape equality determines exact complete source records in a common coherent cache. -/
theorem shape_injective (first second : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (left : Available state first) (right : Available state second)
    (same : shape first = shape second) : first = second := by
  cases first <;> cases second <;> simp only [shape, Shape.node.injEq, Shape.union.injEq, Shape.mu.injEq, Shape.reference.injEq, reduceCtorEq] at same
  case empty.empty => rfl
  case reference.reference first second => cases same; rfl
  case mu.mu entry body depth ordinary other otherBody otherDepth otherOrdinary =>
    exact resident_reference_injective state coherent _ _ left.resident right.resident (by simpa [Value.referenceOf] using same)
  case node.node entry edges depth free other otherEdges otherDepth otherFree =>
    have edgesSame := edgeShapes_injective edges otherEdges state coherent linked
      (resident_edges state linked _ left.resident) (resident_edges state linked _ right.resident)
      (fun child member => left.children child member) (fun child member => right.children child member) same
    have keys := (node_key entry edges depth free state coherent left).trans
      ((congrArg (fun values => NodeKey.node (values.map (fun edge => edge.entry.identity))) edgesSame).trans
        (node_key other otherEdges otherDepth otherFree state coherent right).symm)
    have stored := right.resident other rfl
    rw [← keys] at stored
    exact Option.some.inj ((left.resident entry rfl).symm.trans stored)
  case union.union entry members depth free other otherMembers otherDepth otherFree =>
    have membersSame := manyShapes_injective members otherMembers state coherent linked
      (fun child member => left.children child member) (fun child member => right.children child member) same
    have keys := (union_key entry members depth free state coherent left).trans
      ((congrArg (fun values => NodeKey.union (values.map Value.referenceOf)) membersSame).trans
        (union_key other otherMembers otherDepth otherFree state coherent right).symm)
    have stored := right.resident other rfl
    rw [← keys] at stored
    exact Option.some.inj ((left.resident entry rfl).symm.trans stored)
termination_by sizeOf first

/-- Ordered shape equality determines the exact available child list. -/
theorem manyShapes_injective (first second : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (left : ∀ value ∈ first, Available state value) (right : ∀ value ∈ second, Available state value)
    (same : manyShapes first = manyShapes second) : first = second := by
  cases first with
  | nil => cases second <;> simp_all [manyShapes]
  | cons head tail =>
      cases second with
      | nil => simp [manyShapes] at same
      | cons other rest =>
          simp only [manyShapes, List.cons.injEq] at same
          have heads := shape_injective head other state coherent linked
            (left head (by simp)) (right other (by simp)) same.1
          have tails := manyShapes_injective tail rest state coherent linked
            (fun value member => left value (by simp [member])) (fun value member => right value (by simp [member])) same.2
          simp [heads, tails]
termination_by sizeOf first

/-- Exact edge fields and child shapes recover canonical edge records and their identities. -/
theorem edgeShapes_injective (first second : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state)
    (left : ∀ edge ∈ first, EdgeResident state edge) (right : ∀ edge ∈ second, EdgeResident state edge)
    (leftChildren : ∀ value ∈ first.flatMap EdgeValue.children, Available state value)
    (rightChildren : ∀ value ∈ second.flatMap EdgeValue.children, Available state value)
    (same : edgeShapes first = edgeShapes second) : first = second := by
  cases first with
  | nil =>
      cases second with
      | nil => rfl
      | cons head tail => cases head; simp [edgeShapes] at same
  | cons head tail =>
      cases head with
      | mk entry children =>
          cases second with
          | nil => simp [edgeShapes] at same
          | cons other rest =>
              cases other with
              | mk otherEntry otherChildren =>
                  simp only [edgeShapes, List.cons.injEq, EdgeShape.mk.injEq] at same
                  have childrenSame := manyShapes_injective children otherChildren state coherent linked
                    (fun value member => leftChildren value (by simp [EdgeValue.children, member]))
                    (fun value member => rightChildren value (by simp [EdgeValue.children, member])) same.1.2.2
                  have leftStored := left (.mk entry children) (by simp)
                  have rightStored := right (.mk otherEntry otherChildren) (by simp)
                  have leftFields := (coherent.edges _ _ leftStored).2.2
                  have rightFields := (coherent.edges _ _ rightStored).2.2
                  have keys : entry.key = otherEntry.key := by
                    have refs : entry.key.children = otherEntry.key.children :=
                      leftFields.symm.trans ((congrArg (List.map Value.referenceOf) childrenSame).trans rightFields)
                    cases leftKey : entry.key
                    cases rightKey : otherEntry.key
                    simp_all
                  change state.edgeRecords entry.key = some (.mk entry children) at leftStored
                  change state.edgeRecords otherEntry.key = some (.mk otherEntry otherChildren) at rightStored
                  rw [← keys] at rightStored
                  have heads := Option.some.inj (leftStored.symm.trans rightStored)
                  have tails := edgeShapes_injective tail rest state coherent linked
                    (fun edge member => left edge (by simp [member])) (fun edge member => right edge (by simp [member]))
                    (fun value member => leftChildren value (by simp [EdgeValue.children, member]))
                    (fun value member => rightChildren value (by simp [EdgeValue.children, member])) same.2
                  simp [heads, tails]
termination_by sizeOf first
end

end MicroCFTA.InternedBoundaryShape
