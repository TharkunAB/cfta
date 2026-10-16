import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryNativeProfile
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrences
import MicroCFTA.MergedOrdinaryHeight

/-!
# Original occurrence bounds from uniform profiles and height

The bounds include repeated source positions. They count literal ordinary
nodes and rows. They do not count unique identities or assume execution.
Forests multiply the per-node bound by their original list length.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds
open InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
variable {Symbol Guard : Type} {rowLimit arityLimit : Nat}

/-- Bound all ordinary node occurrences below one profiled node. -/
def nodeCount (rows arity : Nat) : Nat → Nat
  | 0 => 0
  | bound + 1 => 1 + rows * arity * nodeCount rows arity bound

/-- Bound all literal row occurrences below one profiled node. -/
def edgeCount (rows arity : Nat) : Nat → Nat
  | 0 => 0
  | bound + 1 => rows * (1 + arity * edgeCount rows arity bound)

/-- One more ordinary layer cannot reduce the node occurrence bound. -/
theorem nodeCount_succ (rows arity bound : Nat) :
    nodeCount rows arity bound ≤ nodeCount rows arity (bound + 1) := by
  induction bound with
  | zero => exact Nat.zero_le _
  | succ bound ih =>
      simp only [nodeCount]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) 1

/-- One more ordinary layer cannot reduce the row occurrence bound. -/
theorem edgeCount_succ (rows arity bound : Nat) :
    edgeCount rows arity bound ≤ edgeCount rows arity (bound + 1) := by
  induction bound with
  | zero => exact Nat.zero_le _
  | succ bound ih =>
      simp only [edgeCount]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) 1)

/-- A larger height permits every earlier node occurrence bound. -/
theorem nodeCount_mono (rows arity : Nat) {first last : Nat} (bounded : first ≤ last) :
    nodeCount rows arity first ≤ nodeCount rows arity last := by
  induction bounded with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (nodeCount_succ rows arity last)

/-- A larger height permits every earlier row occurrence bound. -/
theorem edgeCount_mono (rows arity : Nat) {first last : Nat} (bounded : first ≤ last) :
    edgeCount rows arity first ≤ edgeCount rows arity last := by
  induction bounded with
  | refl => exact Nat.le_refl _
  | @step last _ ih => exact Nat.le_trans ih (edgeCount_succ rows arity last)

mutual
/-- An original uniform node profile and height bound all literal occurrences. -/
theorem node (value : Value Symbol Guard) (profile : NodeShape rowLimit arityLimit value)
    (bound : Nat) (heightBound : height value ≤ bound) :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.node value).1 ≤ nodeCount rowLimit arityLimit bound ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.node value).2 ≤ edgeCount rowLimit arityLimit bound := by
  cases value with
  | empty => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | reference | mu | union => cases profile
  | node entry edges depth free =>
      cases bound with
      | zero => simp only [height] at heightBound; omega
      | succ bound =>
          have rowHeight : edgesHeight edges ≤ bound := by simp only [height] at heightBound; omega
          have current := rows edges profile.2 bound rowHeight
          constructor
          · have budget := Nat.le_trans current.1 (Nat.mul_le_mul_right _ profile.1)
            simpa only [SourceCurrentAllocatedFiniteOrdinaryOccurrences.node, nodeCount, Nat.mul_assoc] using
              Nat.add_le_add_left budget 1
          · exact Nat.le_trans current.2 (Nat.mul_le_mul_right _ profile.1)
termination_by sizeOf value

/-- A row list counts each original edge and its complete child forest. -/
theorem rows (edges : List (EdgeValue Symbol Guard)) (profile : RowsShape rowLimit arityLimit edges)
    (bound : Nat) (heightBound : edgesHeight edges ≤ bound) :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows edges).1 ≤ edges.length * (arityLimit * nodeCount rowLimit arityLimit bound) ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows edges).2 ≤ edges.length * (1 + arityLimit * edgeCount rowLimit arityLimit bound) := by
  cases edges with
  | nil => simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows]
  | cons first rest =>
      have firstHeight := Nat.le_trans (Nat.le_max_left _ _) heightBound
      have restHeight := Nat.le_trans (Nat.le_max_right _ _) heightBound
      have firstCounts := edge first profile.1 bound firstHeight
      have restCounts := rows rest profile.2 bound restHeight
      simp only [SourceCurrentAllocatedFiniteOrdinaryOccurrences.rows, List.length_cons, Nat.succ_mul]
      constructor <;> omega
termination_by sizeOf edges

/-- A profiled edge adds its own row occurrence after its original children. -/
theorem edge (value : EdgeValue Symbol Guard) (profile : EdgeShape rowLimit arityLimit value)
    (bound : Nat) (heightBound : edgeHeight value ≤ bound) :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge value).1 ≤ arityLimit * nodeCount rowLimit arityLimit bound ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.edge value).2 ≤ 1 + arityLimit * edgeCount rowLimit arityLimit bound := by
  cases value with
  | mk entry values =>
      have current := children values profile.2 bound heightBound
      exact ⟨Nat.le_trans current.1 (Nat.mul_le_mul_right _ profile.1),
        Nat.add_le_add_left (Nat.le_trans current.2 (Nat.mul_le_mul_right _ profile.1)) 1⟩
termination_by sizeOf value

/-- A profiled forest multiplies its per-node bound by its exact original length. -/
theorem children (values : List (Value Symbol Guard)) (profile : ChildrenShape rowLimit arityLimit values)
    (bound : Nat) (heightBound : childrenHeight values ≤ bound) :
    (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children values).1 ≤ values.length * nodeCount rowLimit arityLimit bound ∧
      (SourceCurrentAllocatedFiniteOrdinaryOccurrences.children values).2 ≤ values.length * edgeCount rowLimit arityLimit bound := by
  cases values with
  | nil => simp [SourceCurrentAllocatedFiniteOrdinaryOccurrences.children]
  | cons first rest =>
      have firstHeight := Nat.le_trans (Nat.le_max_left _ _) heightBound
      have restHeight := Nat.le_trans (Nat.le_max_right _ _) heightBound
      have firstCounts := node first profile.1 bound firstHeight
      have restCounts := children rest profile.2 bound restHeight
      simp only [SourceCurrentAllocatedFiniteOrdinaryOccurrences.children, List.length_cons, Nat.succ_mul]
      constructor <;> omega
termination_by sizeOf values
end

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOccurrenceBounds
