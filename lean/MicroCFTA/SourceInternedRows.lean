import MicroCFTA.SourceFromTerms

/-!
# The shared interned row adapter

An exposure snapshot gives `nodeEdges` for each stable nonempty identity.
The worklist below follows `reachable`: skip empty nodes, skip visited
identities, and prepend all children in edge order. The snapshot boundary
includes recursive node exposure and native heap identity readback. Neither
of those operations is replaced by an assumed `toRows` correctness theorem.
-/
namespace MicroCFTA.SourceInternedRows
open Language CanonicalClasses FTAValidation

/-- Empty nodes do not use the nonempty identity namespace. -/
abbrev Ref := Option Nat

/-- Source explicit state names retain a separate empty constructor. -/
inductive State where
  | empty
  | interned (identity : Nat)
  deriving DecidableEq, Ord

/-- The source `stateOf` cases. -/
def stateOf : Ref → State
  | none => .empty
  | some identity => .interned identity

/-- An exposed edge retains its annotation as data. -/
structure Row (Symbol Constraint : Type) where
  label : Symbol
  children : List Ref
  constraint : Constraint

/-- One immutable `nodeEdges` read per nonempty identity. -/
abbrev Heap (Symbol Constraint : Type) := Nat → List (Row Symbol Constraint)

/-- The exact pending child order of a freshly visited source node. -/
def children (heap : Heap Symbol Constraint) (identity : Nat) : List Ref :=
  (heap identity).flatMap Row.children

/-- The nonempty dependencies used by graph reachability. -/
def successors (heap : Heap Symbol Constraint) (identity : Nat) : List Nat :=
  (children heap identity).filterMap id

/-- Source map membership and insertion are represented by the visited key list.
The row value at a visited key is its immutable exposure snapshot. -/
def collect (heap : Heap Symbol Constraint) : Nat → List Nat → List Ref → Option (List Nat)
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, none :: pending => collect heap fuel seen pending
  | fuel + 1, seen, some identity :: pending =>
      if identity ∈ seen then collect heap fuel seen pending
      else collect heap fuel (identity :: seen) (children heap identity ++ pending)

/-- The nonempty states reached by the source graph traversal. -/
inductive Reaches (heap : Heap Symbol Constraint) (roots : List Ref) : Nat → Prop where
  | root : some identity ∈ roots → Reaches heap roots identity
  | child : Reaches heap roots parent → child ∈ successors heap parent → Reaches heap roots child

/-- An identity occurs among successors exactly when its node reference was enqueued. -/
theorem mem_successors (heap : Heap Symbol Constraint) (parent child : Nat) :
    child ∈ successors heap parent ↔ some child ∈ children heap parent := by
  simp [successors, List.mem_filterMap]

/-- A completed walk retains old keys, visits pending nodes, closes fresh rows,
and never inserts an identity twice. -/
theorem collect_properties (heap : Heap Symbol Constraint) (fuel : Nat) (seen : List Nat)
    (pending : List Ref) (result : List Nat) (unique : seen.Nodup)
    (done : collect heap fuel seen pending = some result) :
    seen ⊆ result ∧ (∀ identity, some identity ∈ pending → identity ∈ result) ∧
      (∀ identity ∈ result, identity ∉ seen → ∀ child ∈ successors heap identity, child ∈ result) ∧ result.Nodup := by
  induction fuel generalizing seen pending with
  | zero => cases done
  | succ fuel ih =>
    cases pending with
    | nil =>
      have same : seen = result := Option.some.inj done
      subst result
      exact ⟨fun _ member => member, by simp, by intro identity member absent; exact False.elim (absent member), unique⟩
    | cons node rest =>
      cases node with
      | none =>
        obtain ⟨old, restIn, closed, distinct⟩ := ih seen rest unique done
        exact ⟨old, by simpa using restIn, closed, distinct⟩
      | some identity =>
        by_cases known : identity ∈ seen
        · have next : collect heap fuel seen rest = some result := by simpa [collect, known] using done
          obtain ⟨old, restIn, closed, distinct⟩ := ih seen rest unique next
          refine ⟨old, ?_, closed, distinct⟩
          intro child member
          rcases List.mem_cons.mp member with same | later
          · exact Option.some.inj same ▸ old known
          · exact restIn child later
        · have next : collect heap fuel (identity :: seen) (children heap identity ++ rest) = some result :=
            by simpa [collect, known] using done
          obtain ⟨old, pendingIn, closed, distinct⟩ := ih (identity :: seen) _ (List.nodup_cons.mpr ⟨known, unique⟩) next
          refine ⟨fun _ member => old (by simp [member]), ?_, ?_, distinct⟩
          · intro child member
            rcases List.mem_cons.mp member with same | later
            · have present := old (List.mem_cons_self)
              exact Option.some.inj same ▸ present
            · exact pendingIn child (List.mem_append_right _ later)
          · intro node member absent child childIn
            by_cases same : node = identity
            · subst node
              exact pendingIn child (List.mem_append_left _ ((mem_successors heap identity child).mp childIn))
            · exact closed node member (by simp [same, absent]) child childIn

/-- The walk adds only keys in a property closed under actual source children. -/
theorem collect_preserves (heap : Heap Symbol Constraint) (fuel : Nat) (seen : List Nat)
    (pending : List Ref) (result : List Nat) (property : Nat → Prop)
    (old : ∀ identity ∈ seen, property identity)
    (initial : ∀ identity, some identity ∈ pending → property identity)
    (closed : ∀ identity, property identity → ∀ child ∈ successors heap identity, property child)
    (done : collect heap fuel seen pending = some result) : ∀ identity ∈ result, property identity := by
  induction fuel generalizing seen pending with
  | zero => cases done
  | succ fuel ih =>
    cases pending with
    | nil => cases Option.some.inj done; exact old
    | cons node rest =>
      cases node with
      | none => exact ih seen rest old (fun identity member => initial identity (by simp [member])) done
      | some identity =>
        by_cases known : identity ∈ seen
        · exact ih seen rest old (fun next member => initial next (by simp [member])) (by simpa [collect, known] using done)
        · apply ih (identity :: seen) (children heap identity ++ rest)
          · intro next member
            rcases List.mem_cons.mp member with rfl | member
            · exact initial _ (by simp)
            · exact old next member
          · intro next member
            rcases List.mem_append.mp member with child | later
            · exact closed identity (initial identity (by simp)) next ((mem_successors heap identity next).mpr child)
            · exact initial next (by simp [later])
          · simpa [collect, known] using done

/-- Successful traversal computes the exact reached identity set. -/
theorem collect_exact (heap : Heap Symbol Constraint) (fuel : Nat) (roots : List Ref) (result : List Nat)
    (done : collect heap fuel [] roots = some result) (identity : Nat) :
    identity ∈ result ↔ Reaches heap roots identity := by
  constructor
  · exact collect_preserves heap fuel [] roots result (Reaches heap roots) (by simp)
      (fun _ member => .root member) (fun _ reached _ member => .child reached member) done identity
  · intro reached
    obtain ⟨_, initial, closed, _⟩ := collect_properties heap fuel [] roots result (by simp) done
    induction reached with
    | root member => exact initial _ member
    | child reached member ih => exact closed _ ih (by simp) _ member

/-- Raw transitions preserve the exact symbol, child order, and constraint value. -/
structure Transition (Symbol Constraint : Type) where
  label : Symbol
  children : List State
  constraint : Constraint

def transition (row : Row Symbol Constraint) : Transition Symbol Constraint :=
  ⟨row.label, row.children.map stateOf, row.constraint⟩

/-- `Map.fromDistinctAscList` reads the collected keys in ascending identity order. -/
def table (heap : Heap Symbol Constraint) (visited : List Nat) :
    List (State × List (Transition Symbol Constraint)) :=
  (sortedSet visited).map fun identity => (.interned identity, (heap identity).map transition)

/-- Empty roots have one explicit empty row; other roots use the shared walk. -/
def toRows (heap : Heap Symbol Constraint) (fuel : Nat) : Ref →
    Option (List (State × List (Transition Symbol Constraint)))
  | none => some [(.empty, [])]
  | some identity => (collect heap fuel [] [some identity]).map (table heap)

/-- Functional lookup reads a raw explicit table without changing annotations. -/
def lookup (table : List (State × List (Transition Symbol Constraint))) (state : State) : List (Transition Symbol Constraint) :=
  table.flatMap fun (key, outgoing) => if key = state then outgoing else []

/-- The exact output row at each nonempty identity. -/
theorem table_lookup (heap : Heap Symbol Constraint) (visited : List Nat) (identity : Nat) :
    lookup (table heap visited) (.interned identity) = if identity ∈ visited then (heap identity).map transition else [] := by
  simp only [lookup, table, List.flatMap_map, State.interned.injEq]
  rw [SourceFromTerms.select_unique (sortedSet visited) (sortedSet_nodup _) _ identity]
  simp only [mem_sortedSet]

/-- Nonempty traversal never aliases an identity with the empty state. -/
theorem table_empty (heap : Heap Symbol Constraint) (visited : List Nat) :
    lookup (table heap visited) .empty = [] := by simp [lookup, table, List.flatMap_map]

/-- The root row uses all source alternatives in their original order. -/
theorem toRows_root (heap : Heap Symbol Constraint) (fuel identity : Nat)
    (result : List (State × List (Transition Symbol Constraint)))
    (done : toRows heap fuel (some identity) = some result) :
    lookup result (.interned identity) = (heap identity).map transition := by
  obtain ⟨visited, walked, same⟩ := Option.map_eq_some_iff.mp done
  subst result
  have present := (collect_exact heap fuel [some identity] visited walked identity).mpr (.root (by simp))
  simp [table_lookup, present]

end MicroCFTA.SourceInternedRows
