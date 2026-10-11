import MicroCFTA.PruneMemo

/-!
# Specialization memo reuse as the binder registry grows

A cached specialization depends only on rows actually read through its finite
plan. Existing resolved references retain their rows when the binder registry
grows without changing any existing identity. Unresolved reads are an explicit
remaining caller obligation, not an assumed consequence of caching.
-/
namespace MicroCFTA.PruneDependencies
open Language Observation ObservationGraph PruneMemo
variable {Node : Type}

/-- The graph states whose rows the uncached finite-plan specialization reads. -/
def reads (automaton : Automaton State (Label Symbol Refinement)) : Nat → Plan → State → List State
  | 0, _, _ => []
  | fuel + 1, .node _ planned, state =>
      state :: (automaton state).flatMap (fun edge => edge.children.zipIdx.flatMap (fun child =>
        match childAt child.2 planned with
        | none => []
        | some plan => reads automaton fuel plan child.1))

/-- Equal rows at every actual read preserve the exact specialized graph. -/
theorem specialize_rows_congr [DecidableEq Symbol] [DecidableEq Refinement]
    (before after : Automaton State (Label Symbol Refinement)) (fuel : Nat) (plan : Plan) (state : State)
    (agree : ∀ key ∈ reads before fuel plan state, before key = after key) :
    specialize before fuel plan state = specialize after fuel plan state := by
  induction fuel generalizing plan state with
  | zero => rfl
  | succ fuel ih =>
      cases plan with
      | node observation planned =>
          have root := agree state (by simp [reads])
          simp only [specialize]
          rw [← root]
          congr 1
          apply congrArg List.flatten
          apply List.map_congr_left
          intro edge member
          simp only [edgeCandidates]
          congr 1
          apply products_congr
          intro child present
          cases found : childAt child.2 planned with
          | none => simp [childChoices, found]
          | some childPlan =>
              simp only [childChoices, found]
              apply ih childPlan child.1
              intro key visited
              apply agree key
              apply List.mem_cons_of_mem
              apply List.mem_flatMap.mpr
              refine ⟨edge, member, List.mem_flatMap.mpr ⟨child, present, ?_⟩⟩
              simpa [found] using visited

/-- A valid memo remains valid after exactly its previously read graph rows remain equal. -/
theorem memo_rows_congr [DecidableEq Symbol] [DecidableEq Refinement]
    (before after : Automaton State (Label Symbol Refinement)) (memo : Memo State Symbol Refinement)
    (valid : ValidMemo before memo)
    (agree : ∀ key variants, memo key = some variants →
      ∀ state ∈ reads before (sizeOf key.2) key.2 key.1, before state = after state) :
    ValidMemo after memo := by
  intro key variants stored
  exact (valid key variants stored).trans
    (specialize_rows_congr before after (sizeOf key.2) key.2 key.1 (agree key variants stored))

/-- The binder registry contains immutable nodes under their recursive identity. -/
abbrev Registry (Node : Type) := Nat → Option Node

/-- A registry entry uses the stored node's own identity. -/
def WellKeyed (identity : Node → Nat) (registry : Registry Node) : Prop :=
  ∀ key node, registry key = some node → identity node = key

/-- Register the binder before pruning its open body, as in `pruneMu`. -/
def register (identity : Node → Nat) (registry : Registry Node) (node : Node) : Registry Node :=
  fun key => if key = identity node then some node else registry key

/-- Registering a binder preserves the identity relation. -/
theorem register_wellKeyed (identity : Node → Nat) (registry : Registry Node)
    (valid : WellKeyed identity registry) (node : Node) : WellKeyed identity (register identity registry node) := by
  intro key value found
  by_cases same : key = identity node
  · have equal : node = value := by simpa [register, same] using found
    simpa [equal] using same.symm
  · exact valid key value (by simpa [register, same] using found)

/-- Interning makes equal node identities refer to the same immutable node. -/
def IdentityUnique (identity : Node → Nat) : Prop := ∀ left right, identity left = identity right → left = right

/-- A growing registry preserves each existing resolved binder when identities are unique. -/
theorem register_retains (identity : Node → Nat) (unique : IdentityUnique identity) (registry : Registry Node)
    (valid : WellKeyed identity registry) (node : Node) (key : Nat) (previous : Node)
    (found : registry key = some previous) : register identity registry node key = some previous := by
  by_cases same : key = identity node
  · have equal : previous = node := unique previous node ((valid key previous found).trans same)
    simp [register, same, equal]
  · simp [register, same, found]

/-- Node rows either come directly from an immutable node or from one resolved recursive reference. -/
inductive Source (Node : Type) where
  | direct (node : Node)
  | reference (name : Nat)
  deriving DecidableEq

/-- The source `alternatives` operation returns no rows for an unresolved reference. -/
def graph (rows : Node → List (Edge (Source Node) Symbol)) (registry : Registry Node) : Automaton (Source Node) Symbol
  | .direct node => rows node
  | .reference name => match registry name with | none => [] | some node => rows node

/-- Every recursive reference used in this finite query was already registered. -/
def ResolvedReads (rows : Node → List (Edge (Source Node) (Label Symbol Refinement))) (registry : Registry Node)
    (fuel : Nat) (plan : Plan) (root : Source Node) : Prop :=
  ∀ name, .reference name ∈ reads (graph rows registry) fuel plan root → ∃ node, registry name = some node

/-- Registering another binder preserves every row read by an already resolved query. -/
theorem register_rows (rows : Node → List (Edge (Source Node) (Label Symbol Refinement)))
    (identity : Node → Nat) (unique : IdentityUnique identity) (registry : Registry Node)
    (valid : WellKeyed identity registry) (node : Node) (fuel : Nat) (plan : Plan) (root : Source Node)
    (resolved : ResolvedReads rows registry fuel plan root) (state : Source Node)
    (visited : state ∈ reads (graph rows registry) fuel plan root) :
    graph rows registry state = graph rows (register identity registry node) state := by
  cases state with
  | direct value => rfl
  | reference name =>
      obtain ⟨binder, found⟩ := resolved name visited
      have retained := register_retains identity unique registry valid node name binder found
      simp [graph, found, retained]

/-- The complete split memo survives source binder registration when all earlier queried references were resolved. -/
theorem memo_register [DecidableEq Symbol] [DecidableEq Refinement]
    (rows : Node → List (Edge (Source Node) (Label Symbol Refinement)))
    (identity : Node → Nat) (unique : IdentityUnique identity) (registry : Registry Node)
    (keyed : WellKeyed identity registry) (node : Node) (memo : Memo (Source Node) Symbol Refinement)
    (valid : ValidMemo (graph rows registry) memo)
    (resolved : ∀ key variants, memo key = some variants → ResolvedReads rows registry (sizeOf key.2) key.2 key.1) :
    ValidMemo (graph rows (register identity registry node)) memo := by
  apply memo_rows_congr _ _ memo valid
  intro key variants found state visited
  exact register_rows rows identity unique registry keyed node (sizeOf key.2) key.2 key.1
    (resolved key variants found) state visited

/-- An unresolved reference can acquire new rows; registry growth alone does not justify cache reuse. -/
theorem unresolved_rows_change :
    let rows : Nat → List (Edge (Source Nat) Nat) := fun _ => [⟨7, [], fun _ => true⟩]
    let registry : Registry Nat := fun _ => none
    graph rows registry (.reference 3) = [] ∧
      graph rows (register id registry 3) (.reference 3) ≠ [] := by
  simp [graph, register]

end MicroCFTA.PruneDependencies
