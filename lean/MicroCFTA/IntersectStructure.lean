import MicroCFTA.IntersectTotal

/-!
# Closed-root bounds from finite lexical payloads

Direct payload containment does not follow recursive references. Cached free
variables show that each reference reachable from a closed root has a binder
inside that root. Thus reference unfolding cannot leave the root's finite
payload structure. This derives the closed-root bound used by termination.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Structural reachability follows direct payload containment and stops at references. -/
inductive PayloadReach (view : View Symbol) (root : Input) : Input → Prop where
  | root : PayloadReach view root root
  | body (before : PayloadReach view root (.mu name)) : PayloadReach view root (view.body name)
  | child (before : PayloadReach view root (.node name)) (rowMember : row ∈ view.rows name)
      (childMember : child ∈ row.children) : PayloadReach view root child
  | member (before : PayloadReach view root (.union name)) (member : child ∈ view.members name) :
      PayloadReach view root child

/-- Every contained payload is also reachable by the full input relation. -/
theorem payload_reach_input (view : View Symbol) (root input : Input) (reachable : PayloadReach view root input) :
    InputReach view root input := by
  induction reachable with
  | root => exact .root
  | body _ ih => exact .body ih
  | child _ rowMember childMember ih => exact .child ih rowMember childMember
  | member _ member ih => exact .member ih member

/-- A free variable of a contained payload is free at the root or is bound inside the root. -/
theorem payload_free_scope (view : View Symbol) (freeCorrect : FreeCorrect view) (root input : Input)
    (reachable : PayloadReach view root input) (name : Nat) (free : name ∈ view.free input) :
    name ∈ view.free root ∨ PayloadReach view root (.mu name) := by
  induction reachable with
  | root => exact Or.inl free
  | @body binder before ih =>
    by_cases same : name = binder
    · subst name; exact Or.inr before
    · exact ih ((freeCorrect.binder binder name).mpr ⟨free, same⟩)
  | @child node row child before rowMember childMember ih =>
    exact ih ((freeCorrect.node node name).mpr ⟨row, rowMember, child, childMember, free⟩)
  | @member node child before member ih =>
    exact ih ((freeCorrect.union node name).mpr ⟨child, member, free⟩)

/-- Reference unfolding from a closed root stays inside its direct finite payloads. -/
theorem closed_reach_payload (view : View Symbol) (freeCorrect : FreeCorrect view) (root input : Input)
    (isClosed : closed view root = true) (reachable : InputReach view root input) : PayloadReach view root input := by
  have rootEmpty : view.free root = [] := List.isEmpty_iff.mp isClosed
  induction reachable with
  | root => exact .root
  | body _ ih => exact .body ih
  | child _ rowMember childMember ih => exact .child ih rowMember childMember
  | member _ member ih => exact .member ih member
  | @reference name before ih =>
    rcases payload_free_scope view freeCorrect root (.ref name) ih name (by rw [freeCorrect.reference]; simp) with free | bound
    · simp [rootEmpty] at free
    · exact bound

/-- A direct finite payload size bounds every contained node. -/
theorem payload_size_below (view : View Symbol) (inputs : FiniteInput view) (size : Input → Nat)
    (bodyLess : ∀ name, inputs.valid (.mu name) → size (view.body name) < size (.mu name))
    (childLess : ∀ name, inputs.valid (.node name) → ∀ row ∈ view.rows name, ∀ child ∈ row.children, size child < size (.node name))
    (memberLess : ∀ name, inputs.valid (.union name) → ∀ child ∈ view.members name, size child < size (.union name))
    (root input : Input) (valid : inputs.valid root) (reachable : PayloadReach view root input) : Below size root input := by
  have weaker : ∀ input, Below size root input → size input ≤ size root := by
    intro input below
    rcases below with rfl | less
    · exact Nat.le_refl _
    · exact Nat.le_of_lt less
  induction reachable with
  | root => exact Or.inl rfl
  | @body name before ih =>
    exact Or.inr (Nat.lt_of_lt_of_le
      (bodyLess name (input_reach_valid view inputs root _ valid (payload_reach_input view root _ before))) (weaker _ ih))
  | @child name row child before rowMember childMember ih =>
    exact Or.inr (Nat.lt_of_lt_of_le
      (childLess name (input_reach_valid view inputs root _ valid (payload_reach_input view root _ before)) row rowMember child childMember)
      (weaker _ ih))
  | @member name child before member ih =>
    exact Or.inr (Nat.lt_of_lt_of_le
      (memberLess name (input_reach_valid view inputs root _ valid (payload_reach_input view root _ before)) child member) (weaker _ ih))

/-- The termination interface follows from finite payload size and cached free-variable equations. -/
def structuralInputBounds (view : View Symbol) (inputs : FiniteInput view) (freeCorrect : FreeCorrect view)
    (pairs : List Pair)
    (pairMem : ∀ left right, inputs.valid left → inputs.valid right → left ≠ .empty → right ≠ .empty → pair left right ∈ pairs)
    (localWeight : LocalWeight view) (size : Input → Nat)
    (bodyLess : ∀ name, inputs.valid (.mu name) → size (view.body name) < size (.mu name))
    (childLess : ∀ name, inputs.valid (.node name) → ∀ row ∈ view.rows name, ∀ child ∈ row.children, size child < size (.node name))
    (memberLess : ∀ name, inputs.valid (.union name) → ∀ child ∈ view.members name, size child < size (.union name)) : InputBounds view inputs where
  pairs := pairs
  pair_mem := pairMem
  localWeight := localWeight
  size := size
  body := bodyLess
  child := childLess
  member := memberLess
  closed_reach root valid isClosed input reachable :=
    payload_size_below view inputs size bodyLess childLess memberLess root input valid
      (closed_reach_payload view freeCorrect root input isClosed reachable)

/-- A finite input list gives a finite universe of canonical intersection pairs. -/
def inputPairs (nodes : List Input) : List Pair :=
  nodes.flatMap fun left => nodes.map (pair left)

/-- The finite pair universe contains every pair of its original input nodes. -/
theorem input_pair_mem (nodes : List Input) (left right : Input) (leftMember : left ∈ nodes) (rightMember : right ∈ nodes) :
    pair left right ∈ inputPairs nodes := by
  exact List.mem_flatMap.mpr ⟨left, leftMember, List.mem_map.mpr ⟨right, rightMember, rfl⟩⟩

/-- The local schedule weight stops at binders and uses one phase for references. -/
def localSize (size : Input → Nat) : Input → Nat
  | .mu _ => 0
  | .ref _ => 1
  | input => size input

/-- Stopping at binders cannot increase the full structural payload size. -/
theorem localSize_le (size : Input → Nat) (references : ∀ name, 1 ≤ size (.ref name)) (input : Input) :
    localSize size input ≤ size input := by
  cases input <;> simp only [localSize]
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact references _

/-- The full payload size derives the separate local constructor and union weight. -/
def structuralLocalWeight (view : View Symbol) (size : Input → Nat)
    (references : ∀ name, 1 ≤ size (.ref name)) (positive : ∀ name, 0 < size (.node name))
    (childLess : ∀ name row, row ∈ view.rows name → ∀ child ∈ row.children, size child < size (.node name))
    (memberLess : ∀ name child, child ∈ view.members name → size child < size (.union name)) : LocalWeight view where
  value := localSize size
  binder := fun _ => rfl
  reference := fun _ => rfl
  positive := positive
  child name row member child present := Nat.lt_of_le_of_lt (localSize_le size references child) (childLess name row member child present)
  member name child present := Nat.lt_of_le_of_lt (localSize_le size references child) (memberLess name child present)

/-- Finite payload identities and direct structural size give the full exact intersection result. -/
theorem structural_intersection_total [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (nodes : List Input) (complete : ∀ input, inputs.valid input → input ∈ nodes)
    (size : Input → Nat) (references : ∀ name, 1 ≤ size (.ref name)) (positive : ∀ name, 0 < size (.node name))
    (bodyLess : ∀ name, inputs.valid (.mu name) → size (view.body name) < size (.mu name))
    (childLess : ∀ name row, row ∈ view.rows name → ∀ child ∈ row.children, size child < size (.node name))
    (memberLess : ∀ name child, child ∈ view.members name → size child < size (.union name))
    (left right : Input) (leftValid : inputs.valid left) (rightValid : inputs.valid right)
    (leftClosed : closed view left = true) (rightClosed : closed view right = true) :
    ∃ bound result,
      (∀ fuel, bound ≤ fuel → run view fuel {} left right = .ok result) ∧
      ∀ environment term, meaning environment result term ↔
        (∃ rank, InputDerivation view left rank term) ∧ (∃ rank, InputDerivation view right rank term) := by
  let bounds := structuralInputBounds view inputs freeCorrect (inputPairs nodes)
    (fun first second firstValid secondValid _ _ => input_pair_mem nodes first second (complete first firstValid) (complete second secondValid))
    (structuralLocalWeight view size references positive childLess memberLess) size bodyLess
    (fun name _ => childLess name) (fun name _ => memberLess name)
  exact finite_intersection_total view inputs freeCorrect bounds left right leftValid rightValid leftClosed rightClosed

end MicroCFTA.IntersectSchedule
