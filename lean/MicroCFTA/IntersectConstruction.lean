import MicroCFTA.IntersectStructure

/-!
# Finite interned payload construction

A construction trace records completed payloads in reverse order. Constructor,
union, and binder payloads use children already in the trace. A recursive
reference is a leaf. It can precede the binder with the same identity because
the two inputs have different tags. Reuse of an interned payload adds no step.

This order is payload completion order, not numeric identity allocation order.
`identifyNode` can assign a binder identity before it constructs the body at
that identity. The trace does not permit a direct Haskell knot in the payloads.
-/
namespace MicroCFTA.IntersectSchedule
open Language Binding BinderLanguage

/-- Direct containment reads a binder body, row children, or union members. -/
def payloadChildren (view : View Symbol) : Input → List Input
  | .empty | .ref _ => []
  | .mu name => [view.body name]
  | .node name => (view.rows name).flatMap Row.children
  | .union name => view.members name

/-- Each new completed payload uses previously completed direct child payloads. -/
inductive PayloadConstructed (view : View Symbol) : List Input → Prop where
  | nil : PayloadConstructed view []
  | add (before : PayloadConstructed view nodes) (fresh : input ∉ nodes)
      (children : ∀ child ∈ payloadChildren view input, child ∈ nodes) :
      PayloadConstructed view (input :: nodes)

/-- Every child of a completed payload remains in the completed trace. -/
theorem constructed_children (view : View Symbol) (nodes : List Input) (built : PayloadConstructed view nodes)
    (input : Input) (present : input ∈ nodes) (child : Input) (member : child ∈ payloadChildren view input) : child ∈ nodes := by
  induction built with
  | nil => cases present
  | @add nodes next before fresh children ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_of_mem _ (children child member)
    · exact List.mem_cons_of_mem _ (ih present)

/-- Completion position gives every represented input a finite positive structural size. -/
def constructionSize : List Input → Input → Nat
  | [], _ => 1
  | next :: nodes, input => if input = next then nodes.length + 2 else constructionSize nodes input

/-- Construction size is positive even at unused entries of the total payload view. -/
theorem construction_size_positive (nodes : List Input) (input : Input) : 0 < constructionSize nodes input := by
  induction nodes with
  | nil => exact Nat.zero_lt_one
  | cons next nodes ih => simp only [constructionSize]; split <;> omega

/-- Each completion size is bounded by the finite trace length. -/
theorem construction_size_bounded (nodes : List Input) (input : Input) : constructionSize nodes input ≤ nodes.length + 1 := by
  induction nodes with
  | nil => exact Nat.le_refl _
  | cons next nodes ih => simp only [constructionSize, List.length_cons]; split <;> omega

/-- A fresh completion preserves the size of every earlier completed payload. -/
theorem construction_size_old (nodes : List Input) (next input : Input) (fresh : next ∉ nodes) (member : input ∈ nodes) :
    constructionSize (next :: nodes) input = constructionSize nodes input := by
  have different : input ≠ next := fun same => fresh (same ▸ member)
  simp only [constructionSize, ite_eq_right different]

/-- Every direct payload edge strictly decreases the size derived from construction order. -/
theorem construction_size_decreases (view : View Symbol) (nodes : List Input) (built : PayloadConstructed view nodes)
    (input : Input) (present : input ∈ nodes) (child : Input) (member : child ∈ payloadChildren view input) :
    constructionSize nodes child < constructionSize nodes input := by
  induction built with
  | nil => cases present
  | @add nodes next before fresh children ih =>
    rcases List.mem_cons.mp present with rfl | present
    · rw [construction_size_old nodes input child fresh (children child member)]
      have bound := construction_size_bounded nodes child
      simp only [constructionSize, ite_true]
      omega
    · have childMember := constructed_children view nodes before input present child member
      rw [construction_size_old nodes next child fresh childMember, construction_size_old nodes next input fresh present]
      exact ih present

/-- A finite view returns constructor and union payloads only for completed inputs. -/
structure PayloadTrace (view : View Symbol) where
  nodes : List Input
  built : PayloadConstructed view nodes
  rows : ∀ name row, row ∈ view.rows name → Input.node name ∈ nodes
  members : ∀ name child, child ∈ view.members name → Input.union name ∈ nodes

/-- A constructor child is a direct dependency of its completed node. -/
theorem row_payload_child (view : View Symbol) (name : Nat) (row : Row Symbol)
    (present : row ∈ view.rows name) (child : Input) (member : child ∈ row.children) :
    child ∈ payloadChildren view (.node name) :=
  List.mem_flatMap.mpr ⟨row, present, member⟩

/-- Finite construction derives every structural requirement of recursive intersection. -/
def constructedInputBounds (view : View Symbol) (inputs : FiniteInput view) (freeCorrect : FreeCorrect view)
    (trace : PayloadTrace view) (represented : ∀ input, inputs.valid input → input ∈ trace.nodes) : InputBounds view inputs :=
  structuralInputBounds view inputs freeCorrect (inputPairs trace.nodes)
    (fun left right leftValid rightValid _ _ =>
      input_pair_mem trace.nodes left right (represented left leftValid) (represented right rightValid))
    (structuralLocalWeight view (constructionSize trace.nodes)
      (fun name => construction_size_positive trace.nodes (.ref name))
      (fun name => construction_size_positive trace.nodes (.node name))
      (fun name row present child member => construction_size_decreases view trace.nodes trace.built (.node name)
        (trace.rows name row present) child (row_payload_child view name row present child member))
      (fun name child member => construction_size_decreases view trace.nodes trace.built (.union name)
        (trace.members name child member) child member))
    (constructionSize trace.nodes)
    (fun name valid => construction_size_decreases view trace.nodes trace.built (.mu name) (represented _ valid)
      (view.body name) (by simp [payloadChildren]))
    (fun name valid row present child member => construction_size_decreases view trace.nodes trace.built (.node name)
      (represented _ valid) child (row_payload_child view name row present child member))
    (fun name valid child member => construction_size_decreases view trace.nodes trace.built (.union name)
      (represented _ valid) child member)

/-- A completed finite payload table derives validity of every structural payload read. -/
def tracedFiniteInput (view : View Symbol) (trace : PayloadTrace view)
    (representative : Nat → Input)
    (identities : ∀ input ∈ trace.nodes, input ≠ .empty → representative (identity input) = inputRepresentative input)
    (references : ∀ name, Input.ref name ∈ trace.nodes → Input.mu name ∈ trace.nodes)
    (copies : ∀ input ∈ trace.nodes, closed view input = true → ∀ environment,
      meaning environment (view.copy input) = fun term => ∃ rank, InputDerivation view input rank term) : FiniteInput view where
  valid := fun input => input ∈ trace.nodes
  representative := representative
  identity_exact := identities
  body_valid name member := constructed_children view trace.nodes trace.built (.mu name) member (view.body name) (by simp [payloadChildren])
  reference_valid := references
  row_valid name member row present child belongs :=
    constructed_children view trace.nodes trace.built (.node name) member child (row_payload_child view name row present child belongs)
  union_valid name member child belongs := constructed_children view trace.nodes trace.built (.union name) member child belongs
  copy_exact := copies

/-- A finite completed payload trace gives total, exact intersection without an assumed size or pair bound. -/
theorem constructed_intersection_total [DecidableEq Symbol] (view : View Symbol) (inputs : FiniteInput view)
    (freeCorrect : FreeCorrect view) (trace : PayloadTrace view)
    (represented : ∀ input, inputs.valid input → input ∈ trace.nodes)
    (left right : Input) (leftValid : inputs.valid left) (rightValid : inputs.valid right)
    (leftClosed : closed view left = true) (rightClosed : closed view right = true) :
    ∃ bound result,
      (∀ fuel, bound ≤ fuel → run view fuel {} left right = .ok result) ∧
      ∀ environment term, meaning environment result term ↔
        (∃ rank, InputDerivation view left rank term) ∧ (∃ rank, InputDerivation view right rank term) :=
  finite_intersection_total view inputs freeCorrect (constructedInputBounds view inputs freeCorrect trace represented)
    left right leftValid rightValid leftClosed rightClosed

/-- A finite construction cannot use a binder directly as its own payload body. -/
theorem constructed_body_not_self (view : View Symbol) (trace : PayloadTrace view) (name : Nat)
    (present : Input.mu name ∈ trace.nodes) : view.body name ≠ .mu name := by
  intro same
  have decreases := construction_size_decreases view trace.nodes trace.built (.mu name) present
    (view.body name) (by simp [payloadChildren])
  rw [same] at decreases
  exact Nat.lt_irrefl _ decreases

/-- Explicit references can precede their same-identity binder in a finite construction. -/
theorem reference_then_binder_constructed (view : View Symbol) (name : Nat) (body : view.body name = .ref name) :
    PayloadConstructed view [.mu name, .ref name] := by
  apply PayloadConstructed.add
  · exact .add .nil (by simp) (by simp [payloadChildren])
  · simp
  · simp [payloadChildren, body]

/-- A trace contains all direct payloads of any completed root. -/
theorem constructed_contains_reachable (view : View Symbol) (trace : PayloadTrace view) (root input : Input)
    (present : root ∈ trace.nodes) (reachable : PayloadReach view root input) : input ∈ trace.nodes := by
  induction reachable with
  | root => exact present
  | body _ ih => exact constructed_children view trace.nodes trace.built _ ih _ (by simp [payloadChildren])
  | child _ rowMember childMember ih =>
    exact constructed_children view trace.nodes trace.built _ ih _ (row_payload_child view _ _ rowMember _ childMember)
  | member _ member ih => exact constructed_children view trace.nodes trace.built _ ih _ member

/-- Collecting the payloads of closed roots includes every referenced binder identity. -/
theorem traced_references_bound (view : View Symbol) (freeCorrect : FreeCorrect view) (trace : PayloadTrace view)
    (roots : List Input) (rootsPresent : ∀ root ∈ roots, root ∈ trace.nodes)
    (rootsClosed : ∀ root ∈ roots, closed view root = true)
    (rooted : ∀ input ∈ trace.nodes, ∃ root ∈ roots, PayloadReach view root input)
    (name : Nat) (present : Input.ref name ∈ trace.nodes) : Input.mu name ∈ trace.nodes := by
  obtain ⟨root, member, reachable⟩ := rooted (.ref name) present
  rcases payload_free_scope view freeCorrect root (.ref name) reachable name (by rw [freeCorrect.reference]; simp) with free | bound
  · have empty : view.free root = [] := List.isEmpty_iff.mp (rootsClosed root member)
    simp [empty] at free
  · exact constructed_contains_reachable view trace root (.mu name) (rootsPresent root member) bound

end MicroCFTA.IntersectSchedule
