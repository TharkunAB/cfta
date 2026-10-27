/-- A successful constraint projection names only existing root children. -/
def Fits (constraint : Constraint) (arity : Nat) : Prop :=
  ∀ tries residual,
    SourcePruningEnumerationConstraint.project constraint = some (tries, residual) →
    ∀ start, arityAllows arity (suspendedVars start tries) = true

/-- Every stored canonical edge key retains projected arity for its actual child count. -/
def Heap (state : State Symbol Constraint) : Prop :=
  ∀ key edge, state.edgeRecords key = some edge → Fits key.constraint key.children.length

/-- Coherent resident payloads have the child count stored in their canonical key. -/
theorem Heap.edge (state : State Symbol Constraint) (heap : Heap state)
    (coherent : Coherent state) (edge : EdgeValue Symbol Constraint)
    (resident : EdgeResident state edge) :
    Fits edge.entry.key.constraint edge.children.length := by
  have fields := (coherent.edges edge.entry.key edge resident).2.2
  have lengthSame : edge.children.length = edge.entry.key.children.length := by
    simpa only [List.length_map] using congrArg List.length fields
  have checked := heap edge.entry.key edge resident
  rw [← lengthSame] at checked
  exact checked
