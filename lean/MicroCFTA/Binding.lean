import MicroCFTA.Cache

/-!
# Recursive binding and free-environment cache keys

`Interned.Type.substitutionPlan` traverses a finite interned shape once. It
then substitutes an environment. Nested binders mask their own references.
The source gives every live binder a distinct identity and rebuilds binders
with `createMu`. This structural model keeps those identities. It does not
prove the source's identity allocation or alpha-renaming adapter.

`branch` stores one labelled, constrained edge. `alternatives` stores a node's
outgoing edges. The payload includes every part of the edge other than its
children. Lists stand for the source's ordered sets and maps.
-/

namespace MicroCFTA.Binding

/-- A finite recursive graph shape before interning. -/
inductive Shape (Payload : Type) where
  | empty
  | ref (name : Nat)
  | branch (payload : Payload) (children : List (Shape Payload))
  | alternatives (edges : List (Shape Payload))
  | binder (name : Nat) (body : Shape Payload)
  deriving Repr

mutual
  /-- Collect free recursive references. Repetitions do not change cache keys. -/
  def free : Shape Payload → List Nat
    | .empty => []
    | .ref name => [name]
    | .branch _ children => freeList children
    | .alternatives edges => freeList edges
    | .binder name body => (free body).filter (· != name)

  /-- Collect references from a child forest. -/
  def freeList : List (Shape Payload) → List Nat
    | [] => []
    | shape :: rest => free shape ++ freeList rest
end

/-- A simultaneous substitution. Absent entries retain their references. -/
abbrev Environment (Payload : Type) := Nat → Option (Shape Payload)

/-- Hide a binder's local reference from external substitutions. -/
def mask (environment : Environment Payload) (bound : Nat) : Environment Payload :=
  fun name => if name = bound then none else environment name

mutual
  /-- Execute substitution on a prepared finite shape. -/
  def substitute (environment : Environment Payload) : Shape Payload → Shape Payload
    | .empty => .empty
    | .ref name => (environment name).getD (.ref name)
    | .branch payload children => .branch payload (substituteList environment children)
    | .alternatives edges => .alternatives (substituteList environment edges)
    | .binder name body => .binder name (substitute (mask environment name) body)

  /-- Preserve child order and multiplicity during substitution. -/
  def substituteList (environment : Environment Payload) : List (Shape Payload) → List (Shape Payload)
    | [] => []
    | shape :: rest => substitute environment shape :: substituteList environment rest
end

/-- Substitution can read only the free references of its input shape. -/
theorem substitute_congr (shape : Shape Payload) (left right : Environment Payload)
    (agree : ∀ name ∈ free shape, left name = right name) :
    substitute left shape = substitute right shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ left right : Environment Payload,
      (∀ name ∈ freeList shapes, left name = right name) →
      substituteList left shapes = substituteList right shapes)
    generalizing left right with
  | empty => rfl
  | ref name => simp [substitute, agree name (by simp [free])]
  | branch payload children ih =>
      simp only [substitute]
      rw [ih left right agree]
  | alternatives edges ih =>
      simp only [substitute]
      rw [ih left right agree]
  | binder bound body ih =>
      simp only [substitute]
      congr 1
      apply ih
      intro name present
      by_cases same : name = bound
      · simp [mask, same]
      · simp only [mask, same, ite_false]
        exact agree name (by simp [free, present, same])
  | nil => rfl
  | cons shape rest first tail =>
      rename_i left right agree
      simp only [substituteList]
      congr 1
      · exact first left right (fun name present => agree name (by simp [freeList, present]))
      · exact tail left right (fun name present => agree name (by simp [freeList, present]))

/-- An empty substitution preserves the entire shape. -/
theorem substitute_empty (shape : Shape Payload) : substitute (fun _ => none) shape = shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => substituteList (fun _ => none) shapes = shapes) with
  | empty => rfl
  | ref name => rfl
  | branch payload children ih => simp [substitute, ih]
  | alternatives edges ih => simp [substitute, ih]
  | binder name body ih =>
      have same : mask (fun _ => none : Environment Payload) name = (fun _ => none) := by
        funext other
        simp [mask]
      simp [substitute, same, ih]
  | nil => rfl
  | cons shape rest first tail => simp [substituteList, first, tail]

/-- The source's closed-shape shortcut has exactly the substitution result. -/
theorem closed_unchanged (shape : Shape Payload) (closed : free shape = [])
    (environment : Environment Payload) : substitute environment shape = shape := by
  rw [substitute_congr shape environment (fun _ => none)]
  · exact substitute_empty shape
  · intro name present
    simp [closed] at present

/-- Restrict an environment to the variables that form the binder cache key. -/
def restrict (names : List Nat) (environment : Environment Payload) : Environment Payload :=
  fun name => if name ∈ names then environment name else none

/-- Omitting irrelevant environment entries preserves substitution exactly. -/
theorem restrict_correct (shape : Shape Payload) (environment : Environment Payload) :
    substitute (restrict (free shape) environment) shape = substitute environment shape := by
  apply substitute_congr
  intro name present
  simp [restrict, present]

/-- Equal restricted environments justify sharing the cached binder result. -/
theorem binding_cache_key_sound (shape : Shape Payload) (left right : Environment Payload)
    (same : restrict (free shape) left = restrict (free shape) right) :
    substitute left shape = substitute right shape := by
  rw [← restrict_correct shape left, same, restrict_correct]

/-- Compile a substitution function once from a finite shape. -/
def prepare (shape : Shape Payload) : Environment Payload → Shape Payload :=
  fun environment => if (free shape).isEmpty then shape else substitute environment shape

/-- The source closed-shape check does not change prepared-plan semantics. -/
theorem prepare_correct (shape : Shape Payload) (environment : Environment Payload) :
    prepare shape environment = substitute environment shape := by
  unfold prepare
  split
  · next closed =>
      have empty : free shape = [] := by simpa using closed
      exact (closed_unchanged shape empty environment).symm
  · rfl

/-- Replacing a free reference by itself is the identity substitution. -/
theorem identity_substitution (shape : Shape Payload) (name : Nat) :
    substitute (fun other => if other = name then some (.ref name) else none) shape = shape := by
  induction shape using Shape.rec
    (motive_2 := fun shapes => ∀ name,
      substituteList (fun other => if other = name then some (.ref name) else none) shapes = shapes)
    generalizing name with
  | empty => rfl
  | ref other =>
      by_cases same : other = name <;> simp [substitute, same]
  | branch payload children ih => simp [substitute, ih]
  | alternatives edges ih => simp [substitute, ih]
  | binder bound body ih =>
      simp only [substitute]
      congr 1
      by_cases same : bound = name
      · have masked : mask (fun other => if other = name then some (Shape.ref name : Shape Payload) else none) bound =
            (fun _ => none) := by
          subst bound
          funext other
          simp [mask]
        rw [masked]
        exact substitute_empty body
      · have masked : mask (fun other => if other = name then some (Shape.ref name : Shape Payload) else none) bound =
            (fun other => if other = name then some (.ref name) else none) := by
          funext other
          by_cases hit : other = bound
          · subst other
            simp [mask, same]
          · simp [mask, hit]
        rw [masked]
        exact ih name
  | nil => rfl
  | cons shape rest first tail => simp [substituteList, first, tail]

/-- Both probes participate in the source's interned recursive-node key. -/
structure BinderKey (Shape : Type) where
  depthProbe : Shape
  ordinaryShape : Shape

/-- Equal ordinary shapes cannot hide different depth probes. -/
theorem depth_probe_separates (first second shape : α) (different : first ≠ second) :
    (BinderKey.mk first shape) ≠ BinderKey.mk second shape := by
  intro equal
  exact different (congrArg BinderKey.depthProbe equal)

end MicroCFTA.Binding
