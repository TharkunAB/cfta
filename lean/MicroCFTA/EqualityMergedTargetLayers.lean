import MicroCFTA.MergedOrdinaryHeight

/-!
# Layer progress for repeated target merging

A merge can leave a singleton child column unchanged. One pass can thus
normalize only the root. If small roots map each child through the same
merge relation, each further pass normalizes one more ordinary layer.

This theorem states the remaining source-shape obligations explicitly.
It does not assume a finite universe or termination of recursive calls.
It does not prove termination of the complete equality schedule.
-/
namespace MicroCFTA.EqualityMergedTargetLayers
open InternedConstructorTemplates MergedOrdinaryHeight

/-- The merge worker traverses children only below a closed ordinary root. -/
def children : Value Symbol Guard → List (Value Symbol Guard)
  | .node _ edges _ free => if free = [] then edges.flatMap EdgeValue.children else []
  | _ => []

/-- Every traversed child has strictly smaller ordinary height. -/
theorem child_height (value child : Value Symbol Guard) (member : child ∈ children value) :
    height child < height value := by
  cases value with
  | empty | reference | union | mu => simp [children] at member
  | node entry edges depth free =>
      simp only [children] at member
      split at member
      · obtain ⟨edge, present, included⟩ := List.mem_flatMap.mp member
        exact child_lt entry edges depth free edge present child included
      · contradiction

/-- A bounded layer property checks the current root and then its ordinary children. -/
def Layer (good : Value Symbol Guard → Prop) : Nat → Value Symbol Guard → Prop
  | 0, _ => True
  | depth + 1, value => good value ∧ ∀ child ∈ children value, Layer good depth child

/-- Every ordinary node reached by the merge worker satisfies the root property. -/
inductive Normal (good : Value Symbol Guard → Prop) : Value Symbol Guard → Prop where
  | intro {value} (root : good value)
      (below : ∀ child ∈ children value, Normal good child) : Normal good value

/-- A fully normalized value satisfies every bounded layer property. -/
theorem normal_layer (good : Value Symbol Guard → Prop) (depth : Nat) (value : Value Symbol Guard)
    (normal : Normal good value) : Layer good depth value := by
  induction depth generalizing value with
  | zero => trivial
  | succ depth ih =>
      cases normal with
      | intro root below => exact ⟨root, fun child member => ih child (below child member)⟩

/-- Ordinary height suffices to turn a bounded layer property into full normalization. -/
theorem layer_normal (good : Value Symbol Guard → Prop)
    (boundary : ∀ value, height value = 0 → good value)
    (depth : Nat) (value : Value Symbol Guard) (enough : height value ≤ depth)
    (layer : Layer good depth value) : Normal good value := by
  induction depth generalizing value with
  | zero =>
      refine .intro (boundary value (by omega)) ?_
      intro child member
      have smaller := child_height value child member
      omega
  | succ depth ih =>
      refine .intro layer.1 ?_
      intro child member
      exact ih child (by have smaller := child_height value child member; omega) (layer.2 child member)

/-- These two local shape facts imply layer progress. They do not assert completion. -/
structure Shape (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (good : Value Symbol Guard → Prop) : Prop where
  root : ∀ before after, merge before after → good after
  smallChildren : ∀ before after, merge before after → good before →
    ∀ child ∈ children after, ∃ original ∈ children before, merge original child

/-- A completed merge adds one normalized layer, including the singleton-column delay. -/
theorem layer_step (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (good : Value Symbol Guard → Prop) (shape : Shape merge good)
    (depth : Nat) (before after : Value Symbol Guard)
    (done : merge before after) (layer : Layer good depth before) : Layer good (depth + 1) after := by
  induction depth generalizing before after with
  | zero => exact ⟨shape.root before after done, fun _ _ => trivial⟩
  | succ depth ih =>
      refine ⟨shape.root before after done, ?_⟩
      intro child member
      obtain ⟨original, included, recursive⟩ := shape.smallChildren before after done layer.1 child member
      exact ih original child recursive (layer.2 original included)

/-- A trace records a fixed number of completed successive merge calls. -/
inductive Trace (merge : Value Symbol Guard → Value Symbol Guard → Prop) :
    Nat → Value Symbol Guard → Value Symbol Guard → Prop where
  | nil (value) : Trace merge 0 value value
  | snoc {count before middle after} (previous : Trace merge count before middle)
      (last : merge middle after) : Trace merge (count + 1) before after

/-- Every completed pass adds a layer even when the preceding pass changed the root identity. -/
theorem trace_layers (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (good : Value Symbol Guard → Prop) (shape : Shape merge good)
    (count : Nat) (before after : Value Symbol Guard) (trace : Trace merge count before after) :
    Layer good count after := by
  induction trace with
  | nil => trivial
  | snoc previous last ih => exact layer_step merge good shape _ _ _ last ih

/-- A local nonincrease theorem bounds the height after any number of completed calls. -/
theorem trace_height (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (nonincrease : ∀ before after, merge before after → height after ≤ height before)
    (count : Nat) (before after : Value Symbol Guard) (trace : Trace merge count before after) :
    height after ≤ height before := by
  induction trace with
  | nil => exact Nat.le_refl _
  | snoc previous last ih => exact Nat.le_trans (nonincrease _ _ last) ih

/-- The original ordinary height bounds the passes needed for recursive root normalization. -/
theorem trace_normal (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (good : Value Symbol Guard → Prop) (shape : Shape merge good)
    (boundary : ∀ value, height value = 0 → good value)
    (nonincrease : ∀ before after, merge before after → height after ≤ height before)
    (count : Nat) (before after : Value Symbol Guard) (trace : Trace merge count before after)
    (enough : height before ≤ count) : Normal good after :=
  layer_normal good boundary count after
    (Nat.le_trans (trace_height merge nonincrease count before after trace) enough)
    (trace_layers merge good shape count before after trace)

/-- Exact constructor readback on normal inputs turns the layer bound into a fixed-point bound. -/
theorem trace_fixed (merge : Value Symbol Guard → Value Symbol Guard → Prop)
    (good : Value Symbol Guard → Prop) (shape : Shape merge good)
    (boundary : ∀ value, height value = 0 → good value)
    (nonincrease : ∀ before after, merge before after → height after ≤ height before)
    (readback : ∀ before after, merge before after → Normal good before → after.referenceOf = before.referenceOf)
    (count : Nat) (before after next : Value Symbol Guard) (trace : Trace merge count before after)
    (enough : height before ≤ count) (done : merge after next) : next.referenceOf = after.referenceOf :=
  readback after next done (trace_normal merge good shape boundary nonincrease count before after trace enough)

end MicroCFTA.EqualityMergedTargetLayers
