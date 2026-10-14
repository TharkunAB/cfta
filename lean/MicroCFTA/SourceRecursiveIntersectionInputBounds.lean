import MicroCFTA.SourceRecursiveIntersectionInputInventory

/-!
# Closed-root bounds from actual original physical records

The concrete payload rank bounds original containment and all reference
unfolding from closed roots. The actual issued carrier bounds every input
pair. These facts do not assume a completed recursive intersection.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule

/-- An original Mu input strictly contains its actual body in the physical payload rank. -/
theorem OriginalInput.body_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.mu name)) :
    weight state ((view state holds).body name) < weight state (.mu name) := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case mu entry body depth ordinary original =>
    cases complete
    exact SourceRecursiveIntersectionInputView.body_weight state facts holds entry body depth ordinary available

/-- Every row child of an original physical node strictly decreases the actual payload rank. -/
theorem OriginalInput.child_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.node name))
    (selectedRow : Row Symbol) (present : selectedRow ∈ (view state holds).rows name)
    (input : Input) (member : input ∈ selectedRow.children) : weight state input < weight state (.node name) := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case node entry edges depth free originals =>
    cases complete
    exact row_child_weight state facts holds entry edges depth free available selectedRow present input member

/-- Every member of an original physical union strictly decreases the actual payload rank. -/
theorem OriginalInput.member_weight (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (name : Nat) (original : OriginalInput state (.union name))
    (input : Input) (member : input ∈ (view state holds).members name) : weight state input < weight state (.union name) := by
  obtain ⟨value, original, available, complete⟩ := original
  cases original <;> simp only [Value.referenceOf, IntersectionFlatMemoKey.input, Option.some.injEq, reduceCtorEq] at complete <;> try contradiction
  case union entry members depth free originals =>
    cases complete
    exact SourceRecursiveIntersectionInputView.member_weight state facts holds entry members depth free available input member

/-- Original physical containment reaches the same input or a strictly smaller actual payload. -/
theorem payload_reach_below (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (reachable : PayloadReach (view state holds) root input) : Below (weight state) root input := by
  have belowLe (input : Input) (below : Below (weight state) root input) : weight state input ≤ weight state root := by
    rcases below with rfl | less
    · exact Nat.le_refl _
    · exact Nat.le_of_lt less
  induction reachable with
  | root => exact .inl rfl
  | @body name before ih =>
      have available := payload_reach_original state facts holds root (.mu name) original before
      exact .inr (Nat.lt_of_lt_of_le (available.body_weight state facts holds name) (belowLe _ ih))
  | @child name selectedRow input before present member ih =>
      have available := payload_reach_original state facts holds root (.node name) original before
      exact .inr (Nat.lt_of_lt_of_le (available.child_weight state facts holds name selectedRow present input member) (belowLe _ ih))
  | @member name input before member ih =>
      have available := payload_reach_original state facts holds root (.union name) original before
      exact .inr (Nat.lt_of_lt_of_le (available.member_weight state facts holds name input member) (belowLe _ ih))

/-- Full reference reachability from a closed original root stays below its actual physical rank. -/
theorem closed_reach_below (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (root input : Input) (original : OriginalInput state root)
    (isClosed : closed (view state holds) root = true) (reachable : InputReach (view state holds) root input) :
    Below (weight state) root input :=
  payload_reach_below state facts holds root input original
    (closed_reach_payload (view state holds) (free_correct state facts holds) root input isClosed reachable)

/-- The actual finite issued carrier contains every pair reached from two closed original roots. -/
theorem closed_pair_inventory (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Language.Term Symbol → Bool) (leftRoot rightRoot left right : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true)
    (leftReach : InputReach (view state holds) leftRoot left) (rightReach : InputReach (view state holds) rightRoot right) :
    pair left right ∈ inputPairs (inventory state) :=
  input_pair_mem (inventory state) left right
    (closed_reach_inventory state facts holds leftRoot left leftOriginal leftClosed leftReach)
    (closed_reach_inventory state facts holds rightRoot right rightOriginal rightClosed rightReach)

end MicroCFTA.SourceRecursiveIntersectionInputView
