import MicroCFTA.SourceRecursiveIntersectionInputExact

/-!
# Original physical input views through actual cache growth

Actual record and reservation growth retain the original payloads and every
field of their input view. New allocations can change unused total defaults.
The equations apply to the original available input domain.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule Language

/-- Actual growth retains the complete payload selected by each original available input. -/
theorem payload_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (value : Value Symbol Guard)
    (available : Available before value) (input : Input)
    (complete : IntersectionFlatMemoKey.input value.referenceOf = some input) :
    payload after input = payload before input := by
  rw [payload_readback before beforeFacts value available input complete,
    payload_readback after afterFacts value (available.grows before after growth history) input complete]

/-- Original input syntax remains original and available after actual source growth. -/
theorem OriginalInput.grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (input : Input) (original : OriginalInput before input) : OriginalInput after input := by
  obtain ⟨value, original, available, complete⟩ := original
  exact ⟨value, original, available.grows before after growth history, complete⟩

/-- Cached free-name view fields of original physical inputs remain exact after growth. -/
theorem free_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (input : Input) (original : OriginalInput before input) : (view after holds).free input = (view before holds).free input := by
  obtain ⟨value, _, available, complete⟩ := original
  exact congrArg freeNames (payload_grows before after beforeFacts afterFacts growth history value available input complete)

/-- Copied original physical syntax remains exact after source growth. -/
theorem copy_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (input : Input) (original : OriginalInput before input) : (view after holds).copy input = (view before holds).copy input := by
  obtain ⟨value, _, available, complete⟩ := original
  exact congrArg (shape holds) (payload_grows before after beforeFacts afterFacts growth history value available input complete)

/-- Original Mu body inputs remain exact through actual source growth. -/
theorem body_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (name : Nat) (original : OriginalInput before (.mu name)) : (view after holds).body name = (view before holds).body name := by
  obtain ⟨value, _, available, complete⟩ := original
  have same := payload_grows before after beforeFacts afterFacts growth history value available (.mu name) complete
  simp only [view, same]

/-- Original guarded rows and their ordered child inputs remain exact through source growth. -/
theorem rows_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (name : Nat) (original : OriginalInput before (.node name)) : (view after holds).rows name = (view before holds).rows name := by
  obtain ⟨value, _, available, complete⟩ := original
  have same := payload_grows before after beforeFacts afterFacts growth history value available (.node name) complete
  simp only [view, same]

/-- Original ordered union members remain exact through actual source growth. -/
theorem members_grows (before after : InternedConstructorTemplates.State Symbol Guard)
    (beforeFacts : Facts before) (afterFacts : Facts after) (growth : Grows before after)
    (history : Extends before.nodes.issued after.nodes.issued) (holds : Guard → Term Symbol → Bool)
    (name : Nat) (original : OriginalInput before (.union name)) : (view after holds).members name = (view before holds).members name := by
  obtain ⟨value, _, available, complete⟩ := original
  have same := payload_grows before after beforeFacts afterFacts growth history value available (.union name) complete
  simp only [view, same]

end MicroCFTA.SourceRecursiveIntersectionInputView
