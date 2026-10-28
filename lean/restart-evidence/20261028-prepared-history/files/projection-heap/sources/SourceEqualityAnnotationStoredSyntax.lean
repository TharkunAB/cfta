import MicroCFTA.SourceEqualityAnnotationConstruction

/-!
# Source annotation checks through actual stored-body compilation

Prepared syntax copies each complete original guard. Closed captures emit no
new guard. Original physical cache annotations therefore derive every emitted
check in substitution and optional recursive binder construction.
-/
namespace MicroCFTA.SourceEqualityAnnotationStoredSyntax
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedStoredSubstitution
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationHeap SourceEqualityAnnotationConstruction

/-- Prepared child compilation retains the original ordered annotation checks. -/
theorem many_allowed (valid : Guard → Prop) (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (values : List (Value Symbol Guard)) (checked : ∀ value ∈ values, Allowed valid (encode context locals value)) :
    ManyAllowed valid (encodeMany context locals values) := by
  induction values with
  | nil => simp only [encodeMany, ManyAllowed]
  | cons first rest ih =>
      simp only [encodeMany, ManyAllowed]
      exact ⟨checked first List.mem_cons_self, ih (fun value member => checked value (List.mem_cons_of_mem _ member))⟩

/-- Prepared edge compilation emits exactly the original source guard fields. -/
theorem edges_allowed (valid : Guard → Prop) (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference)
    (edges : List (EdgeValue Symbol Guard)) (guards : ∀ edge ∈ edges, valid edge.entry.key.constraint)
    (checked : ∀ child ∈ edges.flatMap EdgeValue.children, Allowed valid (encode context locals child)) :
    EdgesAllowed valid (encodeEdges context locals edges) := by
  induction edges with
  | nil => simp only [encodeEdges, EdgesAllowed]
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          simp only [encodeEdges, EdgesAllowed]
          exact ⟨guards (.mk entry children) List.mem_cons_self,
            many_allowed valid context locals children (fun child member => checked child (by simp [EdgeValue.children, member])),
            ih (fun edge member => guards edge (List.mem_cons_of_mem _ member)) (fun child member => checked child (by simp [member]))⟩

/-- Actual stored-body compilation preserves source annotation validity at every semantic constructor. -/
theorem encode_allowed (valid : Guard → Prop) (value : Value Symbol Guard) (annotated : Annotated valid value)
    (context : List (Value Symbol Guard)) (locals : List InternedBinderProtocol.Reference) : Allowed valid (encode context locals value) := by
  induction annotated generalizing locals with
  | empty => simp only [encode, Value.free, List.isEmpty_nil, ↓reduceIte, Allowed]
  | reference name =>
      simp only [encode.eq_def, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      split <;> simp only [Allowed]
  | node entry edges depth free guards children ih =>
      rw [encode.eq_def]
      split
      · simp only [Allowed]
      · simpa only [Allowed] using edges_allowed valid context locals edges guards (fun child member => ih child member locals)
  | union entry members depth free children ih =>
      rw [encode.eq_def]
      split
      · simp only [Allowed]
      · simpa only [Allowed] using many_allowed valid context locals members (fun child member => ih child member locals)
  | mu entry body depth ordinary annotated ih =>
      rw [encode.eq_def]
      split
      · simp only [Allowed]
      · simpa only [Allowed] using ih (.interned entry.identity :: locals)

/-- Actual optional source binders retain the physical annotation heap in complete and pending outcomes. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (key : Nat × Nat)
    (body : Value Symbol Guard) (state : State Symbol Guard) (heap : Heap valid state) (facts : Facts state) (resident : Available state body) :
    Heap valid (SourceRecursiveIntersectionMaybeMu.maybeMu key body state).state := by
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq key body state state facts resident]
  split
  · have prepared := encode_allowed valid body
        (SourceEqualityAnnotationHeap.available valid state heap facts.linked body resident) (leaves body) [.intersection key.1 key.2]
    exact SourceEqualityAnnotationConstruction.build valid _ (by simpa only [Allowed] using prepared) _ state heap
  · simpa only [InternedNestedConstruction.Outcome.state] using heap

end MicroCFTA.SourceEqualityAnnotationStoredSyntax
