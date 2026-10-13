import MicroCFTA.InternedEmptyNormalization
import MicroCFTA.InternedFreeOccurrenceExact

/-!
# Compositional empty and free-occurrence observations

Two records can have different canonical identities while agreeing on
emptiness and all costs for one external reference. Actual ordinary and
union constructors preserve this agreement through source normalization.
-/
namespace MicroCFTA.InternedOccurrenceObservations
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedLiveEdges InternedNonemptyRecords
open InternedFreeOccurrenceRank InternedFreeOccurrenceNode InternedFreeOccurrenceExact InternedEmptyNormalization
open InternedBinderProtocol (Reference)

/-- The observation records emptiness and each binder cost for one external name. -/
def Same (name : Reference) (first second : Value Symbol Guard) : Prop :=
  (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧
    ∀ count, (name, count) ∈ costs first ↔ (name, count) ∈ costs second

/-- An unchanged captured record preserves every observation. -/
theorem same_refl (name : Reference) (value : Value Symbol Guard) : Same name value value := ⟨Iff.rfl, fun _ => Iff.rfl⟩

/-- Distinct supplied references agree on all occurrences of another name. -/
theorem reference_same (name first second : Reference) (left : name ≠ first) (right : name ≠ second) :
    Same name (.reference first : Value Symbol Guard) (.reference second) := by
  constructor
  · simp [Value.referenceOf]
  · intro count
    simp [costs, left, right]

/-- Ordered inputs have the same length and related values at each position. -/
inductive Paired {First Second : Type} (relation : First → Second → Prop) : List First → List Second → Prop
  | nil : Paired relation [] []
  | cons {a b first second} : relation a b → Paired relation first second → Paired relation (a :: first) (b :: second)

/-- The same optional list position supplies related values or the same default. -/
theorem getElem?_same (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Same name) first second) (index : Nat) :
    Same name (first[index]?.getD .empty) (second[index]?.getD .empty) := by
  induction paired generalizing index with
  | nil => exact same_refl name .empty
  | cons related paired ih =>
      cases index with
      | zero => exact related
      | succ index => exact ih index

/-- Ordered paired inputs transport a universal property. -/
theorem all_iff {First Second : Type} {relation : First → Second → Prop} {first : List First} {second : List Second}
    (paired : Paired relation first second) (left : First → Prop) (right : Second → Prop)
    (equivalent : ∀ a b, relation a b → (left a ↔ right b)) :
    (∀ value ∈ first, left value) ↔ ∀ value ∈ second, right value := by
  induction paired with
  | nil => simp
  | @cons a b first second related paired ih =>
      simpa using and_congr (equivalent a b related) ih

/-- Ordered paired inputs transport an occurrence witness. -/
theorem exists_iff {First Second : Type} {relation : First → Second → Prop} {first : List First} {second : List Second}
    (paired : Paired relation first second) (left : First → Prop) (right : Second → Prop)
    (equivalent : ∀ a b, relation a b → (left a ↔ right b)) :
    (∃ value ∈ first, left value) ↔ ∃ value ∈ second, right value := by
  induction paired with
  | nil => simp
  | @cons a b first second related paired ih =>
      simpa using or_congr (equivalent a b related) ih

/-- Paired child records agree on whether an edge has an empty child. -/
theorem any_empty_iff (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Same name) first second) :
    first.any (fun child => child.referenceOf == .empty) = true ↔
      second.any (fun child => child.referenceOf == .empty) = true := by
  simpa only [List.any_eq_true, beq_iff_eq] using
    exists_iff paired (fun value => value.referenceOf = .empty) (fun value => value.referenceOf = .empty)
      (fun _ _ related => related.1)

/-- Paired child records agree on whether an edge survives source empty-child removal. -/
theorem live_iff (name : Reference) (first second : List (Value Symbol Guard))
    (paired : Paired (Same name) first second) :
    first.any (fun child => child.referenceOf == .empty) = false ↔
      second.any (fun child => child.referenceOf == .empty) = false := by
  simpa only [List.any_eq_false, beq_iff_eq] using
    all_iff paired (fun value => value.referenceOf ≠ .empty) (fun value => value.referenceOf ≠ .empty)
      (fun _ _ related => not_congr related.1)

/-- Actual canonical ordinary construction preserves the complete observation for paired edge children. -/
theorem makeNode_same [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (first second : List (EdgeValue Symbol Guard)) (left right : State Symbol Guard)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right) (leftLinked : Linked left) (rightLinked : Linked right)
    (leftResident : ∀ edge ∈ first, EdgeResident left edge) (rightResident : ∀ edge ∈ second, EdgeResident right edge)
    (paired : Paired (fun a b => Paired (Same name) a.children b.children) first second) :
    Same name (run (makeNode first) left).1 (run (makeNode second) right).1 := by
  constructor
  · rw [makeNode_empty_iff first left leftCoherent leftLinked leftResident,
      makeNode_empty_iff second right rightCoherent rightLinked rightResident]
    exact all_iff paired _ _ (fun a b related => any_empty_iff name a.children b.children related)
  · intro count
    rw [makeNode_cost_iff first left leftCoherent leftLinked leftResident,
      makeNode_cost_iff second right rightCoherent rightLinked rightResident]
    apply exists_iff paired
    intro a b related
    exact and_congr (live_iff name a.children b.children related)
      (exists_iff related _ _ (fun a b same => same.2 count))

/-- Actual source union construction preserves the observation through every normalization branch. -/
theorem makeUnion_same [DecidableEq (EdgeKey Symbol Guard)] (name : Reference)
    (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right) (leftCached : Cached left) (rightCached : Cached right)
    (leftLinked : Linked left) (rightLinked : Linked right) (leftLive : Live left) (rightLive : Live right)
    (leftProper : NonemptyRecords left) (rightProper : NonemptyRecords right)
    (leftAvailable : ∀ value ∈ first, Available left value) (rightAvailable : ∀ value ∈ second, Available right value)
    (paired : Paired (Same name) first second) :
    Same name (run (makeUnion first) left).1 (run (makeUnion second) right).1 := by
  constructor
  · rw [makeUnion_empty_iff first left leftCoherent leftLinked leftLive leftProper leftAvailable,
      makeUnion_empty_iff second right rightCoherent rightLinked rightLive rightProper rightAvailable]
    exact all_iff paired _ _ (fun _ _ related => related.1)
  · intro count
    rw [makeUnion_cost_iff first left leftCoherent leftCached leftLinked leftLive leftAvailable,
      makeUnion_cost_iff second right rightCoherent rightCached rightLinked rightLive rightAvailable]
    exact exists_iff paired _ _ (fun _ _ related => related.2 count)

end MicroCFTA.InternedOccurrenceObservations
