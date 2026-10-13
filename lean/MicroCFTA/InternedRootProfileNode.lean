import MicroCFTA.InternedRootProfileLists
import MicroCFTA.InternedProfileSemantics
import MicroCFTA.InternedEmptyNormalization

/-!
# Root profiles of actual ordinary source construction

A pure empty profile denotes exactly EmptyNode for available normalized
records. An ordinary constructor is opaque exactly when one requested
edge has no empty child. Complete cache readback preserves this decision.
-/
namespace MicroCFTA.InternedRootProfileNode
open Cache InternedConstructorTemplates InternedRootProfile InternedRecordCoherence InternedProbeProvenance
open InternedNonemptyRecords InternedEmptyNormalization InternedEdgeResidency InternedNestedFacts InternedNestedProvenance
open InternedBinderProtocol (Reference)

/-- Combining root profiles is empty exactly when each original operand profile is empty. -/
theorem many_empty_iff (values : List (Value Symbol Guard)) :
    many values = some [] ↔ ∀ value ∈ values, profile value = some [] := by
  induction values with
  | nil => simp [many]
  | cons first rest ih =>
      cases firstProfile : profile first <;> cases restProfile : many rest <;> simp_all [many, combine]

/-- A pure empty root profile is exactly the actual EmptyNode record. -/
theorem profile_empty_iff (value : Value Symbol Guard) (state : State Symbol Guard)
    (proper : NonemptyRecords state) (available : Available state value) :
    profile value = some [] ↔ value = .empty := by
  cases value with
  | empty | reference | node | mu => simp [profile]
  | union entry members depth free =>
      constructor
      · intro empty
        have all := many_empty_iff members |>.mp (by simpa only [profile] using empty)
        have shape := resident_nonempty state proper (.union entry members depth free) available.resident
        obtain ⟨child, included, nonempty⟩ := union_has_nonempty entry members depth free shape
        have same := (profile_empty_iff child state proper (available.children child included)).mp (all child included)
        exact False.elim (nonempty (by simp [same, Value.referenceOf]))
      · intro impossible; cases impossible
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem included
  simp_wf
  simp_all
  omega

/-- The pure interpreter's empty decision agrees with actual source identity. -/
theorem isEmpty_profile (value : Value Symbol Guard) (state : State Symbol Guard)
    (proper : NonemptyRecords state) (available : Available state value) :
    InternedProfileSemantics.isEmpty (profile value) = (value.referenceOf == .empty) := by
  apply Bool.eq_iff_iff.mpr
  have abstract : InternedProfileSemantics.isEmpty (profile value) = true ↔ profile value = some [] := by
    cases profile value with
    | none => simp [InternedProfileSemantics.isEmpty]
    | some names => cases names <;> simp [InternedProfileSemantics.isEmpty]
  rw [abstract, profile_empty_iff value state proper available, beq_iff_eq, reference_empty]

/-- Actual node readback is opaque when nonempty and has the pure empty profile otherwise. -/
theorem makeNode_shape [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges) :
    profile (run (makeNode edges) state).1 =
      if (run (makeNode edges) state).1.referenceOf == .empty then some [] else none := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  cases same : canonicalEdges (surviving edges) with
  | nil => simp [makeNode, same, run, profile, Value.referenceOf]
  | cons first rest =>
      obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
        (by simpa only [same] using selected)
      simp only [makeNode, same, run]
      rw [readback]
      simp [identifyNode, profile, Value.referenceOf]

/-- The actual ordinary profile is determined by the original source empty-child decisions. -/
theorem makeNode_profile [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges) :
    profile (run (makeNode edges) state).1 =
      if edges.all (fun edge => edge.children.any (fun child => child.referenceOf == .empty)) then some [] else none := by
  rw [makeNode_shape edges state facts resident]
  have decisions : ((run (makeNode edges) state).1.referenceOf == .empty) =
      edges.all (fun edge => edge.children.any (fun child => child.referenceOf == .empty)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.all_eq_true]
    exact makeNode_empty_iff edges state facts.coherent facts.linked resident
  rw [decisions]

/-- Node profiles use exactly the pure interpreter's live-edge test on actual child profiles. -/
theorem makeNode_profile_children [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (proper : NonemptyRecords state) (resident : Edges state edges) :
    profile (run (makeNode edges) state).1 =
      if edges.any (fun edge => edge.children.all (fun child => !InternedProfileSemantics.isEmpty (profile child)))
      then none else some [] := by
  rw [makeNode_profile edges state facts resident]
  have children : ∀ edge ∈ edges,
      edge.children.all (fun child => !InternedProfileSemantics.isEmpty (profile child)) =
        !(edge.children.any (fun child => child.referenceOf == .empty)) := by
    intro edge member
    rw [List.not_any_eq_all_not]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    apply forall_congr'
    intro child
    apply forall_congr'
    intro included
    rw [isEmpty_profile child state proper (facts.cached.edges edge.entry.key edge (resident edge member) child included)]
  have same : edges.any (fun edge => edge.children.all (fun child => !InternedProfileSemantics.isEmpty (profile child))) =
      !(edges.all (fun edge => edge.children.any (fun child => child.referenceOf == .empty))) := by
    rw [List.not_all_eq_any_not]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    exact exists_congr fun edge => and_congr_right fun member => by rw [children edge member]
  rw [same]
  cases edges.all (fun edge => edge.children.any (fun child => child.referenceOf == .empty)) <;> rfl

end MicroCFTA.InternedRootProfileNode
