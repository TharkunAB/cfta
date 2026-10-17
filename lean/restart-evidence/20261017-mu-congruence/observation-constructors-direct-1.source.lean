import MicroCFTA.SourceCurrentOpenObservations
import MicroCFTA.MergedFreshOrdinaryUnionOrigins
import MicroCFTA.SourceEqualityRequiredCache

/-!
# Actual constructors in one observation view

Seed lists compose ordered singleton observations. Ordinary rows retain
full guards and ordered child observations. Actual node normalization needs
matching surviving rows. Open observations alone do not imply this premise.
Actual union normalization retains both reference and complete row origins.
-/
namespace MicroCFTA.SourceCurrentOpenObservationConstructors
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedLiveEdges
open InternedUnionRetention InternedUnionFilterFusion
open MergedFreshOrdinaryGraph SourceCurrentOpenObservations
open Productivity Language

private theorem pair_mem {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    {first second : List (Value Symbol Guard)} (matched : All₂ relation first second)
    (value : Value Symbol Guard) (member : value ∈ first) :
    ∃ other ∈ second, relation value other := by
  induction matched with
  | nil => cases member
  | cons pair rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, pair⟩
      · obtain ⟨other, present, related⟩ := ih later
        exact ⟨other, List.mem_cons_of_mem _ present, related⟩

private theorem pair_reverse {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    {first second : List (Value Symbol Guard)} (matched : All₂ relation first second) :
    All₂ (fun right left => relation left right) second first := by
  induction matched with
  | nil => exact .nil
  | cons pair rest ih => exact .cons pair ih

/-- Ordered singleton observations compose into observations of the exact seed lists. -/
theorem seeds [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (first second : List (Value Symbol Guard))
    (matched : All₂ (fun left right => Same depth view [left] [right]) first second) :
    Same depth view first second := by
  have references (name : InternedBinderProtocol.Reference) :
      ReferenceOrigin view first name ↔ ReferenceOrigin view second name := by
    rw [reference_seeds, reference_seeds]
    constructor
    · rintro ⟨value, present, origin⟩
      obtain ⟨other, included, related⟩ := pair_mem matched value present
      have same := related
      cases depth with
      | zero => exact ⟨other, included, (same name).mp origin⟩
      | succ depth => exact ⟨other, included, (same.1 name).mp origin⟩
    · rintro ⟨value, present, origin⟩
      obtain ⟨other, included, related⟩ := pair_mem (pair_reverse matched) value present
      have same := related
      cases depth with
      | zero => exact ⟨other, included, (same name).mpr origin⟩
      | succ depth => exact ⟨other, included, (same.1 name).mpr origin⟩
  cases depth with
  | zero => exact references
  | succ depth =>
      refine ⟨references, ?_, ?_⟩
      · intro row origin
        obtain ⟨value, present, actual⟩ := (origin_seeds view first row).mp origin
        obtain ⟨other, included, related⟩ := pair_mem matched value present
        obtain ⟨output, result, fields⟩ := related.2.1 row actual
        exact ⟨output, (origin_seeds view second output).mpr ⟨other, included, result⟩, fields⟩
      · intro row origin
        obtain ⟨value, present, actual⟩ := (origin_seeds view second row).mp origin
        obtain ⟨other, included, related⟩ := pair_mem (pair_reverse matched) value present
        obtain ⟨output, result, fields⟩ := related.2.2 row actual
        exact ⟨output, (origin_seeds view first output).mpr ⟨other, included, result⟩, fields⟩

private theorem no_reference [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (value : Value Symbol Guard) (ordinary : SourceEqualityRequiredCache.Ordinary value)
    (name : InternedBinderProtocol.Reference) : ¬ ReferenceOrigin view [value] name := by
  have different : ∀ name, value ≠ .reference name := by
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary]
  have terminal : successors view value = [] := by
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary, successors]
  rw [reference_expand view value different name, terminal, reference_seeds]
  rintro ⟨_, impossible, _⟩
  cases impossible

/-- Literal ordinary rows match by occurrence and keep exact guards and ordered children. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (firstEntry secondEntry : Interned InternedBinderProtocol.NodeKey)
    (first second : List (EdgeValue Symbol Guard)) (firstLevel secondLevel : Nat)
    (firstFree secondFree : List InternedBinderProtocol.Reference)
    (forward : ∀ row ∈ first, ∃ other ∈ second, RowMatch (fun left right => Same depth view [left] [right]) row other)
    (backward : ∀ row ∈ second, ∃ other ∈ first, RowMatch (fun left right => Same depth view [left] [right]) row other) :
    Same (depth + 1) view [.node firstEntry first firstLevel firstFree] [.node secondEntry second secondLevel secondFree] := by
  refine ⟨fun name => iff_of_false (no_reference view _ trivial name) (no_reference view _ trivial name), ?_, ?_⟩
  · intro row origin
    obtain ⟨other, present, fields⟩ := forward row ((origin_node view _ _ _ _ row).mp origin)
    exact ⟨other, (origin_node view _ _ _ _ other).mpr present, fields⟩
  · intro row origin
    obtain ⟨other, present, fields⟩ := backward row ((origin_node view _ _ _ _ row).mp origin)
    exact ⟨other, (origin_node view _ _ _ _ other).mpr present, fields⟩

private theorem node_rows [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard)
    (facts : Facts state) (rows : List (EdgeValue Symbol Guard)) (resident : Edges state rows)
    (row : EdgeValue Symbol Guard) :
    Origin view [(run (makeNode rows) state).1] row ↔ row ∈ surviving rows := by
  have ordinary := SourceEqualityRequiredCache.node_ordinary rows state facts resident
  have terminal : successors view (run (makeNode rows) state).1 = [] := by
    generalize selected : (run (makeNode rows) state).1 = value at ordinary ⊢
    cases value <;> simp_all [SourceEqualityRequiredCache.Ordinary, successors]
  have exactRows : Origin view [(run (makeNode rows) state).1] row ↔ row ∈ nodeEdges (run (makeNode rows) state).1 :=
    ⟨MergedFreshOrdinaryExposureCoverage.origin_terminal view _ terminal row,
      fun member => ⟨_, .seed List.mem_cons_self, member⟩⟩
  rw [exactRows, EqualityLeafProjectionPhysical.makeNode_edges rows state facts.coherent facts.linked resident]
  exact ⟨canonicalEdges_member _ row,
    EqualityLeafProjectionPhysical.canonicalEdges_retains state facts.coherent _ row
      (fun edge member => resident edge (List.mem_filter.mp member).1)⟩

/-- Actual node calls are congruent when their surviving row occurrences match in one common view. -/
theorem makeNode [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view firstState secondState : State Symbol Guard)
    (first second : List (EdgeValue Symbol Guard)) (firstFacts : Facts firstState) (secondFacts : Facts secondState)
    (firstResident : Edges firstState first) (secondResident : Edges secondState second)
    (forward : ∀ row ∈ surviving first, ∃ other ∈ surviving second,
      RowMatch (fun left right => Same depth view [left] [right]) row other)
    (backward : ∀ row ∈ surviving second, ∃ other ∈ surviving first,
      RowMatch (fun left right => Same depth view [left] [right]) row other) :
    Same (depth + 1) view [(run (InternedConstructorTemplates.makeNode first) firstState).1]
      [(run (InternedConstructorTemplates.makeNode second) secondState).1] := by
  refine ⟨fun name => iff_of_false
    (no_reference view _ (SourceEqualityRequiredCache.node_ordinary first firstState firstFacts firstResident) name)
    (no_reference view _ (SourceEqualityRequiredCache.node_ordinary second secondState secondFacts secondResident) name), ?_, ?_⟩
  · intro row origin
    obtain ⟨other, present, fields⟩ := forward row ((node_rows firstState view firstFacts first firstResident row).mp origin)
    exact ⟨other, (node_rows secondState view secondFacts second secondResident other).mpr present, fields⟩
  · intro row origin
    obtain ⟨other, present, fields⟩ := backward row ((node_rows secondState view secondFacts second secondResident row).mp origin)
    exact ⟨other, (node_rows firstState view firstFacts first firstResident other).mpr present, fields⟩

private theorem flatten_references [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (value : Value Symbol Guard) (name : InternedBinderProtocol.Reference) :
    (∃ member ∈ unionMembers value, ReferenceOrigin view [member] name) ↔ ReferenceOrigin view [value] name := by
  cases value with
  | empty =>
      simp only [unionMembers, List.not_mem_nil, false_and, exists_false]
      exact iff_of_false id (no_reference view _ trivial name)
  | reference | node | mu => simp only [unionMembers, List.mem_singleton, exists_eq_left]
  | union entry members depth free =>
      exact (reference_seeds view members name).symm.trans
        (reference_expand view (.union entry members depth free) (fun _ impossible => by cases impossible) name).symm

private theorem selected_references [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard)
    (facts : Facts state) (values : List (Value Symbol Guard)) (available : Values state values)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view (distinctNodes (values.flatMap unionMembers)) name ↔ ReferenceOrigin view values name := by
  rw [reference_seeds, reference_seeds]
  have flatAvailable : Values state (values.flatMap unionMembers) := by
    intro value member
    obtain ⟨source, present, selected⟩ := List.mem_flatMap.mp member
    exact InternedFreshProbeKeys.unionMembers_available source (available source present) value selected
  constructor
  · rintro ⟨member, present, origin⟩
    obtain ⟨source, original, selected⟩ := List.mem_flatMap.mp (distinctNodes_member _ member present)
    exact ⟨source, original, (flatten_references view source name).mp ⟨member, selected, origin⟩⟩
  · rintro ⟨source, present, origin⟩
    obtain ⟨member, selected, origin⟩ := (flatten_references view source name).mpr origin
    exact ⟨member, distinctNodes_retains state facts.coherent _ (fun value included => (flatAvailable value included).resident)
      member (List.mem_flatMap.mpr ⟨source, present, selected⟩), origin⟩

private theorem ordinary_references [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (values : List (Value Symbol Guard)) (rows : List (EdgeValue Symbol Guard))
    (actual : ordinaryEdges values = some rows) (name : InternedBinderProtocol.Reference) :
    ¬ ReferenceOrigin view values name := by
  rw [reference_seeds]
  rintro ⟨value, member, origin⟩
  obtain ⟨entry, edges, level, free, same, _⟩ := InternedUnionDescendants.ordinaryEdges_contains values rows actual value member
  subst value
  exact no_reference view _ trivial name origin

private theorem union_references [DecidableEq (EdgeKey Symbol Guard)] (state view : State Symbol Guard)
    (facts : Facts state) (values : List (Value Symbol Guard)) (available : Values state values)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin view [(run (InternedConstructorTemplates.makeUnion values) state).1] name ↔ ReferenceOrigin view values name := by
  rw [← selected_references state view facts values available name]
  cases selected : distinctNodes (values.flatMap unionMembers) with
  | nil =>
      simp only [InternedConstructorTemplates.makeUnion, selected, run]
      exact iff_of_false (no_reference view _ trivial name) (by rw [reference_seeds]; rintro ⟨_, h, _⟩; cases h)
  | cons first rest =>
      cases rest with
      | nil => simpa only [InternedConstructorTemplates.makeUnion, selected, run]
      | cons second tail =>
          cases ordinary : ordinaryEdges (first :: second :: tail) with
          | none =>
              obtain ⟨entry, readback⟩ := union_readback values first second tail state facts available selected ordinary
              rw [readback]
              exact reference_expand view _ (fun _ impossible => by cases impossible) name
          | some rows =>
              have inputs : Values state (first :: second :: tail) := by simpa only [selected] using selected_available values state available
              have resident := InternedUnionDescendants.ordinaryEdges_resident _ rows state facts.linked
                (fun value member => (inputs value member).resident) ordinary
              simp only [InternedConstructorTemplates.makeUnion, selected, ordinary]
              exact iff_of_false
                (no_reference view _ (SourceEqualityRequiredCache.node_ordinary rows state facts resident) name)
                (ordinary_references view _ rows ordinary name)

/-- Actual union normalization retains both bare-reference and complete row observations. -/
theorem makeUnion_normalize [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (state view : State Symbol Guard)
    (facts : Facts state) (live : Live state) (values : List (Value Symbol Guard)) (available : Values state values) :
    Same depth view [(run (InternedConstructorTemplates.makeUnion values) state).1] values := by
  apply of_origins depth view _ _ (union_references state view facts values available)
  intro row
  exact (MergedFreshOrdinaryUnionOrigins.union_origins state view facts live values available row).trans
    (origin_seeds view values row).symm

/-- Two actual union calls compose ordered member observations in the same common view. -/
theorem makeUnion [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view firstState secondState : State Symbol Guard)
    (first second : List (Value Symbol Guard)) (firstFacts : Facts firstState) (secondFacts : Facts secondState)
    (firstLive : Live firstState) (secondLive : Live secondState)
    (firstAvailable : Values firstState first) (secondAvailable : Values secondState second)
    (matched : All₂ (fun left right => Same depth view [left] [right]) first second) :
    Same depth view [(run (InternedConstructorTemplates.makeUnion first) firstState).1]
      [(run (InternedConstructorTemplates.makeUnion second) secondState).1] :=
  (makeUnion_normalize depth firstState view firstFacts firstLive first firstAvailable).trans
    ((seeds depth view first second matched).trans
      (makeUnion_normalize depth secondState view secondFacts secondLive second secondAvailable).symm)

end MicroCFTA.SourceCurrentOpenObservationConstructors
