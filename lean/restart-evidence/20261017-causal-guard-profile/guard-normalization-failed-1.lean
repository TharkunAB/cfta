import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.InternedUnionFilterFusion

/-!
# Exact guard profiles through actual source normalization

Ordinary construction keeps only rows without empty children. Union work
retains the guard profiles of its original available members. Canonical
ordering, duplicate removal, and earlier cache readback retain complete
resident payloads. These equations inspect literal guards, not languages.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardNormalization
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedNestedFacts InternedLiveEdges InternedFreshProbeKeys
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCap (Cap Edge)
namespace G := SourceCurrentConstrainedCapGuardDepth
variable {Symbol Guard : Type}

/-- All finite upper-bound observations determine an optional natural number. -/
theorem within_ext (first second : Option Nat)
    (same : ∀ depth, G.Within depth first ↔ G.Within depth second) : first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some depth => exact False.elim ((same depth).mpr (Nat.le_refl _))
  | some depth =>
      cases second with
      | none => exact False.elim ((same depth).mp (Nat.le_refl _))
      | some other =>
          exact congrArg some (Nat.le_antisymm ((same other).mpr (Nat.le_refl _)) ((same depth).mp (Nat.le_refl _)))

/-- A zero contribution leaves either finite or missing profile unchanged. -/
theorem join_zero (value : Option Nat) : G.join value (some 0) = value := by
  cases value <;> simp [G.join]

/-- Canonical edge ordering retains the exact row guard profile of resident rows. -/
theorem canonical_rows (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state)
    (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    G.rows annotation (canonicalEdges edges) = G.rows annotation edges := by
  apply within_ext
  intro depth
  rw [G.rows_iff_caps, G.rows_iff_caps]
  exact ⟨fun bounded edge member => bounded edge (canonicalEdges_retains state coherent edges edge resident member),
    fun bounded edge member => bounded edge (canonicalEdges_member edges edge member)⟩

private theorem makeNode_canonical_profile [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    G.profile annotation (run (makeNode edges) state).1 = G.rows annotation (canonicalEdges (surviving edges)) := by
  have selected : ∀ edge ∈ canonicalEdges (surviving edges), EdgeResident state edge :=
    fun edge member => resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · rename_i same
    simp only [run, G.profile, same, G.rows]
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state coherent linked
      (by simpa only [same] using selected)
    simp only [run, readback, identifyNode, G.profile, same]

/-- Actual ordinary readback has exactly the guard profile of its surviving original rows. -/
theorem makeNode_profile [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    G.profile annotation (run (makeNode edges) state).1 = G.rows annotation (surviving edges) := by
  rw [makeNode_canonical_profile annotation edges state coherent linked resident]
  exact canonical_rows annotation _ state coherent (fun edge member => resident edge (List.mem_filter.mp member).1)

/-- A returned ordinary cap reflects to every surviving original row. -/
theorem makeNode_cap_iff [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (linked : Linked state) (resident : ∀ edge ∈ edges, EdgeResident state edge) :
    Cap annotation depth (run (makeNode edges) state).1 ↔ ∀ edge ∈ surviving edges, Edge annotation depth edge := by
  rw [← G.within_iff_cap, makeNode_profile annotation edges state coherent linked resident, G.rows_iff_caps]

/-- Literal edge readback retains its guard cost and exact ordered child profile. -/
theorem makeEdge_profile [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (coherent : Coherent state) (cached : Cached state) (available : ∀ value ∈ values, Available state value) :
    G.rows annotation [(run (makeEdge symbol guard values) state).1] =
      G.join (some (G.guardCost annotation guard)) (G.raise (G.children annotation values)) := by
  cases result : (run (makeEdge symbol guard values) state).1 with
  | mk entry children =>
      have key := InternedOrdinaryAbsenceReplay.makeEdge_key symbol guard values state coherent
      have exactChildren := InternedShallowValues.makeEdge_children symbol guard values state coherent cached available
      rw [result] at key exactChildren
      change entry.key = _ at key
      change children = values at exactChildren
      simp only [G.rows, key, exactChildren, join_zero]

/-- A root value has a cap exactly when all of its flattened union members have that cap. -/
theorem union_members_cap_iff (annotation : Guard → Prop) (depth : Nat) (value : Value Symbol Guard) :
    Cap annotation depth value ↔ ∀ member ∈ unionMembers value, Cap annotation depth member := by
  constructor
  · intro bounded member included
    exact SourceCurrentConstrainedCap.union_member bounded member included
  · intro bounded
    cases value with
    | empty => exact .plain depth .empty
    | reference | node | mu => exact bounded _ List.mem_cons_self
    | union entry members level free => exact .union depth entry members level free bounded

/-- Every original cap is reflected by actual union normalization in a live source heap. -/
theorem makeUnion_cap_iff [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop) (depth : Nat)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (live : Live state) (available : ∀ value ∈ values, Available state value) :
    Cap annotation depth (run (makeUnion values) state).1 ↔ ∀ value ∈ values, Cap annotation depth value := by
  constructor
  · intro bounded value included
    apply (union_members_cap_iff annotation depth value).mpr
    intro member inside
    have flattened : member ∈ values.flatMap unionMembers := List.mem_flatMap.mpr ⟨value, included, inside⟩
    have allAvailable : ∀ value ∈ values.flatMap unionMembers, Available state value := by
      intro value present
      obtain ⟨source, included, inside⟩ := List.mem_flatMap.mp present
      exact unionMembers_available source (available source included) value inside
    have retained := InternedUnionRetention.distinctNodes_retains state facts.coherent _
      (fun value present => (allAvailable value present).resident) member flattened
    cases selected : distinctNodes (values.flatMap unionMembers) with
    | nil => simp only [selected, List.not_mem_nil] at retained
    | cons first rest =>
        cases rest with
        | nil =>
            have same : member = first := List.mem_singleton.mp (by simpa only [selected] using retained)
            simpa only [makeUnion, selected, run, ← same] using bounded
        | cons second tail =>
            have memberSelected : member ∈ first :: second :: tail := by simpa only [selected] using retained
            cases ordinary : ordinaryEdges (first :: second :: tail) with
            | none =>
                obtain ⟨entry, returned⟩ := InternedUnionFilterFusion.union_readback values first second tail state facts available selected ordinary
                rw [returned] at bounded
                exact SourceCurrentConstrainedCap.union_member bounded member memberSelected
            | some edges =>
                have membersAvailable : ∀ value ∈ first :: second :: tail, Available state value := by
                  simpa only [selected] using InternedUnionFilterFusion.selected_available values state available
                have resident := ordinaryEdges_resident _ edges state facts.linked
                  (fun value present => (membersAvailable value present).resident) ordinary
                have nodeCap : Cap annotation depth (run (makeNode edges) state).1 := by
                  simpa only [makeUnion, selected, ordinary] using bounded
                have rows := (makeNode_cap_iff annotation depth edges state facts.coherent facts.linked resident).mp nodeCap
                obtain ⟨entry, own, level, free, same, kept⟩ := InternedUnionDescendants.ordinaryEdges_contains _ edges ordinary member memberSelected
                have memberLive := resident_live state live member (allAvailable member flattened).resident
                subst member
                apply SourceCurrentConstrainedCap.ordinary annotation depth entry own level free
                intro edge present
                exact rows edge (by simp only [surviving, List.mem_filter, Bool.not_eq_true]; exact ⟨kept edge present, memberLive edge present⟩)
  · exact SourceCurrentConstrainedCap.makeUnion annotation depth values state facts available

/-- Actual union readback has exactly the maximum guard profile of its original operands. -/
theorem makeUnion_profile [DecidableEq (EdgeKey Symbol Guard)] (annotation : Guard → Prop)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (facts : Facts state)
    (live : Live state) (available : ∀ value ∈ values, Available state value) :
    G.profile annotation (run (makeUnion values) state).1 = G.children annotation values := by
  apply within_ext
  intro depth
  rw [G.within_iff_cap, G.children_iff_caps]
  exact makeUnion_cap_iff annotation depth values state facts live available

end MicroCFTA.SourceCurrentConstrainedCapGuardNormalization
