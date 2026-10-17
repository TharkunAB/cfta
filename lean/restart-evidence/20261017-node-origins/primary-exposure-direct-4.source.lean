import MicroCFTA.SourceCurrentPrimaryReplay
import MicroCFTA.SourceCurrentRequiredExposureSafe
import MicroCFTA.SourceCurrentRequiredSupport
import MicroCFTA.SourceCurrentRequiredFiniteExposure
import MicroCFTA.SourceEqualitySelectedRequired

/-!
# Primary certificates for structural Required inputs

False primary certificates retain their recursive acceptance facts.
Each original path replays at the completed heap. The secondary gate
does not supply this stronger certificate for a closed constrained Mu.
-/
namespace MicroCFTA.SourceCurrentRequiredPrimaryExposure
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open EndpointStatefulGateTrace
open SourceCurrentRequiredRowOrigins (ExposureSafe)
open SourceCurrentRequiredSupport (Tip)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
noncomputable local instance : DecidableEq (EdgeKey Symbol Guard) := by classical exact inferInstance

/-- Every row in a false primary scan retains its child certificate at later heaps. -/
theorem false_edges_members
    (index : Nat) (path : EqualityNormalize.Path) (edges : List (EdgeValue Symbol Guard))
    (before after : Heap) (trace : EdgesTrace source reaches index path edges before false after)
    (semantic : SemanticReady before) (available : Values before (edges.flatMap EdgeValue.children))
    (target : Heap) (retained : Grows after target) :
    ∀ edge ∈ edges, ChildTrace source reaches edge.children index path target false target := by
  induction edges generalizing before with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := SourceCurrentPrimaryReplay.child_replay source reaches _ _ _ _ _ _ head semantic
            (fun value member => available value (by simp [member]))
          have tailAvailable : Values _ (rest.flatMap EdgeValue.children) :=
            fun value member => firstEffects.2.1.available value (available value (by simp [member]))
          have tailEffects := SourceCurrentPrimaryReplay.edges_replay source reaches _ _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable edge member

/-- An existing selected slot retains the exact primary node certificate. -/
theorem false_selected
    {values : List (Value Symbol Guard)} {index : Nat} {path : EqualityNormalize.Path}
    {value : Value Symbol Guard} {before after : Heap}
    (trace : ChildTrace source reaches values index path before false after)
    (found : values[index]? = some value) : NodeTrace source reaches path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      exact node

/-- Every original path in a false class retains its primary certificate at later heaps. -/
theorem false_class_paths
    (values : List (Value Symbol Guard)) (paths : Class) (before after : Heap)
    (trace : ClassTrace source reaches values paths before false after)
    (semantic : SemanticReady before) (available : Values before values)
    (target : Heap) (retained : Grows after target) :
    ∀ path ∈ paths, PathTrace source reaches values path target false target := by
  induction paths generalizing before with
  | nil => intro path member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := SourceCurrentPrimaryReplay.path_replay source reaches _ _ _ _ _ head semantic available
          have tailAvailable := fun value member => firstEffects.2.1.available value (available value member)
          have tailEffects := SourceCurrentPrimaryReplay.class_replay source reaches _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro path member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable path member

/-- False primary tips derive the structural requirement domain from the original records. -/
theorem node (needed : Needed) (state : Heap) (semantic : SemanticReady state)
    (normal : SourceCurrentRequiredUnionNormal.UnionNormal state)
    (value : Value Symbol Guard) (available : Available state value)
    (valid : SourceEqualityNeeded.Valid needed)
    (nonnegative : SourceEqualityNeededNonnegative.Nonnegative needed)
    (traces : ∀ path, Tip needed path → NodeTrace source reaches path value state false state) :
    ExposureSafe needed value := by
  cases needed with
  | node entries =>
      by_cases terminal : entries = []
      · subst entries
        exact .identity value
      cases value with
      | empty => exact .empty _
      | reference name =>
          obtain ⟨path, tip⟩ := SourceCurrentRequiredSupport.tip_exists (.node entries) valid nonnegative
          cases traces path tip
      | union entry members level free =>
          obtain ⟨path, tip⟩ := SourceCurrentRequiredSupport.tip_exists (.node entries) valid nonnegative
          cases traces path tip
      | mu entry body depth ordinary =>
          obtain ⟨path, tip⟩ := SourceCurrentRequiredSupport.tip_exists (.node entries) valid nonnegative
          cases traces path tip with
          | closed plain _ => exact .accepted _ _ plain
          | unfold plain _ _ _ => exact .accepted _ _ plain
      | node entry rows level free =>
          by_cases fast : (level == 0 && free.isEmpty) = true
          · exact SourceCurrentRequiredFiniteExposure.finite_exposure (.node entries) state semantic normal
              (.node entry rows level free) available
              (by simpa only [Value.depth, beq_iff_eq] using (Bool.and_eq_true_iff.mp fast).1)
              (List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp fast).2)
          · apply ExposureSafe.ordinary
            intro row member index childNeeded found child selected
            have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
            have childValid := valid.2 _ _ present
            have childNonnegative := (nonnegative _ _ present).2
            have childAvailable := available.children child
              (List.mem_flatMap.mpr ⟨row, member, List.mem_of_getElem? selected⟩)
            apply node childNeeded state semantic normal child childAvailable childValid childNonnegative
            intro path tip
            have original := traces (index :: path) (.child found tip)
            have scanned : EdgesTrace source reaches index path rows state false state := by
              cases original with
              | finite impossible => exact False.elim (fast impossible)
              | branches _ trace => exact trace
            exact false_selected
              (false_edges_members index path rows state state scanned semantic
                (fun value member => available.children value member) state (grows_refl state) row member) selected
termination_by sizeOf needed
decreasing_by
  have smaller := List.sizeOf_lt_of_mem present
  simp only [Prod.mk.sizeOf_spec, Needed.node.sizeOf_spec] at *
  omega

/-- Original primary paths supply the exact compiled forest domain. -/
theorem of_paths (paths : Class) (values : List (Value Symbol Guard)) (state : Heap)
    (semantic : SemanticReady state) (normal : SourceCurrentRequiredUnionNormal.UnionNormal state)
    (available : Values state values)
    (traces : ∀ path ∈ paths, PathTrace source reaches values path state false state) :
    ∀ entries, build (paths.map (List.map Int.ofNat)) = .node entries →
      ∀ index childNeeded, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some childNeeded →
      ∀ value, values[index]? = some value → ExposureSafe childNeeded value := by
  intro entries compiled index childNeeded found value selected
  have valid := build_valid (paths.map (List.map Int.ofNat))
  have nonnegative := SourceEqualityNeededNonnegative.build_nonnegative (paths.map (List.map Int.ofNat))
    (by
      intro path member key included
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
      obtain ⟨natural, _, rfl⟩ := List.mem_map.mp included
      exact Int.ofNat_nonneg natural)
  rw [compiled] at valid nonnegative
  have present := SourceEqualityNeededMap.lookup_mem _ _ _ found
  apply node childNeeded state semantic normal value (available value (List.mem_of_getElem? selected))
    (valid.2 _ _ present) (nonnegative _ _ present).2
  intro path tip
  have whole : Tip (build (paths.map (List.map Int.ofNat))) (index :: path) := by
    rw [compiled]
    exact .child found tip
  obtain ⟨original, member, same⟩ := List.mem_map.mp (whole.build_member (by simp))
  have equal : original = index :: path := by
    simpa only [List.map_map, Function.comp_def, Int.toNat_natCast, List.map_id] using
      congrArg (List.map Int.toNat) same
  subst original
  cases traces (index :: path) member with
  | child traced => exact false_selected traced selected

/-- Selected false primary classes derive the structural domain for their canonical path union. -/
theorem selected_domain (values : List (Value Symbol Guard)) (selected : Constraints) (state : Heap)
    (semantic : SemanticReady state) (normal : SourceCurrentRequiredUnionNormal.UnionNormal state)
    (available : Values state values)
    (primary : ∀ paths ∈ selected, ClassTrace source reaches values paths state false state) :
    ∀ entries, build (SourceEqualitySelectedRequired.paths selected) = .node entries →
      ∀ index childNeeded, SourceEqualityNeededMap.lookup (Int.ofNat index) entries = some childNeeded →
      ∀ value, values[index]? = some value → ExposureSafe childNeeded value := by
  apply of_paths (canonicalClass selected.flatten) values state semantic normal available
  intro path member
  obtain ⟨paths, included, present⟩ := List.mem_flatten.mp ((mem_canonicalClass _ _).mp member)
  exact false_class_paths values paths state state (primary paths included) semantic available
    state (grows_refl state) path present

end MicroCFTA.SourceCurrentRequiredPrimaryExposure
