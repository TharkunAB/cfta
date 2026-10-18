import MicroCFTA.SourceCurrentReaderObservations
import MicroCFTA.SourceCurrentStoredReconstruction
import MicroCFTA.InternedFreshMuUnfoldBudget

/-!
# Actual support for observation readers

Support is closed under epsilon successors and ordered row children.
Each supported unfolding completes without a cache effect. Actual replay
then preserves every supported observation after cache growth.

Initial Ready data also produces a finite preparation. It settles every
closed resident Mu, including new lower-degree records. The final reader
supports all its closed available values. This does not compare that reader
with the original cold reader. Open values can use the generic support law.
-/
namespace MicroCFTA.SourceCurrentObservationReaderSupport
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedFreshMuUnfoldBudget (Settled)
open InternedEdgeResidency (nodeEdges)
open MergedFreshOrdinaryGraph (Origin successors)
open SourceCurrentOpenObservations (Same ReferenceOrigin RowMatch)
open SourceEqualityRequiredCache (Ready Keeps)
open Productivity (Reachable)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Supported values retain their successors and row children and have actual effect-free unfoldings. -/
def WarmSupport (reader : State Symbol Guard) (support : Value Symbol Guard → Prop) : Prop :=
  (∀ value, support value → ∀ next ∈ successors reader value, support next) ∧
  (∀ value, support value → ∀ row ∈ nodeEdges value, ∀ child ∈ row.children, support child) ∧
  ∀ value, support value → Settled reader value

private theorem successors_same (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop)
    (warm : WarmSupport before support) (value : Value Symbol Guard) (included : support value) :
    successors before value = successors after value := by
  obtain ⟨result,actual⟩ := warm.2.2 value included
  have repeated := InternedFreshOrdinaryStoredSubstitution.unfold_replay value before after result before
    valid actual growth
  cases value with
  | empty | reference | node | union => rfl
  | mu => simp only [successors,actual,repeated]

/-- Exact replay retains the same closed support predicate in every later constructor cache. -/
theorem WarmSupport.grows (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support) :
    WarmSupport after support := by
  refine ⟨?_,warm.2.1,?_⟩
  · intro value included next member
    rw [← successors_same before after valid growth support warm value included] at member
    exact warm.1 value included next member
  · intro value included
    exact Settled.grows before after valid growth value (warm.2.2 value included)

private theorem reached_support (reader : State Symbol Guard) (support : Value Symbol Guard → Prop)
    (closed : ∀ value, support value → ∀ next ∈ successors reader value, support next)
    (roots : List (Value Symbol Guard)) (included : ∀ value ∈ roots, support value)
    (value : Value Symbol Guard) (reached : Reachable (successors reader) roots value) : support value := by
  induction reached with
  | seed member => exact included _ member
  | step prior member ih => exact closed _ ih _ member

private theorem reach_transfer (before after : State Symbol Guard) (support : Value Symbol Guard → Prop)
    (closed : ∀ value, support value → ∀ next ∈ successors before value, support next)
    (same : ∀ value, support value → successors before value = successors after value)
    (roots : List (Value Symbol Guard)) (included : ∀ value ∈ roots, support value)
    (value : Value Symbol Guard) (reached : Reachable (successors before) roots value) :
    Reachable (successors after) roots value := by
  induction reached with
  | seed member => exact .seed member
  | @step previous next prior member ih =>
      exact .step ih ((same previous (reached_support before support closed roots included previous prior)) ▸ member)

private theorem reach_iff (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (roots : List (Value Symbol Guard)) (included : ∀ value ∈ roots, support value)
    (value : Value Symbol Guard) :
    Reachable (successors before) roots value ↔ Reachable (successors after) roots value := by
  have later := warm.grows before after valid growth support
  exact ⟨reach_transfer before after support warm.1
      (successors_same before after valid growth support warm) roots included value,
    reach_transfer after before support later.1
      (fun value member => (successors_same before after valid growth support warm value member).symm)
      roots included value⟩

/-- Supported roots expose exactly the same complete rows after actual constructor-cache growth. -/
theorem origin_iff (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (roots : List (Value Symbol Guard)) (included : ∀ value ∈ roots, support value)
    (row : EdgeValue Symbol Guard) : Origin before roots row ↔ Origin after roots row := by
  constructor
  · rintro ⟨value,reached,member⟩
    exact ⟨value,(reach_iff before after valid growth support warm roots included value).mp reached,member⟩
  · rintro ⟨value,reached,member⟩
    exact ⟨value,(reach_iff before after valid growth support warm roots included value).mpr reached,member⟩

/-- Supported roots expose exactly the same bare names after actual constructor-cache growth. -/
theorem reference_iff (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (roots : List (Value Symbol Guard)) (included : ∀ value ∈ roots, support value)
    (name : InternedBinderProtocol.Reference) :
    ReferenceOrigin before roots name ↔ ReferenceOrigin after roots name :=
  reach_iff before after valid growth support warm roots included (.reference name)

private theorem origin_children (reader : State Symbol Guard) (support : Value Symbol Guard → Prop)
    (warm : WarmSupport reader support) (roots : List (Value Symbol Guard))
    (included : ∀ value ∈ roots, support value) (row : EdgeValue Symbol Guard) (origin : Origin reader roots row) :
    ∀ child ∈ row.children, support child := by
  obtain ⟨value,reached,member⟩ := origin
  exact warm.2.1 value (reached_support reader support warm.1 roots included value reached) row member

/-- Every finite comparison of supported roots is equivalent at the two actual readers. -/
theorem same_iff (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (depth : Nat) (first second : List (Value Symbol Guard))
    (firstSupport : ∀ value ∈ first, support value) (secondSupport : ∀ value ∈ second, support value) :
    Same depth before first second ↔ Same depth after first second := by
  induction depth generalizing first second with
  | zero =>
      constructor
      · intro actual name
        exact (reference_iff before after valid growth support warm first firstSupport name).symm.trans
          ((actual name).trans (reference_iff before after valid growth support warm second secondSupport name))
      · intro actual name
        exact (reference_iff before after valid growth support warm first firstSupport name).trans
          ((actual name).trans (reference_iff before after valid growth support warm second secondSupport name).symm)
  | succ depth ih =>
      have forward (rows : List (Value Symbol Guard)) (included : ∀ value ∈ rows, support value)
          (row : EdgeValue Symbol Guard) : Origin before rows row ↔ Origin after rows row :=
        origin_iff before after valid growth support warm rows included row
      have convert (left right : EdgeValue Symbol Guard)
          (leftSupport : ∀ child ∈ left.children, support child)
          (rightSupport : ∀ child ∈ right.children, support child) :
          RowMatch (fun a b => Same depth before [a] [b]) left right ↔
            RowMatch (fun a b => Same depth after [a] [b]) left right := by
        constructor
        · rintro ⟨symbol,guard,children⟩
          refine ⟨symbol,guard,?_⟩
          exact All₂.imp (fun a b related => (ih [a] [b]
            (by intro value member; exact List.mem_singleton.mp member ▸ leftSupport a (by assumption))
            (by intro value member; exact List.mem_singleton.mp member ▸ rightSupport b (by assumption))).mp related) children
        · rintro ⟨symbol,guard,children⟩
          refine ⟨symbol,guard,?_⟩
          exact All₂.imp (fun a b related => (ih [a] [b]
            (by intro value member; exact List.mem_singleton.mp member ▸ leftSupport a (by assumption))
            (by intro value member; exact List.mem_singleton.mp member ▸ rightSupport b (by assumption))).mpr related) children
      constructor
      · rintro ⟨references,rows,others⟩
        refine ⟨?_,?_,?_⟩
        · intro name
          exact (reference_iff before after valid growth support warm first firstSupport name).symm.trans
            ((references name).trans (reference_iff before after valid growth support warm second secondSupport name))
        · intro row found
          have original := (forward first firstSupport row).mpr found
          obtain ⟨other,otherFound,matching⟩ := rows row original
          exact ⟨other,(forward second secondSupport other).mp otherFound,
            (convert row other (origin_children before support warm first firstSupport row original)
              (origin_children before support warm second secondSupport other otherFound)).mp matching⟩
        · intro row found
          have original := (forward second secondSupport row).mpr found
          obtain ⟨other,otherFound,matching⟩ := others row original
          exact ⟨other,(forward first firstSupport other).mp otherFound,
            (convert row other (origin_children before support warm second secondSupport row original)
              (origin_children before support warm first firstSupport other otherFound)).mp matching⟩
      · rintro ⟨references,rows,others⟩
        refine ⟨?_,?_,?_⟩
        · intro name
          exact (reference_iff before after valid growth support warm first firstSupport name).trans
            ((references name).trans (reference_iff before after valid growth support warm second secondSupport name).symm)
        · intro row found
          obtain ⟨other,otherFound,matching⟩ := rows row ((forward first firstSupport row).mp found)
          have original := (forward second secondSupport other).mpr otherFound
          exact ⟨other,original,(convert row other
            (origin_children before support warm first firstSupport row found)
            (origin_children before support warm second secondSupport other original)).mpr matching⟩
        · intro row found
          obtain ⟨other,otherFound,matching⟩ := others row ((forward second secondSupport row).mp found)
          have original := (forward first firstSupport other).mpr otherFound
          exact ⟨other,original,(convert row other
            (origin_children before support warm second secondSupport row found)
            (origin_children before support warm first firstSupport other original)).mpr matching⟩

/-- Physical Empty agreement and all finite supported comparisons remain valid at the later reader. -/
theorem related (before after : State Symbol Guard) (valid : Valid before)
    (growth : Grows before after) (support : Value Symbol Guard → Prop) (warm : WarmSupport before support)
    (first second : Value Symbol Guard) (firstSupport : support first) (secondSupport : support second)
    (actual : SourceCurrentReaderObservations.Related before first second) :
    SourceCurrentReaderObservations.Related after first second := by
  refine ⟨actual.1,?_⟩
  intro depth
  exact (same_iff before after valid growth support warm depth [first] [second]
    (by intro value member; exact List.mem_singleton.mp member ▸ firstSupport)
    (by intro value member; exact List.mem_singleton.mp member ▸ secondSupport)).mp (actual.2 depth)

/-- A finite preparation records only actual successful unfoldings of closed available values. -/
inductive Preparation : State Symbol Guard → State Symbol Guard → Prop where
  /-- An empty preparation keeps the initial reader. -/
  | refl (state) : Preparation state state
  /-- One literal closed unfolding precedes the remaining finite preparation. -/
  | step {before middle after} (value result : Value Symbol Guard)
      (available : Available before value) (closed : value.free = [])
      (actual : unfold value before = .done result middle)
      (tail : Preparation middle after) : Preparation before after

end MicroCFTA.SourceCurrentObservationReaderSupport
