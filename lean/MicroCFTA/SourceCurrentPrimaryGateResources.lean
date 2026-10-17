import MicroCFTA.SourceCurrentMemoMergeNumericControl
import MicroCFTA.SourceCurrentAllocatedProjectionResources
import MicroCFTA.InternedFreshOrdinaryUnfoldRank

/-!
# Shared initial resource forecasts for current class gates

Open Mu prefixes decrease free-occurrence rank at the same path. Structural
mass bounds their initial rank. Ordinary rows recurse at smaller path length
and retain their original count while the heap grows. No input is required
to be closed. The formulas do not assert a completed gate by themselves.
-/
namespace MicroCFTA.SourceCurrentPrimaryGateResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedFreeOccurrenceRank (costs manyCosts edgeCosts rank)
open InternedValueMassHeap (Stored)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentAllocatedReaderControl (g g_mono g_strict)
open HeightOrderControlled (iterate)
export SourceCurrentMemoMergeNumericControl
  (iterate_ge iterate_mono iterate_count_mono iterate_compare iterate_add iterate_succ_right)
variable {Symbol Guard : Type}

mutual
/-- Every actual free occurrence traverses at most the complete payload mass. -/
theorem cost_le_mass (value : Value Symbol Guard) (name count) (member : (name, count) ∈ costs value) :
    count ≤ InternedValueMass.value value := by
  cases value with
  | empty => simp only [costs, List.not_mem_nil] at member
  | reference own =>
      simp only [costs] at member
      have same := List.mem_singleton.mp member; cases same; simp only [InternedValueMass.value]; omega
  | node entry rows depth free =>
      simp only [costs] at member
      have bound := edge_cost_le_mass rows name count member
      simp only [InternedValueMass.value]; omega
  | union entry members depth free =>
      simp only [costs] at member
      have bound := many_cost_le_mass members name count member
      simp only [InternedValueMass.value]; omega
  | mu entry body depth ordinary =>
      simp only [costs] at member
      obtain ⟨⟨own, prior⟩, selected, same⟩ := List.mem_map.mp member
      have bound := cost_le_mass body own prior (List.mem_filter.mp selected).1
      have equal := congrArg Prod.snd same
      simp only [InternedValueMass.value]; simp only at equal; omega
termination_by sizeOf value

/-- Ordered member payloads bound every retained free-occurrence cost. -/
theorem many_cost_le_mass (values : List (Value Symbol Guard)) (name count)
    (member : (name, count) ∈ manyCosts values) : count ≤ InternedValueMass.values values := by
  cases values with
  | nil => simp only [manyCosts, List.not_mem_nil] at member
  | cons first rest =>
      simp only [manyCosts] at member
      rcases List.mem_append.mp member with own | later
      · have bound := cost_le_mass first name count own; simp only [InternedValueMass.values]; omega
      · have bound := many_cost_le_mass rest name count later; simp only [InternedValueMass.values]; omega
termination_by sizeOf values

/-- Ordered row payloads bound every retained free-occurrence cost. -/
theorem edge_cost_le_mass (edges : List (EdgeValue Symbol Guard)) (name count)
    (member : (name, count) ∈ edgeCosts edges) : count ≤ InternedValueMass.edges edges := by
  cases edges with
  | nil => simp only [edgeCosts, List.not_mem_nil] at member
  | cons first rest =>
      cases first with
      | mk entry children =>
          simp only [edgeCosts] at member
          rcases List.mem_append.mp member with own | later
          · have bound := many_cost_le_mass children name count own
            simp only [InternedValueMass.edges, InternedValueMass.edge]; omega
          · have bound := edge_cost_le_mass rest name count later
            simp only [InternedValueMass.edges]; omega
termination_by sizeOf edges
end

/-- Cached metadata is not needed to bound the executable occurrence rank. -/
theorem rank_le_mass (value : Value Symbol Guard) : rank value ≤ InternedValueMass.value value := by
  cases least : ((costs value).map Prod.snd).min? with
  | none => simp only [rank, least, Option.getD_none]; omega
  | some minimum =>
      obtain ⟨⟨name, count⟩, member, same⟩ := List.mem_map.mp (List.min?_eq_some_iff.mp least).1
      have bound := cost_le_mass value name count member
      simpa only [rank, least, Option.getD_some, ← same] using bound

/-- Current causal payload mass bounds the rank at each actual gate entry. -/
theorem rank_le {bound : Nat} {heap : State Symbol Guard} (fits : Fits bound heap)
    {value : Value Symbol Guard} (available : Available heap value) : rank value ≤ bound :=
  Nat.le_trans (rank_le_mass value) (InternedValueMassHeap.available heap fits.stored value available)

/-- Actual full open or closed unfolding fits the next scalar envelope. -/
theorem unfold_fits [DecidableEq (EdgeKey Symbol Guard)] {bound : Nat}
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after)
    (fits : Fits bound before) (available : Available before value) : Fits (g bound) after := by
  have produced := SourceCurrentAllocatedProjectionResources.unfold_bound value before bound fits.stored available
  have stored : Stored (SourceCurrentAllocatedRecursiveMassTrace.ceiling bound) after := by
    simpa only [actual, InternedNestedConstruction.Outcome.state] using produced.1
  have nodes : after.nodes.next ≤ before.nodes.next + SourceCurrentAllocatedRecursiveMassTrace.charge bound := by
    simpa only [actual, InternedNestedConstruction.Outcome.state] using produced.2.1
  have edges : after.edges.next ≤ before.edges.next + SourceCurrentAllocatedRecursiveMassTrace.charge bound := by
    simpa only [actual, InternedNestedConstruction.Outcome.state] using produced.2.2.1
  refine ⟨stored.mono (by unfold g; omega), ?_, ?_, Nat.zero_le _⟩
  · have old := fits.nodes; change before.nodes.next ≤ bound at old
    change after.nodes.next ≤ g bound; unfold g; omega
  · have old := fits.edges; change before.edges.next ≤ bound at old
    change after.edges.next ≤ g bound; unfold g; omega

/-- A fixed number of open unfolds has an initial scalar forecast. -/
def muPrefix (count bound : Nat) : Nat := iterate g count bound
/-- One spare unit makes every same-path prefix a conservative bound. -/
def unfoldPrefix (bound : Nat) : Nat := muPrefix (bound + 1) bound

/-- A node first pays its same-path prefix, then each original ordinary row. -/
def nodeBound : Nat → Nat → Nat
  | 0, bound => unfoldPrefix bound
  | height + 1, bound => let start := unfoldPrefix bound; iterate (nodeBound height) start start
/-- An ordinary node needs no same-path unfolding muPrefix. -/
def ordinaryBound : Nat → Nat → Nat
  | 0, bound => bound
  | height + 1, bound => iterate (nodeBound height) bound bound

/-- The ordinary phase follows the complete initial same-path prefix. -/
theorem nodeBound_eq (height bound : Nat) : nodeBound height bound = ordinaryBound height (unfoldPrefix bound) := by
  cases height <;> rfl
/-- Every muPrefix retains its initial scalar. -/
theorem muPrefix_ge (count bound : Nat) : bound ≤ muPrefix count bound := iterate_ge g (fun q => Nat.le_of_lt (g_strict q)) count bound
/-- Larger muPrefix counts and initial scalars retain the whole prefix. -/
theorem muPrefix_mono {firstCount lastCount first last : Nat} (counts : firstCount ≤ lastCount) (bounds : first ≤ last) :
    muPrefix firstCount first ≤ muPrefix lastCount last :=
  Nat.le_trans (iterate_mono g g_mono firstCount bounds) (iterate_count_mono g (fun q => Nat.le_of_lt (g_strict q)) counts last)
/-- One unfolding shifts the remaining prefix to its literal next scalar. -/
theorem muPrefix_succ (count bound : Nat) : muPrefix (count + 1) bound = muPrefix count (g bound) := rfl
/-- The full initial prefix retains the original scalar. -/
theorem unfoldPrefix_ge (bound : Nat) : bound ≤ unfoldPrefix bound := muPrefix_ge _ _
/-- Larger initial scalars retain their complete same-path prefix. -/
theorem unfoldPrefix_mono {first last : Nat} (bounds : first ≤ last) : unfoldPrefix first ≤ unfoldPrefix last :=
  muPrefix_mono (Nat.succ_le_succ bounds) bounds

/-- Every complete node forecast retains its original scalar. -/
theorem nodeBound_ge (height bound : Nat) : bound ≤ nodeBound height bound := by
  induction height generalizing bound with
  | zero => exact unfoldPrefix_ge bound
  | succ height ih => exact Nat.le_trans (unfoldPrefix_ge bound) (iterate_ge _ ih _ _)
/-- Larger initial scalars retain every complete node forecast. -/
theorem nodeBound_mono (height : Nat) {first last : Nat} (bounds : first ≤ last) : nodeBound height first ≤ nodeBound height last := by
  induction height generalizing first last with
  | zero => exact unfoldPrefix_mono bounds
  | succ height ih =>
      exact Nat.le_trans (iterate_mono _ ih _ (unfoldPrefix_mono bounds))
        (iterate_count_mono _ (nodeBound_ge height) (unfoldPrefix_mono bounds) _)
/-- Every ordinary phase retains its input scalar. -/
theorem ordinaryBound_ge (height bound : Nat) : bound ≤ ordinaryBound height bound := by
  cases height with
  | zero => exact Nat.le_refl _
  | succ height => exact iterate_ge _ (nodeBound_ge height) _ _
/-- Larger input scalars retain an ordinary phase's complete ordered scan. -/
theorem ordinaryBound_mono (height : Nat) {first last : Nat} (bounds : first ≤ last) : ordinaryBound height first ≤ ordinaryBound height last := by
  cases height with
  | zero => exact bounds
  | succ height =>
      exact Nat.le_trans (iterate_mono _ (nodeBound_mono height) _ bounds)
        (iterate_count_mono _ (nodeBound_ge height) bounds _)

/-- Worker fuel pays each same-path unfold and the largest smaller-path query. -/
def nodeFuel : Nat → Nat → Nat
  | 0, bound => bound + 1 + 1
  | height + 1, bound => bound + 1 + (1 + nodeFuel height (nodeBound (height + 1) bound))
/-- An ordinary phase pays one dispatch before a possible child query. -/
def ordinaryFuel : Nat → Nat → Nat
  | 0, _ => 1
  | height + 1, bound => 1 + nodeFuel height (ordinaryBound (height + 1) bound)
/-- Prefix fuel and ordinary fuel compose at the forecasted muPrefix return. -/
theorem nodeFuel_eq (height bound : Nat) : nodeFuel height bound = bound + 1 + ordinaryFuel height (unfoldPrefix bound) := by
  cases height <;> rfl
/-- Larger initial scalars retain the uniform node worker fuel. -/
theorem nodeFuel_mono (height : Nat) {first last : Nat} (bounds : first ≤ last) : nodeFuel height first ≤ nodeFuel height last := by
  induction height generalizing first last with
  | zero => unfold nodeFuel; omega
  | succ height ih =>
      exact Nat.add_le_add (Nat.add_le_add_right bounds 1)
        (Nat.add_le_add_left (ih (nodeBound_mono (height + 1) bounds)) 1)
/-- Larger initial scalars retain the ordinary phase's worker fuel. -/
theorem ordinaryFuel_mono (height : Nat) {first last : Nat} (bounds : first ≤ last) : ordinaryFuel height first ≤ ordinaryFuel height last := by
  cases height with
  | zero => exact Nat.le_refl _
  | succ height => exact Nat.add_le_add_left (nodeFuel_mono height (ordinaryBound_mono (height + 1) bounds)) 1

/-- A forest path first selects its original root and then performs a node query. -/
def pathBound : List Nat → Nat → Nat
  | [], bound => bound
  | _ :: rest, bound => nodeBound rest.length bound
/-- Empty paths dispatch no node query. -/
def pathFuel : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: rest, bound => nodeFuel rest.length bound
/-- Class paths run in their original order at forecasted muPrefix heaps. -/
def classBound : List (List Nat) → Nat → Nat
  | [], bound => bound
  | path :: rest, bound => classBound rest (pathBound path bound)
/-- One common class fuel covers each exact forecasted path entry. -/
def classFuel : List (List Nat) → Nat → Nat
  | [], _ => 0
  | path :: rest, bound => max (pathFuel path bound) (classFuel rest (pathBound path bound))

/-- Ordinary dispatch always has at least one worker step. -/
theorem ordinaryFuel_pos (height bound : Nat) : 0 < ordinaryFuel height bound := by
  cases height <;> simp only [ordinaryFuel] <;> omega
/-- The node worker forecast retains the initial scalar and one dispatch. -/
theorem nodeFuel_ge (height bound : Nat) : bound + 1 ≤ nodeFuel height bound := by
  rw [nodeFuel_eq]
  exact Nat.le_add_right _ _
/-- The node forecast includes the ordinary phase at its initial scalar. -/
theorem ordinaryFuel_le_nodeFuel (height bound : Nat) : ordinaryFuel height bound ≤ nodeFuel height bound := by
  have larger := ordinaryFuel_mono height (unfoldPrefix_ge bound)
  rw [nodeFuel_eq]
  omega
/-- Every forest path retains the initial scalar. -/
theorem pathBound_ge (path : List Nat) (bound : Nat) : bound ≤ pathBound path bound := by
  cases path with
  | nil => exact Nat.le_refl _
  | cons index rest => exact nodeBound_ge _ _
/-- Larger initial scalars retain any original path forecast. -/
theorem pathBound_mono (path : List Nat) {first last : Nat} (bounds : first ≤ last) : pathBound path first ≤ pathBound path last := by
  cases path with
  | nil => exact bounds
  | cons index rest => exact nodeBound_mono _ bounds
/-- Larger initial scalars retain a path's common worker fuel. -/
theorem pathFuel_mono (path : List Nat) {first last : Nat} (bounds : first ≤ last) : pathFuel path first ≤ pathFuel path last := by
  cases path with
  | nil => exact Nat.le_refl _
  | cons index rest => exact nodeFuel_mono _ bounds
/-- A class forecast retains its original heap resources. -/
theorem classBound_ge (paths : List (List Nat)) (bound : Nat) : bound ≤ classBound paths bound := by
  induction paths generalizing bound with
  | nil => exact Nat.le_refl _
  | cons path rest ih => exact Nat.le_trans (pathBound_ge path bound) (ih _)
/-- Larger initial scalars retain all ordered class path returns. -/
theorem classBound_mono (paths : List (List Nat)) {first last : Nat} (bounds : first ≤ last) : classBound paths first ≤ classBound paths last := by
  induction paths generalizing first last with
  | nil => exact bounds
  | cons path rest ih => exact ih (pathBound_mono path bounds)
/-- Larger initial scalars retain the uniform fuel for every class path. -/
theorem classFuel_mono (paths : List (List Nat)) {first last : Nat} (bounds : first ≤ last) : classFuel paths first ≤ classFuel paths last := by
  induction paths generalizing first last with
  | nil => exact Nat.le_refl _
  | cons path rest ih =>
      exact Nat.max_le.mpr ⟨Nat.le_trans (pathFuel_mono path bounds) (Nat.le_max_left _ _),
        Nat.le_trans (ih (pathBound_mono path bounds)) (Nat.le_max_right _ _)⟩

end MicroCFTA.SourceCurrentPrimaryGateResources
