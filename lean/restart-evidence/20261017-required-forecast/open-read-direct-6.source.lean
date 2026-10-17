import MicroCFTA.SourceCurrentProjectionUnionResources
import MicroCFTA.SourceSecondaryGateHead
import MicroCFTA.SourceEqualityProjectionCosts

/-!
# Initial numeric reads for supported open warm heads

WarmHead permits open ordinary values and same-heap Mu unfolding prefixes.
Each fresh prefix identity belongs to the initial issued inventory. A closed
suffix uses the existing controlled collector bound. This module does not
assert numeric completion for arbitrary open recursive values.
-/
namespace MicroCFTA.SourceCurrentOpenRowReadResources
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceEqualityRequiredCache (Keeps)
open SourceCurrentMemoMergeResourceControl (Fits primitiveGrowth)
open SourceCurrentMemoMergeEffects (Effect)
open SourceSecondaryGateHead (WarmHead)
open MergedFreshOrdinaryExposure (collect nodeEdges)
open SourceCurrentAllocatedRecursiveMassTrace (massAfter)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Initial issued identities pay the same-heap prefix before closed collection. -/
def readFuel (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readFuel bound + 1
/-- The initial ordinary rows and a closed suffix share one width envelope. -/
def readWidth (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readWidth bound
/-- The original heap and the closed collector return fit one scalar. -/
def readGrowth (bound : Nat) : Nat := bound + SourceCurrentProjectionUnionResources.readFuel bound + readWidth bound
/-- Head reconstruction pays its literal final node constructor. -/
def headGrowth (bound : Nat) : Nat := primitiveGrowth (readWidth bound) (readGrowth bound)

/-- Increasing initial resources retain the shared open read fuel. -/
theorem readFuel_mono {first last : Nat} (increase : first ≤ last) : readFuel first ≤ readFuel last := by
  have fuel := SourceCurrentProjectionUnionResources.readFuel_mono increase
  unfold readFuel
  omega
/-- Increasing initial resources retain the output row envelope. -/
theorem readWidth_mono {first last : Nat} (increase : first ≤ last) : readWidth first ≤ readWidth last :=
  Nat.add_le_add increase (SourceCurrentProjectionUnionResources.readWidth_mono increase)
/-- Increasing initial resources retain the returned heap envelope. -/
theorem readGrowth_mono {first last : Nat} (increase : first ≤ last) : readGrowth first ≤ readGrowth last :=
  Nat.add_le_add (Nat.add_le_add increase (SourceCurrentProjectionUnionResources.readFuel_mono increase))
    (readWidth_mono increase)
/-- The read envelope retains the initial resources. -/
theorem readGrowth_ge (bound : Nat) : bound ≤ readGrowth bound := by unfold readGrowth; omega
/-- The read envelope includes its output width. -/
theorem readWidth_le_growth (bound : Nat) : readWidth bound ≤ readGrowth bound := by unfold readGrowth; omega
/-- Increasing initial resources retain the head envelope. -/
theorem headGrowth_mono {first last : Nat} (increase : first ≤ last) : headGrowth first ≤ headGrowth last :=
  SourceCurrentMemoMergeResourceControl.primitiveGrowth_mono (readWidth_mono increase) (readGrowth_mono increase)
/-- The head envelope retains the initial resources. -/
theorem headGrowth_ge (bound : Nat) : bound ≤ headGrowth bound :=
  Nat.le_trans (readGrowth_ge bound) (SourceCurrentMemoMergeResourceControl.primitiveGrowth_ge _ _)

private theorem closedFuel_ge (bound : Nat) : bound ≤ SourceCurrentProjectionUnionResources.readFuel bound := by
  have growth := SourceCurrentAllocatedReaderControl.g_strict bound
  have major := HeightOrderControlled.majorant_ge SourceCurrentAllocatedReaderControl.g
    SourceCurrentAllocatedReaderControl.g_strict (bound + 1) (SourceCurrentAllocatedReaderControl.g bound)
  simpa only [SourceCurrentProjectionUnionResources.readFuel, SourceCurrentAllocatedRowReadNumeric.readFuel,
    SourceCurrentAllocatedReaderNumeric.fuel, SourceCurrentAllocatedReaderNumeric.initialControl,
    Nat.one_mul, Nat.max_self] using Nat.le_trans (Nat.le_of_lt growth) major

section Actual
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem unfolded_available {value next : Value Symbol Guard} {heap : State Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap value)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value heap = .done next heap) : Available heap next := by
  obtain ⟨result, after, done, _, _, known, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete value heap semantic available
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (done.symm.trans actual)
  exact known

private theorem closed_collect (bound : Nat) (heap : State Symbol Guard) (seen : List Nat)
    (value : Value Symbol Guard) (semantic : SemanticReady heap) (available : Available heap value)
    (closed : value.free = []) (fits : Fits bound heap) :
    ∃ rows after, collect (SourceCurrentProjectionUnionResources.readFuel bound) heap seen [value] = .done rows after ∧
      Fits (SourceCurrentProjectionUnionResources.readFuel bound) after ∧
      rows.length ≤ SourceCurrentProjectionUnionResources.readWidth bound := by
  let config : SourceCurrentAllocatedReaderControl.Config Symbol Guard := ⟨heap, seen, [value]⟩
  have good : SourceCurrentAllocatedReaderControl.Good bound config :=
    ⟨semantic.ready.semantic, semantic.ready.covered, semantic.ready.depth,
      InternedValueMassBinderDepth.stored_bounded heap bound fits.stored,
      by intro item member; cases List.mem_singleton.mp member; exact available,
      by intro item member; cases List.mem_singleton.mp member; exact closed⟩
  have initial : SourceCurrentAllocatedReaderControl.Fits bound config := by
    refine ⟨fits.stored, fits.nodes, fits.edges, ?_⟩
    have small := Nat.le_trans (SourceCurrentAllocatedReaderControl.weight_le_mass value)
      (InternedValueMassHeap.available heap fits.stored value available)
    simpa only [config, MergedColdReaderTermination.workWeight, Nat.add_zero] using small
  obtain ⟨count, rows, after, _, _, _, afterFits, _, done, _⟩ :=
    SourceCurrentAllocatedReaderNumeric.control_complete bound (SourceCurrentAllocatedReaderControl.g bound)
      config good (initial.mono (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict bound)))
  have done : collect (SourceCurrentProjectionUnionResources.readFuel bound) heap seen [value] = .done rows after.heap := by
    simpa only [SourceCurrentProjectionUnionResources.readFuel, SourceCurrentAllocatedRowReadNumeric.readFuel,
      SourceCurrentAllocatedReaderNumeric.initialControl, Nat.one_mul, Nat.max_self, config] using done
  have afterFits : SourceCurrentAllocatedReaderControl.Fits (SourceCurrentProjectionUnionResources.readFuel bound) after := by
    simpa only [SourceCurrentProjectionUnionResources.readFuel, SourceCurrentAllocatedRowReadNumeric.readFuel,
      SourceCurrentAllocatedReaderNumeric.initialControl, Nat.one_mul, Nat.max_self] using afterFits
  have resources := SourceCurrentAllocatedProjectionResources.collect_bound
    (SourceCurrentProjectionUnionResources.readFuel bound) heap semantic.ready.semantic semantic.ready.covered
    seen [value] good.available good.closed bound fits.stored rows after.heap done
  have width := Nat.le_trans resources.2.2.2
    (Nat.mul_le_mul (Nat.le_succ _) (SourceCurrentAllocatedRecursiveMassMonotone.massAfter_mono
      (Nat.le_succ _) (Nat.le_refl bound)))
  exact ⟨rows, after.heap, done, ⟨afterFits.stored, afterFits.nodes, afterFits.edges, Nat.zero_le _⟩, width⟩

private theorem collect_count {heap : State Symbol Guard} {value : Value Symbol Guard}
    (warm : WarmHead heap value) (bound : Nat) (semantic : SemanticReady heap)
    (available : Available heap value) (fits : Fits bound heap) (seen remaining : List Nat)
    (unseen : ∀ identity, identity < heap.nodes.next → identity ∉ seen → identity ∈ remaining) :
    ∃ fuel rows after, fuel ≤ remaining.length + SourceCurrentProjectionUnionResources.readFuel bound + 1 ∧
      collect fuel heap seen [value] = .done rows after ∧
      Fits (SourceCurrentProjectionUnionResources.readFuel bound) after ∧ rows.length ≤ readWidth bound := by
  induction warm generalizing seen remaining with
  | empty =>
      exact ⟨1, [], heap, by omega, rfl,
        fits.mono (closedFuel_ge bound), by simp only [List.length_nil]; omega⟩
  | @ordinary entry rows depth free =>
      have small := InternedValueMassHeap.available heap fits.stored (.node entry rows depth free) available
      have length := InternedStoredEncodingWidth.edges_length rows
      have width : rows.length ≤ readWidth bound := by
        simp only [InternedValueMass.value] at small
        unfold readWidth
        omega
      exact ⟨1, rows, heap, by omega,
        by simp only [collect, MergedSourceExposure.Result.prepend, List.append_nil],
        fits.mono (closedFuel_ge bound), width⟩
  | closed closed =>
      obtain ⟨rows, after, done, afterFits, width⟩ := closed_collect bound heap seen _ semantic available closed fits
      exact ⟨_, rows, after, by omega, done, afterFits, by unfold readWidth; omega⟩
  | @unfold entry body depth ordinary next actual _ ih =>
      by_cases visited : entry.identity ∈ seen
      · exact ⟨1, [], heap, by omega, by simp only [collect, ite_eq_left visited],
          fits.mono (closedFuel_ge bound), by simp only [List.length_nil]; omega⟩
      · have facts := semantic.ready.semantic.1.normal.facts
        have stored := InternedFreshProbeKeys.resident_entry heap facts.coherent _ available.resident entry rfl
        have issued := facts.coherent.valid.2.1 entry.identity entry.key
          (facts.coherent.valid.2.2 entry.key entry stored).2
        have member := unseen entry.identity issued visited
        have retained : ∀ identity, identity < heap.nodes.next → identity ∉ entry.identity :: seen →
            identity ∈ remaining.erase entry.identity := by
          intro identity inside fresh
          have different : identity ≠ entry.identity := by intro same; subst identity; exact fresh (by simp)
          exact (List.mem_erase_of_ne different).mpr (unseen identity inside (fun old => fresh (by simp only [List.mem_cons]; exact Or.inr old)))
        obtain ⟨fuel, rows, after, enough, done, afterFits, width⟩ :=
          ih (unfolded_available semantic available actual) (entry.identity :: seen) (remaining.erase entry.identity) retained
        have shorter := List.length_erase_of_mem member
        have positive := List.length_pos_of_mem member
        exact ⟨fuel + 1, rows, after, by omega,
          by simpa only [collect, ite_eq_right visited, actual] using done, afterFits, width⟩

/-- A supported warm collector constructs its own success from initial scalar resources. -/
theorem collect_complete {heap : State Symbol Guard} {value : Value Symbol Guard}
    (warm : WarmHead heap value) (bound : Nat) (semantic : SemanticReady heap)
    (available : Available heap value) (fits : Fits bound heap) (seen : List Nat) :
    ∃ rows after, collect (readFuel bound) heap seen [value] = .done rows after ∧
      Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound := by
  obtain ⟨fuel, rows, after, enough, done, afterFits, width⟩ :=
    collect_count warm bound semantic available fits seen (List.range heap.nodes.next)
      (by intro identity inside _; exact List.mem_range.mpr inside)
  have shorter : fuel ≤ readFuel bound := by
    simp only [List.length_range] at enough
    have nodes : heap.nodes.next ≤ bound := fits.nodes
    unfold readFuel
    omega
  have stable := MergedFreshOrdinaryColdReplay.collect_stable fuel (readFuel bound - fuel) heap seen [value]
    (by simp only [done, MergedSourceExposure.Finished])
  have equal : fuel + (readFuel bound - fuel) = readFuel bound := by omega
  rw [equal, done] at stable
  exact ⟨rows, after, stable, afterFits.mono (by unfold readGrowth; omega), width⟩


private theorem numeric_read {heap : State Symbol Guard} {value : Value Symbol Guard}
    (warm : WarmHead heap value) (bound : Nat) (semantic : SemanticReady heap)
    (available : Available heap value) (fits : Fits bound heap) :
    ∃ rows after, nodeEdges (readFuel bound) value heap = .done rows after ∧
      Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound := by
  have unchanged (rows : List (EdgeValue Symbol Guard))
      (done : nodeEdges (readFuel bound) value heap = .done rows heap) (width : rows.length ≤ bound) :
      ∃ rows after, nodeEdges (readFuel bound) value heap = .done rows after ∧
        Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound :=
    ⟨rows, heap, done, fits.mono (readGrowth_ge bound), by unfold readWidth; omega⟩
  cases warm with
  | empty => exact unchanged [] rfl (Nat.zero_le _)
  | @ordinary entry rows depth free =>
      have small := InternedValueMassHeap.available heap fits.stored (.node entry rows depth free) available
      have length := InternedStoredEncodingWidth.edges_length rows
      exact unchanged rows rfl (by simp only [InternedValueMass.value] at small; omega)
  | closed closed =>
      obtain ⟨rows, after, done, _, _, _, stored, nodes, edges, _, _, stable⟩ :=
        SourceCurrentAllocatedRowReadUniform.complete value heap bound semantic available closed
          fits.stored fits.nodes fits.edges
      have width := SourceCurrentAllocatedProjectionResources.read_bound
        (SourceCurrentProjectionUnionResources.readFuel bound) value heap semantic.ready.semantic
        semantic.ready.covered available closed bound fits.stored rows after done
      have extra := stable (bound + 1)
      have same : SourceCurrentProjectionUnionResources.readFuel bound + (bound + 1) = readFuel bound := by
        unfold readFuel
        omega
      change nodeEdges (SourceCurrentProjectionUnionResources.readFuel bound + (bound + 1)) value heap = .done rows after at extra
      rw [same] at extra
      have enough : SourceCurrentProjectionUnionResources.readFuel bound ≤ readGrowth bound := by
        unfold readGrowth
        omega
      exact ⟨rows, after, extra, ⟨stored.mono enough, Nat.le_trans nodes enough, Nat.le_trans edges enough,
        Nat.zero_le _⟩, by have known := width.2.2.2.1; unfold readWidth; omega⟩
  | @unfold entry body depth ordinary next actual rest =>
      obtain ⟨rows, after, done, afterFits, width⟩ :=
        collect_complete (.unfold actual rest) bound semantic available fits []
      have fallback : (collect (readFuel bound) heap [] [.mu entry body depth ordinary]).canonical =
          .done (canonicalEdges rows) after := by rw [done]; rfl
      have canonical : (canonicalEdges rows).length ≤ rows.length :=
        List.Nodup.length_le_of_subset (MergedNodeRowBounds.canonical_nodup rows) (canonicalEdges_member rows)
      have nextAvailable := unfolded_available semantic available actual
      cases next with
      | node entry more depth free =>
          have small := InternedValueMassHeap.available heap fits.stored (.node entry more depth free) nextAvailable
          have length := InternedStoredEncodingWidth.edges_length more
          exact unchanged more (by simp only [nodeEdges, actual])
            (by simp only [InternedValueMass.value] at small; omega)
      | empty | reference | union | mu =>
          exact ⟨canonicalEdges rows, after, by simpa only [nodeEdges, actual] using fallback,
            afterFits, Nat.le_trans canonical width⟩

/-- Initial support constructs an exact row read at one computed sufficient fuel. -/
theorem complete (value : Value Symbol Guard) (heap : State Symbol Guard) (bound : Nat)
    (semantic : SemanticReady heap) (available : Available heap value) (warm : WarmHead heap value)
    (fits : Fits bound heap) :
    ∃ rows after, nodeEdges (readFuel bound) value heap = .done rows after ∧
      SourceEqualityProjectionRead.Read value heap rows after ∧
      Keeps heap after ∧ SemanticReady after ∧ Fits (readGrowth bound) after ∧
      rows.length ≤ readWidth bound ∧ Edges after rows ∧
      ∀ extra, nodeEdges (readFuel bound + extra) value heap = .done rows after := by
  obtain ⟨rows, after, done, afterFits, width⟩ := numeric_read warm bound semantic available fits
  obtain ⟨oldFuel, oldRows, oldAfter, oldDone, keeps, ready, resident⟩ :=
    SourceSecondaryGateHead.warm_nodeEdges_complete warm semantic available
  obtain ⟨sameRows, sameHeap⟩ := SourceEqualityProjectionRead.Read.unique (.done oldFuel oldDone) (.done _ done)
  subst oldRows
  subst oldAfter
  refine ⟨rows, after, done, .done _ done, keeps, ready, afterFits, width, resident, ?_⟩
  intro extra
  exact (MergedFreshOrdinaryColdReplay.nodeEdges_stable _ extra value heap
    (by simp only [done, MergedSourceExposure.Finished])).trans done

/-- An earlier successful read has the same complete return at the initial supported fuel. -/
theorem read {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value before rows after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (warm : WarmHead before value) (fits : Fits bound before) :
    Effect before after ∧ Fits (readGrowth bound) after ∧ rows.length ≤ readWidth bound ∧
      Edges after rows ∧ SourceCurrentProjectionNumericReplay.ReadReady (readFuel bound) actual ∧
      ∀ extra, nodeEdges (readFuel bound + extra) value before = .done rows after := by
  obtain ⟨produced, final, done, checked, _, _, afterFits, width, resident, stable⟩ :=
    complete value before bound semantic available warm fits
  obtain ⟨rfl, rfl⟩ := checked.unique actual
  obtain ⟨keeps, ready, finalCosts, _⟩ := SourceEqualityProjectionCosts.read_effects actual semantic costs available
  exact ⟨⟨keeps, ready, finalCosts⟩, afterFits, width, resident, done, stable⟩

/-- Larger scalar bounds replay the same demanded read at the shared fuel. -/
theorem read_ready {value : Value Symbol Guard} {before after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value before rows after)
    (bound larger : Nat) (semantic : SemanticReady before) (available : Available before value)
    (warm : WarmHead before value) (fits : Fits bound before) (increase : bound ≤ larger) :
    SourceCurrentProjectionNumericReplay.ReadReady (readFuel larger) actual := by
  obtain ⟨produced, final, done, checked, _⟩ :=
    complete value before larger semantic available warm (fits.mono increase)
  obtain ⟨rfl, rfl⟩ := checked.unique actual
  exact done

/-- Open supported head normalization retains its exact returned heap and shared read certificate. -/
theorem head {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (bound : Nat) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before value) (warm : WarmHead before value) (fits : Fits bound before) :
    Effect before after ∧ Fits (headGrowth bound) after ∧ Available after result ∧
      SourceEqualityRequiredCache.Ordinary result ∧
      SourceCurrentProjectionNumericReplay.HeadReady (readFuel (headGrowth bound)) actual := by
  cases actual with
  | read oldFuel rows middle exposed rebuilt =>
      have first := read (.done oldFuel exposed) bound semantic costs available warm fits
      have final := SourceEqualityOpenOrdinaryHead.node rows middle first.1.semantic first.2.2.2.1
      have finalEffect : Effect middle (run (makeNode rows) middle).2 :=
        ⟨final.1, final.2.1, InternedFreshOrdinaryCostHeap.preserve middle _ first.1.costs
          (InternedShallowHeap.makeNode_noNewMu rows middle)⟩
      have resources := SourceCurrentMemoMergeResourceControl.node rows middle (readGrowth bound) (readWidth bound)
        first.2.1 first.2.2.2.1 first.2.2.1
      have ready := read_ready (.done oldFuel exposed) bound (headGrowth bound) semantic available warm fits (headGrowth_ge bound)
      have resultSame := congrArg Prod.fst rebuilt
      have stateSame := congrArg Prod.snd rebuilt
      dsimp only at resultSame stateSame
      subst result
      subst after
      exact ⟨first.1.trans finalEffect, resources.1, final.2.2.1, final.2.2.2,
        .read oldFuel rows middle exposed rfl ready final.2.2.2⟩

end Actual
end MicroCFTA.SourceCurrentOpenRowReadResources
