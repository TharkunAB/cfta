import MicroCFTA.MergedComparisonWarmProgress

/-!
# A decreasing cold-record measure for physical comparison

The fixed initial complete-record list contains every later Mu. Actual
cache growth can only remove cold entries. A changed reader warms at
least one entry, so the number of cold originals strictly decreases.
-/
namespace MicroCFTA.MergedComparisonColdMeasure
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedShallowHeap MergedPhysicalWarmup MergedComparisonWarmProgress
open InternedBinderProtocol (NodeKey)

/-- The fixed original physical inventory includes every currently available Mu. -/
def CoversMu (originals : List (Value Symbol Guard)) (state : State Symbol Guard) : Prop :=
  ∀ entry body depth ordinary, Available state (.mu entry body depth ordinary) →
    Value.mu entry body depth ordinary ∈ originals

/-- The actual initial issued inventory supplies the recursive domain. -/
theorem covers_initial (state : State Symbol Guard) (facts : Facts state) : CoversMu (nodeInventory state) state := by
  intro entry body depth ordinary available
  exact inventory_complete state facts.coherent entry.key _ (available.resident entry rfl)

/-- Actual effects that add no Mu preserve the fixed initial recursive domain. -/
theorem CoversMu.preserve (before after : State Symbol Guard) (facts : Facts before)
    (originals : List (Value Symbol Guard)) (covers : CoversMu originals before) (unchanged : NoNewMu before after) :
    CoversMu originals after := by
  intro entry body depth ordinary available
  exact covers entry body depth ordinary (facts.cached.nodes entry.key _
    (unchanged entry.key entry body depth ordinary (available.resident entry rfl)))

/-- Count original records whose actual stored unfolding still changes the cache. -/
noncomputable def coldCount [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (state : State Symbol Guard) : Nat := by
  classical
  exact originals.foldr (fun value count => if Warm state value then count else count + 1) 0

/-- An empty initial list has no outstanding cold record. -/
theorem coldCount_nil [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) : coldCount [] state = 0 := rfl

/-- Each original contributes one precisely when its unfolding is still cold. -/
theorem coldCount_cons [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (rest : List (Value Symbol Guard)) (state : State Symbol Guard) :
    coldCount (value :: rest) state =
      @ite Nat (Warm state value) (Classical.propDecidable _) (coldCount rest state) (coldCount rest state + 1) := rfl

/-- Later actual cache growth cannot make an original warm record cold again. -/
theorem coldCount_le [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after) :
    coldCount originals after ≤ coldCount originals before := by
  classical
  induction originals with
  | nil => exact Nat.le_refl _
  | cons value rest ih =>
      by_cases first : Warm before value
      · have later := first.grows before after valid growth value
        simpa only [coldCount_cons, ite_eq_left first, ite_eq_left later] using ih
      · by_cases later : Warm after value <;> simp only [coldCount_cons, first, later, ↓reduceIte] <;> omega

/-- Warming one retained cold original strictly decreases the finite cold count. -/
theorem coldCount_lt [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    (value : Value Symbol Guard) (member : value ∈ originals) (cold : ¬ Warm before value) (warm : Warm after value) :
    coldCount originals after < coldCount originals before := by
  classical
  induction originals with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst first
        have tail := coldCount_le rest before after valid growth
        simp only [coldCount_cons, ite_eq_right cold, ite_eq_left warm]
        omega
      · have tail := ih member
        by_cases firstWarm : Warm before first
        · have later := firstWarm.grows before after valid growth first
          simpa only [coldCount_cons, ite_eq_left firstWarm, ite_eq_left later] using tail
        · by_cases later : Warm after first <;> simp only [coldCount_cons, firstWarm, later, ↓reduceIte] <;> omega

/-- Every changed actual effect with warm progress decreases the count of original cold Mu records. -/
theorem progress_lt [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (before after : State Symbol Guard) (valid : Valid before) (growth : Grows before after)
    (covers : CoversMu originals before) (progress : Progress before after) (changed : after ≠ before) :
    coldCount originals after < coldCount originals before := by
  obtain ⟨entry, body, depth, ordinary, available, cold, warm⟩ := progress.resolve_left changed
  exact coldCount_lt originals before after valid growth _ (covers entry body depth ordinary available) cold warm

/-- The actual cold source reader either returns its initial cache or strictly decreases the cold count. -/
theorem reader_progress [DecidableEq (EdgeKey Symbol Guard)] (originals : List (Value Symbol Guard))
    (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (prepared : Prepared state) (available : Available state value) (covers : CoversMu originals state) :
    (MergedSourceExposure.nodeEdges fuel value state).state = state ∨
      coldCount originals (MergedSourceExposure.nodeEdges fuel value state).state < coldCount originals state := by
  by_cases same : (MergedSourceExposure.nodeEdges fuel value state).state = state
  · exact Or.inl same
  · exact Or.inr (progress_lt originals state _ facts.coherent.valid
      (MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared available).growth covers
      (nodeEdges_progress fuel value state facts prepared available) same)

end MicroCFTA.MergedComparisonColdMeasure
