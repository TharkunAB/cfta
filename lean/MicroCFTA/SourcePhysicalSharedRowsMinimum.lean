import MicroCFTA.SourcePhysicalSharedRowsLanguage

/-!
# Actual shared-row minimum and overlap callbacks for physical plain records

The callback reads the completed physical result, traverses its actual
shared rows, and executes the proved minimum recurrence. Concrete dispatch
correctness gives its common-language test. No global product graph or
child-pair identity function is required.
-/
namespace MicroCFTA.SourcePhysicalSharedRows
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency SourceInternedIntersectionRows Language

/-- The actual callback combines the source row precheck with minimum-table lookup. -/
def productive (state : State Symbol Unit) (value : Value Symbol Unit)
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Unit))) : Bool :=
  SourceRowsMinimumPublic.productiveRows (heap state) (reference value) raw

/-- The source precheck reads exactly the actual physical node's outgoing edge emptiness. -/
theorem productive_source (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value)
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Unit))) :
    productive state value raw = if (nodeEdges value).isEmpty then false
      else (SourceRowsMinimumAdapter.minimumSizes raw (encode value)).isSome := by
  unfold productive SourceRowsMinimumPublic.productiveRows
  change (if (SourceInternedRows.graph (heap state) (fun _ _ => true) (encode value)).isEmpty then false else _) = _
  rw [graph_readback state facts value available plain]
  simp [rows, encode]

/-- Actual row traversal and actual minimum iteration both have finite completed executions. -/
theorem finite (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) :
    ∃ fuel raw minimumFuel,
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap state) larger (reference value) = some raw) ∧
      MinimumSize.sweeps (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) =
        SourceRowsMinimumAdapter.minimumSizes raw ∧
      MinimumSize.sweep (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst)
        (SourceRowsMinimumAdapter.minimumSizes raw) = SourceRowsMinimumAdapter.minimumSizes raw := by
  apply SourceRowsMinimumPublic.finite (heap state) (List.range state.nodes.next) (heap_closed state facts)
  intro identity same
  exact List.mem_range.mpr (reference_bounded state facts value available identity same)

/-- The callback answers true exactly when the concrete physical root has an accepted finite term. -/
theorem productive_exact (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (fuel : Nat)
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Unit)))
    (done : SourceInternedRows.toRows (heap state) fuel (reference value) = some raw) :
    productive state value raw = true ↔ ∃ term, SourceInternedIntersectionRows.Accepts value term := by
  rw [productive, SourceRowsMinimumPublic.productive_exact (heap state) fuel (reference value) raw done]
  exact exists_congr (fun term => language_exact state facts value available plain term)

/-- Actual minimum lookup computes the least node count of the physical root's accepted language. -/
theorem minimum_exact (state : State Symbol Unit) (facts : Facts state) (value : Value Symbol Unit)
    (available : Available state value) (plain : Plain value) (fuel : Nat)
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Unit)))
    (done : SourceInternedRows.toRows (heap state) fuel (reference value) = some raw) (size : Nat) :
    SourceRowsMinimumAdapter.minimumSizes raw (encode value) = some size ↔
      (∃ term, SourceInternedIntersectionRows.Accepts value term ∧ RecursiveSize.nodeSize term = size) ∧
      (∀ term, SourceInternedIntersectionRows.Accepts value term → size ≤ RecursiveSize.nodeSize term) := by
  have language : ∀ term, Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true))
      (SourceInternedRows.stateOf (reference value)) term ↔ SourceInternedIntersectionRows.Accepts value term :=
    language_exact state facts value available plain
  unfold encode
  rw [SourceRowsMinimumPublic.minimum_root_exact (heap state) fuel (reference value) raw done size]
  simp only [language]

/-- A completed actual dispatched result gives an exact shared-row common-term callback. -/
theorem dispatch_callback [DecidableEq Symbol] (pair : Value Symbol Unit × Value Symbol Unit)
    (plain : Plain pair.1 ∧ Plain pair.2) (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) :
    let result := run (SourceInternedIntersectionDispatch.dispatch (SourceInternedIntersectionDispatch.bound pair) pair) state
    ∃ fuel raw minimumFuel,
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap result.2) larger (reference result.1) = some raw) ∧
      MinimumSize.sweeps (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) =
        SourceRowsMinimumAdapter.minimumSizes raw ∧
      (productive result.2 result.1 raw = true ↔ ∃ term,
        Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode pair.1) term ∧
        Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode pair.2) term) := by
  let result := run (SourceInternedIntersectionDispatch.dispatch (SourceInternedIntersectionDispatch.bound pair) pair) state
  have checked := SourceInternedIntersectionDispatch.finite_exact pair plain.1 plain.2 state facts inputs
  obtain ⟨fuel, raw, minimumFuel, done, minimum, _⟩ := finite result.2 checked.1 result.1 checked.2.1
  refine ⟨fuel, raw, minimumFuel, done, minimum, ?_⟩
  rw [productive_exact result.2 checked.1 result.1 checked.2.1 checked.2.2.1 fuel raw (done fuel (Nat.le_refl _))]
  apply exists_congr
  intro term
  exact (checked.2.2.2 term).trans (and_congr
    (language_exact state facts pair.1 inputs.1 plain.1 term).symm
    (language_exact state facts pair.2 inputs.2 plain.2 term).symm)

/-- The callback after a completed native memo hit or miss needs no global child-meet assignment. -/
theorem native_callback [DecidableEq Symbol] (bits : Nat)
    (domain : Cache.Interned IntersectionFlatMemoKeyDomain.DomainKey)
    (pair : Value Symbol Unit × Value Symbol Unit) (plain : Plain pair.1 ∧ Plain pair.2)
    (state : State Symbol Unit) (facts : Facts state) (inputs : Inputs state pair) (supply : state.nodes.next < 2 ^ bits)
    (memo : Cache.Table (IntersectionFlatMemoKeyDomain.Triple (bits + 2)) (Value Symbol Unit))
    (valid : SourceInternedIntersectionDispatch.NativeValid (bits + 2) domain state memo) :
    let result := SourceInternedIntersectionDispatch.nativeRun (bits + 2) domain pair state memo
    ∃ fuel raw minimumFuel,
      (∀ larger, fuel ≤ larger → SourceInternedRows.toRows (heap result.2.1) larger (reference result.1) = some raw) ∧
      MinimumSize.sweeps (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) =
        SourceRowsMinimumAdapter.minimumSizes raw ∧
      (productive result.2.1 result.1 raw = true ↔ ∃ term,
        Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode pair.1) term ∧
        Language.Accepts (SourceInternedRows.graph (heap state) (fun _ _ => true)) (encode pair.2) term) := by
  let result := SourceInternedIntersectionDispatch.nativeRun (bits + 2) domain pair state memo
  have checked := SourceInternedIntersectionDispatch.nativeRun_correct bits domain pair plain state facts inputs supply memo valid
  have available := checked.2.2.2.2.1
  have resultPlain := checked.2.2.2.2.2.1
  have exact := checked.2.2.2.2.2.2
  obtain ⟨fuel, raw, minimumFuel, done, minimum, _⟩ := finite result.2.1 checked.1 result.1 available
  refine ⟨fuel, raw, minimumFuel, done, minimum, ?_⟩
  rw [productive_exact result.2.1 checked.1 result.1 available resultPlain fuel raw (done fuel (Nat.le_refl _))]
  apply exists_congr
  intro term
  exact (exact term).trans (and_congr
    (language_exact state facts pair.1 inputs.1 plain.1 term).symm
    (language_exact state facts pair.2 inputs.2 plain.2 term).symm)

end MicroCFTA.SourcePhysicalSharedRows
