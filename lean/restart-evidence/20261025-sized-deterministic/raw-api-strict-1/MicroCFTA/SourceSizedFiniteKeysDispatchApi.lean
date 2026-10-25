import MicroCFTA.SourceSizedFiniteKeysDispatchScans

/-!
# Original-map Sized dispatch and query equality

The deterministic key check or finite key-pair minimum calculation supplies
the optimized gate.
Ordered row readback supplies each query sequence. These facts give exact
public dispatch equality for arbitrary original state types.
-/
namespace MicroCFTA.SourceSizedFiniteKeysDispatch
open Language RecursiveSize SizedRank SourceSizedDecided SourceSizedFiniteKeys SourceSizedDispatcher
open SourceSizedPreprocessing SourceDenseRows SourceObservations SourceSymbolicIndex

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- A successful raw finite-map gate gives distinct runs at every original state. -/
theorem raw_unique [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : unambiguous table root valid = true) :
    SizedRank.Unambiguous (ordinaryRows (nativeSorted table root valid)) := by
  have finiteUnique := SourceSizedDispatchGraph.gate_unique
    (ordinaryRows (sortedRows (input table root valid))) (ordinary_plain _)
    (input table root valid).states (input table root valid).complete
    (by rwa [← unambiguous_eq table root valid])
  intro state size
  by_cases member : state ∈ keys table
  · have same := SourceSizedDispatch.enumerate_ordered_rows
      (ordinaryRows (sortedRows (input table root valid))) (ordinaryRows (nativeSorted table root valid))
      Subtype.val (sorted_ordered table root valid (fun _ _ => true)) size ⟨state, member⟩
    rw [same]
    exact finiteUnique ⟨state, member⟩ size
  · have empty : ordinaryRows (nativeSorted table root valid) state = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro edge present
      exact member (sorted_supported table root valid (fun _ _ => true) state edge present)
    cases size <;> simp [RecursiveSize.enumerate, empty]

/-- Distinct complete run classes identify all optimized queries with the reference. -/
theorem optimized_of_unique [DecidableEq Alphabet]
    (rows : Automaton Carrier Alphabet) (plain : Decoder.Plain rows)
    (unique : SizedRank.Unambiguous rows) (root : Carrier) :
    optimizedApi rows root = referenceApi rows root :=
  optimizedApi_of_unique rows plain unique root

/-- The raw deterministic scan derives uniqueness on the original finite map keys. -/
theorem raw_deterministic_unique [DecidableEq Symbol] [Ord Symbol]
    [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (passed : SourceSizedDeterministic.bottomUpDeterministic
      (ordinaryRows (nativeSorted table root valid)) (keys table) = true) :
    SizedRank.Unambiguous (ordinaryRows (nativeSorted table root valid)) :=
  SourceSizedDeterministic.gate_unique _ (ordinary_plain _) (keys table)
    (sorted_supported table root valid (fun _ _ => true)) passed

/-- Canonical readback identifies the entire reference API, including signed queries. -/
theorem referenceApi_eq [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (holds : Payload → Term Symbol → Bool) :
    referenceApi (automaton (nativeSorted table root valid) holds) root =
      referenceApi (automaton (sortedRows (input table root valid)) holds) (input table root valid).root := by
  have same : (fun size => SourceSizedReference.classes (automaton (nativeSorted table root valid) holds) size root) =
      (fun size => SourceSizedReference.classes (automaton (sortedRows (input table root valid)) holds) size (input table root valid).root) := by
    funext size
    exact (sorted_classes_exact table root valid holds (input table root valid).root size).symm
  unfold referenceApi
  rw [same]

/-- A successful source product-minimum gate identifies all four actual optimized queries. -/
theorem optimizedApi_eq [DecidableEq Symbol] [Ord Symbol] [Std.TransOrd Symbol] [Std.LawfulEqOrd Symbol]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State)
    (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) (passed : unambiguous table root valid = true) :
    optimizedApi (ordinaryRows (nativeSorted table root valid)) root =
      optimizedApi (ordinaryRows (sortedRows (input table root valid))) (input table root valid).root := by
  rw [optimized_of_unique _ (ordinary_plain _) (raw_unique table root valid passed),
    optimizedApi_eq_reference _ (ordinary_plain _) (input table root valid).states
      (input table root valid).complete (by rwa [← unambiguous_eq table root valid])]
  exact referenceApi_eq table root valid (fun _ _ => true)

variable [DecidableEq Formula] [Ord (Label Formula)] [Std.TransOrd (Label Formula)] [Std.LawfulEqOrd (Label Formula)]
  (table : SourceSizedFiniteKeys.Table State (Label Formula) (Constraint Formula)) (root : State)
  (valid : FTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
    .ok (interpreted table (fun _ _ => true)))

/-- The raw public reference scans the original map and reads its canonical rows. -/
noncomputable def nativeReference : Except Unit (Api (Label Formula)) :=
  if residualCheck (lookup table) (keys table) root then
    .ok (referenceApi (equalityRows (nativeSorted table root valid)) root)
  else .error ()

/-- The raw source dispatcher checks deterministic keys before the product minimum table. -/
noncomputable def nativeSized : Except Unit (Api (Label Formula)) :=
  if plainCheck (lookup table) (keys table) &&
      (SourceSizedDeterministic.bottomUpDeterministic
        (ordinaryRows (nativeSorted table root valid)) (keys table) || unambiguous table root valid) then
    .ok (optimizedApi (ordinaryRows (nativeSorted table root valid)) root)
  else nativeReference table root valid

/-- The actual original-map fallback has the same reference error and all four query functions. -/
theorem nativeReference_eq : nativeReference table root valid = publicReference (input table root valid) := by
  unfold nativeReference publicReference
  rw [residual_eq table root valid]
  split
  · congr 1
    exact referenceApi_eq table root valid SourceSizedEqualities.constraintHolds
  · rfl

/-- Actual raw-map dispatch has the same complete query record and error as the public adapter. -/
theorem nativeSized_eq : nativeSized table root valid = publicSized (input table root valid) := by
  rw [publicSized_eq_reference, ← nativeReference_eq]
  unfold nativeSized
  split
  · rename_i passed
    have both : plainCheck (lookup table) (keys table) = true ∧
        (SourceSizedDeterministic.bottomUpDeterministic
          (ordinaryRows (nativeSorted table root valid)) (keys table) = true ∨
            unambiguous table root valid = true) := by
      simpa only [Bool.and_eq_true, Bool.or_eq_true] using passed
    have unique : SizedRank.Unambiguous (ordinaryRows (nativeSorted table root valid)) := by
      rcases both.2 with deterministic | product
      · exact raw_deterministic_unique table root valid deterministic
      · exact raw_unique table root valid product
    have plain : plainCheck (input table root valid).rows (input table root valid).states = true := by
      rwa [← plain_eq table root valid]
    have residual : residualCheck (lookup table) (keys table) root = true := by
      rw [residual_eq table root valid]
      exact plain_residual _ _ (input table root valid).complete _ plain
    rw [nativeReference, residual]
    apply congrArg Except.ok
    rw [optimized_of_unique _ (ordinary_plain _) unique,
      referenceApi_eq table root valid (fun _ _ => true),
      referenceApi_eq table root valid SourceSizedEqualities.constraintHolds,
      checked_rows _ _ (input table root valid).complete plain]
  · rfl

/-- Every successful raw dispatch uses the original canonical distinct-term sequence. -/
theorem native_success (api : Api (Label Formula))
    (success : nativeSized table root valid = .ok api) :
    residualCheck (lookup table) (keys table) root = true ∧
      api = referenceApi (equalityRows (nativeSorted table root valid)) root := by
  rw [nativeSized_eq] at success
  obtain ⟨passed, same⟩ := publicSized_success (input table root valid) api success
  refine ⟨?_, ?_⟩
  · rwa [residual_eq table root valid]
  · rw [same]
    exact (referenceApi_eq table root valid SourceSizedEqualities.constraintHolds).symm

end MicroCFTA.SourceSizedFiniteKeysDispatch
