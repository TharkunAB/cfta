import MicroCFTA.SourceSizedConjunctionClosure

/-!
# Decorated canonical rows after conjunction exploration

The source puts equality classes in the symbol before canonical sorting.
It restores only the symbol's first component after sorting. The original
class payload and ordered children remain in each row. Successful preparation
supplies the root, distinct keys, and child closure used by validation.
Native Map/Set representation and machine arithmetic remain separate.
-/
namespace MicroCFTA.SourceSizedConjunctionSorted
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows Std
open SourceSizedConjunctionWorklist
attribute [local instance] lexOrd

variable {Key State Symbol : Type}

/-- Include the equality classes in the symbol read by canonical refinement. -/
def decorate (row : Row Key Symbol (List (List Nat))) :
    Row Key (Symbol × List (List Nat)) (List (List Nat)) :=
  ⟨(row.label, row.constraint), row.children, row.constraint⟩

/-- Remove only the temporary symbol decoration after sorting. -/
def restore (row : Row Key (Symbol × List (List Nat)) (List (List Nat))) :
    Row Key Symbol (List (List Nat)) :=
  ⟨row.label.1, row.children, row.constraint⟩

/-- Decoration and restoration preserve the complete original row. -/
theorem restore_decorate (row : Row Key Symbol (List (List Nat))) :
    restore (decorate row) = row := by cases row; rfl

/-- Decorate every row without changing entry or alternative order. -/
def decorateTable (table : Table Key Symbol (List (List Nat))) :
    Table Key (Symbol × List (List Nat)) (List (List Nat)) :=
  table.map fun entry => (entry.1, entry.2.map decorate)

/-- Decoration preserves every key occurrence in its original position. -/
theorem decorated_key_sequence (table : Table Key Symbol (List (List Nat))) :
    (decorateTable table).map Prod.fst = table.map Prod.fst := by
  simp only [decorateTable, List.map_map, Function.comp_def]

/-- Merged lookup retains the exact original row order under decoration. -/
theorem decorated_lookup [DecidableEq Key]
    (table : Table Key Symbol (List (List Nat))) (key : Key) :
    lookup (decorateTable table) key = (lookup table key).map decorate := by
  simp only [lookup, decorateTable, List.flatMap_map, List.map_flatMap]
  apply TablePosition.flatMap_congr
  intro entry _
  by_cases same : entry.1 = key <;> simp [same]

/-- The original finite key inventory is unchanged by decoration. -/
theorem decorated_keys [DecidableEq Key] [Ord Key]
    (table : Table Key Symbol (List (List Nat))) :
    SourceDenseRows.keys (decorateTable table) = SourceDenseRows.keys table := by
  unfold SourceDenseRows.keys
  rw [decorated_key_sequence]

section Prepared
variable [DecidableEq State] [Ord State] [Ord (List State)] [DecidableEq Symbol]

/-- Actual successful preparation supplies closure of all decorated rows. -/
theorem decorated_closed (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    Closed (decorateTable returned) := by
  intro owner row present child childIn
  rw [decorated_lookup] at present
  obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp present
  rw [decorated_keys]
  exact SourceSizedConjunctionClosure.prepare_closed classified root returned success
    owner original originalIn child childIn

/-- Current structural validation accepts the actual decorated prepared table. -/
theorem validation_succeeds (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    SourceFTAValidation.validateRows [root] (interpreted (decorateTable returned) (fun _ _ => true)) =
      .ok (interpreted (decorateTable returned) (fun _ _ => true)) := by
  apply SourceSizedStructuralKeys.validation_of_closed
  · rw [decorated_keys]
    exact SourceSizedConjunctionClosure.prepare_root_keys classified root returned success
  · exact decorated_closed classified root returned success

/-- The literal current FTA constructor has no error at the decorated output. -/
theorem mkFTA_succeeds (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    SourceFTAValidation.mkFTA [root] (interpreted (decorateTable returned) (fun _ _ => true)) =
      .ok (FTAValidation.normalizeRows (interpreted (decorateTable returned) (fun _ _ => true))) :=
  (SourceFTAValidation.mkFTA_exact [root] _).mpr
    ((SourceFTAValidation.validateRows_exact [root] _).mp
      (validation_succeeds classified root returned success))

/-- Derive the complete finite canonical input from the actual preparation result. -/
def input (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :=
  SourceSizedStructuralKeys.input (decorateTable returned) [root]
    (validation_succeeds classified root returned success)

variable [Ord Symbol]

/-- Canonically sort decorated rows, then restore each original symbol. -/
def sortedRows (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    List State → List (Row (List State) Symbol (List (List Nat))) :=
  fun key =>
    (SourceSizedStructuralKeys.nativeSorted (decorateTable returned) [root]
      (validation_succeeds classified root returned success) key).map restore

/-- The sort uses the actual decorated canonical classes and complete row keys. -/
theorem sorted_exact (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) :
    sortedRows classified root returned success key =
      (((lookup returned key).map decorate).mergeSort fun first second =>
        (compare
          (SourceSizedPreprocessing.rowKey
            (SourceSizedStructuralKeys.classOf (decorateTable returned) [root]
              (validation_succeeds classified root returned success)) first)
          (SourceSizedPreprocessing.rowKey
            (SourceSizedStructuralKeys.classOf (decorateTable returned) [root]
              (validation_succeeds classified root returned success)) second)).isLE).map restore := by
  unfold sortedRows SourceSizedStructuralKeys.nativeSorted
  rw [decorated_lookup]

/-- Every sorted row still carries the same classes in its decoration and payload. -/
theorem sorted_payload (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) (row : Row (List State) (Symbol × List (List Nat)) (List (List Nat)))
    (present : row ∈ SourceSizedStructuralKeys.nativeSorted (decorateTable returned) [root]
      (validation_succeeds classified root returned success) key) :
    row.label.2 = row.constraint := by
  have original := (SourceSizedStructuralKeys.nativeSorted_perm (decorateTable returned) [root]
    (validation_succeeds classified root returned success) key).mem_iff.mp present
  rw [decorated_lookup] at original
  obtain ⟨before, _, rfl⟩ := List.mem_map.mp original
  rfl

/-- Sorting and symbol restoration permute complete rows without changing payloads or children. -/
theorem sorted_permutation (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) :
    (sortedRows classified root returned success key).Perm (lookup returned key) := by
  have permutation := (SourceSizedStructuralKeys.nativeSorted_perm (decorateTable returned) [root]
    (validation_succeeds classified root returned success) key).map restore
  rw [decorated_lookup] at permutation
  have cancel : ((lookup returned key).map decorate).map restore = lookup returned key := by
    rw [List.map_map]
    change (lookup returned key).map id = lookup returned key
    exact List.map_id _
  rw [cancel] at permutation
  exact permutation

/-- Finite restriction, decorated canonical sorting, and restoration have exact readback. -/
theorem sorted_readback [TransOrd (Symbol × List (List Nat))]
    [LawfulEqOrd (Symbol × List (List Nat))]
    (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : Member (SourceDenseRows.keys (decorateTable returned))) :
    (SourceSizedPreprocessing.sortedRows (input classified root returned success) key).map
      (fun row => restore (forget row)) = sortedRows classified root returned success key.val := by
  have readback := SourceSizedStructuralKeys.sorted_readback (decorateTable returned) [root]
    (validation_succeeds classified root returned success) key
  have mapped := congrArg
    (fun rows : List (Row (List State) (Symbol × List (List Nat)) (List (List Nat))) => rows.map restore)
    readback
  simpa only [List.map_map, Function.comp_def, input, sortedRows] using mapped

/-- Return the sorted row lists under the original stored map keys. -/
def sortedTable (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    Stored State Symbol :=
  (returned.map Prod.fst).map fun key => (key, sortedRows classified root returned success key)

/-- Final symbol restoration and row sorting retain the whole key sequence. -/
theorem sortedTable_key_sequence (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    (sortedTable classified root returned success).map Prod.fst = returned.map Prod.fst := by
  rw [sortedTable, List.map_map]
  change (returned.map Prod.fst).map id = returned.map Prod.fst
  exact List.map_id _

private theorem lookup_map {Key Value : Type} [DecidableEq Key]
    (items : List Key) (distinct : items.Nodup) (rows : Key → List Value) (key : Key) :
    (items.map (fun item => (item, rows item))).flatMap (fun entry =>
      if entry.1 = key then entry.2 else []) = if key ∈ items then rows key else [] := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have fresh := List.nodup_cons.mp distinct
      simp only [List.map_cons, List.flatMap_cons]
      rw [ih fresh.2]
      by_cases same : item = key
      · subst key; simp [fresh.1]
      · simp [same, Ne.symm same]

private theorem lookup_empty {Key Label Payload : Type} [DecidableEq Key]
    (table : Table Key Label Payload) (key : Key) :
    key ∉ table.map Prod.fst → lookup table key = [] := by
  induction table with
  | nil => intro _; rfl
  | cons entry rest ih =>
      intro absent
      have different : entry.1 ≠ key := by
        intro same
        exact absent (List.mem_map.mpr ⟨entry, by simp, same⟩)
      have later : key ∉ rest.map Prod.fst := by
        intro present
        exact absent (by simp [present])
      simpa only [lookup, List.flatMap_cons, ite_eq_right different, List.nil_append] using ih later

/-- Distinct keys derived from preparation give exact final lookup, including absent keys. -/
theorem sortedTable_lookup (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned)
    (key : List State) :
    lookup (sortedTable classified root returned success) key =
      sortedRows classified root returned success key := by
  unfold sortedTable lookup
  rw [lookup_map _ (prepare_ready classified root returned success).distinct]
  by_cases present : key ∈ returned.map Prod.fst
  · rw [ite_eq_left present]
  · rw [ite_eq_right present]
    have originalEmpty := lookup_empty returned key present
    have permutation := sorted_permutation classified root returned success key
    rw [originalEmpty] at permutation
    symm
    exact List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using permutation.length_eq)

/-- Final lookup has exactly the original key inventory. -/
theorem sortedTable_keys (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    SourceDenseRows.keys (sortedTable classified root returned success) = SourceDenseRows.keys returned := by
  unfold SourceDenseRows.keys
  rw [sortedTable_key_sequence]

/-- The final table retains child closure derived from actual exploration. -/
theorem sortedTable_closed (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    Closed (sortedTable classified root returned success) := by
  intro owner row present child childIn
  rw [sortedTable_lookup] at present
  have original := (sorted_permutation classified root returned success owner).mem_iff.mp present
  rw [sortedTable_keys]
  exact SourceSizedConjunctionClosure.prepare_closed classified root returned success
    owner row original child childIn

/-- Current structural validation accepts the final restored sorted table. -/
theorem sortedTable_validation (classified : Classified State Symbol) (root : State)
    (returned : Stored State Symbol) (success : prepare classified root = .ready returned) :
    SourceFTAValidation.validateRows [root]
      (interpreted (sortedTable classified root returned success) (fun _ _ => true)) =
      .ok (interpreted (sortedTable classified root returned success) (fun _ _ => true)) := by
  apply SourceSizedStructuralKeys.validation_of_closed
  · rw [sortedTable_keys]
    exact SourceSizedConjunctionClosure.prepare_root_keys classified root returned success
  · exact sortedTable_closed classified root returned success

end Prepared
end MicroCFTA.SourceSizedConjunctionSorted
