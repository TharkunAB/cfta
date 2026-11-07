import MicroCFTA.SourceSizedScopedErasure

/-!
# The actual scoped trim inventory and row scan

The inventory filters the original map keys. It retains the root entry
even when the root has no productive row. Every retained raw row has
an owner in this inventory. Scanning the original keys or the trimmed
table therefore gives the same plainness result.

The explicit trimmed table retains key order and each row's order and
payload. These facts need no global plainness or uniform symbol arity.
-/
namespace MicroCFTA.SourceSizedScopedTrimInventory
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

/-- Read exactly the original keys retained by root-preserving structural trim. -/
def inventory (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) : List State :=
  SourceSizedDecidedTrim.trimKeys (keys table) (SourceSizedDeterminizationTableInput.rows table) root

/-- Every inventory state is an original declared key. -/
theorem inventory_subset (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) :
    inventory table root ⊆ keys table := by
  intro state member
  exact (List.mem_filter.mp member).1

/-- Trimming retains the relative order of the original map keys. -/
theorem inventory_sublist (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) :
    (inventory table root).Sublist (keys table) :=
  List.filter_sublist

/-- Each retained key occurs once. -/
theorem inventory_nodup (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) :
    (inventory table root).Nodup :=
  (keys_nodup table).filter _

/-- A retained raw row derives its owner membership in the scoped inventory. -/
theorem row_owner (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root state : State)
    (row : Row State Symbol Payload)
    (member : row ∈ SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state) :
    state ∈ inventory table root := by
  unfold SourceSizedTrimGuards.trimmedRows at member
  split at member
  next retained =>
    have stored := (List.mem_filter.mp member).1
    have owner : state ∈ keys table :=
      SourceSizedDeterminizationTableInput.rows_supported table state
        (row.edge (fun _ _ => true)) (List.mem_map.mpr ⟨row, stored, rfl⟩)
    have flags := Bool.and_eq_true_iff.mp retained
    apply List.mem_filter.mpr
    refine ⟨owner, ?_⟩
    apply Bool.or_eq_true_iff.mpr
    exact Or.inr (Bool.and_eq_true_iff.mpr ⟨flags.2, flags.1⟩)
  next => simp at member

/-- States outside the inventory have no retained raw row. -/
theorem rows_empty_outside (table : SourceSizedFiniteKeys.Table State Symbol Payload)
    (root state : State) (outside : state ∉ inventory table root) :
    SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro row member
  exact outside (row_owner table root state row member)

/-- The original-key scan equals the scan of just the actual trimmed keys. -/
theorem plainCheck_eq [DecidableEq Payload]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) (neutral : Payload) :
    SourceSizedScopedErasure.plainCheck table root neutral =
      (inventory table root).all (fun state =>
        (SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state).all
          fun row => decide (row.constraint = neutral)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro passed
    apply List.all_eq_true.mpr
    intro state member
    exact List.all_eq_true.mp passed state (inventory_subset table root member)
  · intro passed
    apply List.all_eq_true.mpr
    intro state _
    apply List.all_eq_true.mpr
    intro row member
    exact List.all_eq_true.mp
      (List.all_eq_true.mp passed state (row_owner table root state row member)) row member

/-- Store every retained key with its complete trimmed raw alternative list. -/
def trimmedTable (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) :
    SourceSizedFiniteKeys.Table State Symbol Payload :=
  (inventory table root).map fun state =>
    (state, SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state)

/-- The explicit trimmed table retains exactly the scoped key sequence. -/
theorem trimmedTable_keys (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) :
    (trimmedTable table root).map Prod.fst = inventory table root := by
  simp only [trimmedTable, List.map_map, Function.comp_def]
  change (inventory table root).map id = inventory table root
  exact List.map_id _

private theorem lookup_map {Key Value : Type} [DecidableEq Key]
    (items : List Key) (distinct : items.Nodup) (rows : Key → List Value) (state : Key) :
    (items.map (fun key => (key, rows key))).flatMap (fun entry =>
      if entry.1 = state then entry.2 else []) = if state ∈ items then rows state else [] := by
  induction items with
  | nil => simp
  | cons key rest ih =>
    have fresh := List.nodup_cons.mp distinct
    simp only [List.map_cons, List.flatMap_cons]
    rw [ih fresh.2]
    by_cases same : key = state
    · subst state
      simp [fresh.1]
    · simp [same, Ne.symm same]

/-- Trimmed-table lookup is exact at every state, including outside its key inventory. -/
theorem trimmed_lookup (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root state : State) :
    lookup (trimmedTable table root) state =
      SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state := by
  let trimmed := SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root
  change ((inventory table root).map (fun key => (key, trimmed key))).flatMap
    (fun entry => if entry.1 = state then entry.2 else []) = trimmed state
  rw [lookup_map _ (inventory_nodup table root)]
  by_cases present : state ∈ inventory table root
  · rw [ite_eq_left present]
  · rw [ite_eq_right present]
    exact (rows_empty_outside table root state present).symm

/-- Scanning the actual trimmed table rows gives the scoped source precheck. -/
theorem plainCheck_table [DecidableEq Payload]
    (table : SourceSizedFiniteKeys.Table State Symbol Payload) (root : State) (neutral : Payload) :
    SourceSizedScopedErasure.plainCheck table root neutral =
      (trimmedTable table root).all (fun entry => entry.2.all fun row => decide (row.constraint = neutral)) := by
  rw [plainCheck_eq, trimmedTable, List.all_map]
  rfl

end MicroCFTA.SourceSizedScopedTrimInventory
