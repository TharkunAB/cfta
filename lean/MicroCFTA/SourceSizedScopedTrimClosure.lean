import MicroCFTA.SourceSizedScopedTrimInventory
import MicroCFTA.SourceSizedDecidedOrder

/-!
# Structural closure of the actual scoped trimmed table

Every child of a retained row belongs to the actual trimmed inventory.
The proof restricts the original table to its finite declared keys and
transports the retained rows and trim keys in their original order.
The raw state type need not be finite.

Current structural validation supplies the original child closure and
root membership. The final trimmed table then passes that same validator.
No uniform symbol arity or global guard condition is required.
-/
namespace MicroCFTA.SourceSizedScopedTrimClosure
open Language SourceSizedDecided SourceSizedFiniteKeys SourceDenseRows
open SourceSizedScopedTrimInventory

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]

private theorem finite_child {Key : Type} [DecidableEq Key]
    (rows : Key → List (Row Key Symbol Payload)) (nodes : List Key)
    (complete : ∀ state, state ∈ nodes) (root state : Key) (row : Row Key Symbol Payload)
    (member : row ∈ SourceSizedTrimGuards.trimmedRows rows nodes root state)
    (child : Key) (childIn : child ∈ row.children) :
    child ∈ SourceSizedDecidedTrim.trimKeys nodes (automaton rows (fun _ _ => true)) root := by
  unfold SourceSizedTrimGuards.trimmedRows at member
  split at member
  next retained =>
    have stored := (List.mem_filter.mp member).1
    have children := (List.mem_filter.mp member).2
    have flags := Bool.and_eq_true_iff.mp retained
    have included : state ∈
        SourceSizedDecidedTrim.trimKeys nodes (automaton rows (fun _ _ => true)) root := by
      apply List.mem_filter.mpr
      exact ⟨complete state, Bool.or_eq_true_iff.mpr
        (Or.inr (Bool.and_eq_true_iff.mpr ⟨flags.2, flags.1⟩))⟩
    exact SourceSizedDecidedOrder.trimKeys_live_children nodes complete
      (automaton rows (fun _ _ => true)) root state included (row.edge (fun _ _ => true))
      (List.mem_map.mpr ⟨row, stored, rfl⟩) children child childIn
  next => simp at member

/-- Every retained raw child belongs to the actual scoped inventory. -/
theorem child_mem (table : Table State Symbol Payload) (root : State)
    (closed : Closed table) (rootPresent : root ∈ keys table)
    (state : State) (row : Row State Symbol Payload)
    (member : row ∈ SourceSizedTrimGuards.trimmedRows (lookup table) (keys table) root state)
    (child : State) (childIn : child ∈ row.children) : child ∈ inventory table root := by
  let finiteRoot : Member (keys table) := ⟨root, rootPresent⟩
  let finiteState : Member (keys table) :=
    ⟨state, inventory_subset table root (row_owner table root state row member)⟩
  have readback : row ∈
      (SourceSizedTrimGuards.trimmedRows (restricted table closed) (keys table).attach
        finiteRoot finiteState).map forget := by
    rw [SourceSizedFiniteKeysTrim.trimmedRows_readback table closed finiteRoot finiteState]
    exact member
  obtain ⟨finiteRow, finiteMember, same⟩ := List.mem_map.mp readback
  have childReadback : child ∈ (forget finiteRow).children := by
    rw [same]
    exact childIn
  change child ∈ finiteRow.children.map Subtype.val at childReadback
  obtain ⟨finiteChild, finiteChildIn, sameChild⟩ := List.mem_map.mp childReadback
  have included := finite_child (restricted table closed) (keys table).attach
    (member_complete (keys table)) finiteRoot finiteState finiteRow finiteMember
    finiteChild finiteChildIn
  change child ∈ SourceSizedDecidedTrim.trimKeys (keys table)
    (automaton (lookup table) (fun _ _ => true)) root
  rw [SourceSizedFiniteKeysTrim.restricted_trimKeys table closed (fun _ _ => true) finiteRoot]
  exact List.mem_map.mpr ⟨finiteChild, included, sameChild⟩

/-- Original structural closure derives closure of the actual retained table. -/
theorem trimmed_closed (table : Table State Symbol Payload) (root : State)
    (closed : Closed table) (rootPresent : root ∈ keys table) :
    Closed (trimmedTable table root) := by
  intro state row member child childIn
  rw [trimmed_lookup] at member
  apply (mem_keys (trimmedTable table root) child).mpr
  rw [trimmedTable_keys]
  exact child_mem table root closed rootPresent state row member child childIn

/-- A declared root remains a key even when it has no productive row. -/
theorem trimmed_root (table : Table State Symbol Payload) (root : State)
    (rootPresent : root ∈ keys table) : root ∈ keys (trimmedTable table root) := by
  apply (mem_keys (trimmedTable table root) root).mpr
  rw [trimmedTable_keys]
  simp [inventory, SourceSizedDecidedTrim.trimKeys, rootPresent]

/-- The retained table passes the current root and dangling-child checks. -/
theorem trimmed_validation (table : Table State Symbol Payload) (root : State)
    (closed : Closed table) (rootPresent : root ∈ keys table) :
    SourceFTAValidation.validateRows root
        (interpreted (trimmedTable table root) (fun _ _ => true)) =
      .ok (interpreted (trimmedTable table root) (fun _ _ => true)) :=
  SourceSizedStructuralKeys.validation_of_closed (trimmedTable table root) root
    (trimmed_root table root rootPresent) (trimmed_closed table root closed rootPresent)

/-- Successful original structural validation derives successful scoped validation. -/
theorem validated_trimmed (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true))) :
    SourceFTAValidation.validateRows root
        (interpreted (trimmedTable table root) (fun _ _ => true)) =
      .ok (interpreted (trimmedTable table root) (fun _ _ => true)) :=
  trimmed_validation table root
    (SourceSizedStructuralKeys.validated_closed table root success)
    (SourceSizedStructuralKeys.validated_root table root success)

end MicroCFTA.SourceSizedScopedTrimClosure
