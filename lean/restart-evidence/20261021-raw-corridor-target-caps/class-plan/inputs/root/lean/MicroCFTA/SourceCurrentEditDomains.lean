import MicroCFTA.SourceCurrentRequiredEndpoints
import MicroCFTA.SourceEqualityEditCompiledPaths

/-!
# Path domains for the actual simultaneous-edit trie

Each entered edit subtree has a retained callback. The path domain checks
only the original children selected by those callbacks. An empty child map
does not supply a node identity rule. Unselected children can remain open.
-/
namespace MicroCFTA.SourceCurrentEditDomains
open Language InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceEqualityNeededMap
open SourceEqualityProjectionPathDomain SourceEqualityProjectionGraph

/-- A retained callback occurs below this edit root. -/
def HasLeaf (edits : Edits Action) : Prop := ∃ path action, (path, action) ∈ leaves edits

/-- Every stored child has a callback and satisfies the same condition. -/
def Populated : Edits Action → Prop
  | .editAt _ => True
  | .editBelow entries => ∀ index child, (index, child) ∈ entries → Populated child ∧ HasLeaf child
termination_by edits => sizeOf edits
decreasing_by
  have smaller := List.sizeOf_lt_of_mem ‹(index, child) ∈ entries›
  simp only [Prod.mk.sizeOf_spec, Edits.editBelow.sizeOf_spec] at *
  omega

/-- Every retained full edit path has its selected projection domain. -/
def Safe (edits : Edits Action) (value : Value Symbol Guard) : Prop :=
  ∀ path action, (path, action) ∈ leaves edits → NodeClosed path value

/-- Child scans retain the source offset and each actual signed lookup. -/
def ChildrenSafe (entries : List (Int × Edits Action)) (offset : Nat) (values : List (Value Symbol Guard)) : Prop :=
  ∀ query child, lookup (Int.ofNat (offset + query)) entries = some child →
    ∀ value, values[query]? = some value → Safe child value

/-- Every original row supplies the selected child domains. -/
def RowsSafe (entries : List (Int × Edits Action)) (edges : List (EdgeValue Symbol Guard)) : Prop :=
  ∀ edge ∈ edges, ChildrenSafe entries 0 edge.children

/-- Node transport preserves each finite signed path domain. -/
def Transport (value result : Value Symbol Guard) : Prop :=
  ∀ path, NodeClosed path value → NodeClosed path result

/-- Insertion always leaves a callback, including an existing ancestor callback. -/
theorem insert_hasLeaf (path : Path) (action : Action) (edits : Edits Action) (valid : Valid edits) :
    HasLeaf (insert path action edits) := by
  induction path generalizing edits with
  | nil => exact ⟨[], action, by simp [SourceEqualityEdits.insert, leaves]⟩
  | cons index path ih =>
      cases edits with
      | editAt previous => exact ⟨[], previous, by simp [SourceEqualityEdits.insert, leaves]⟩
      | editBelow entries =>
          rw [SourceEqualityEdits.Valid] at valid
          have previous : Valid ((lookup index entries).getD empty) := by
            cases found : lookup index entries with
            | none => exact empty_valid
            | some child => exact valid.2 _ _ (lookup_mem _ _ _ found)
          obtain ⟨suffix, target, member⟩ := ih _ previous
          have childMember : (index, insert path action ((lookup index entries).getD empty)) ∈
              alter index (fun old => insert path action (old.getD empty)) entries :=
            lookup_mem _ _ _ (by rw [lookup_alter _ _ _ _ valid.1]; simp)
          exact ⟨index :: suffix, target, below_member _ _ _ childMember _ _ member⟩

/-- Actual insertion retains populated child subtrees. -/
theorem insert_populated (path : Path) (action : Action) (edits : Edits Action)
    (valid : Valid edits) (populated : Populated edits) : Populated (insert path action edits) := by
  induction path generalizing edits with
  | nil => simp only [SourceEqualityEdits.insert, Populated]
  | cons index path ih =>
      cases edits with
      | editAt previous => simp only [SourceEqualityEdits.insert, Populated]
      | editBelow entries =>
          rw [SourceEqualityEdits.Valid] at valid
          rw [Populated] at populated
          have previousValid : Valid ((lookup index entries).getD empty) := by
            cases found : lookup index entries with
            | none => exact empty_valid
            | some child => exact valid.2 _ _ (lookup_mem _ _ _ found)
          have previousPopulated : Populated ((lookup index entries).getD empty) := by
            cases found : lookup index entries with
            | none => simp [SourceEqualityEdits.empty, Populated]
            | some child => exact (populated _ _ (lookup_mem _ _ _ found)).1
          rw [SourceEqualityEdits.insert, Populated]
          exact alter_all index (fun old => SourceEqualityEdits.insert path action (old.getD empty)) entries (fun child => Populated child ∧ HasLeaf child)
            populated ⟨ih _ previousValid previousPopulated, insert_hasLeaf _ _ _ previousValid⟩ valid.1

/-- The actual source compiler never stores an empty edit subtree. -/
theorem build_populated (pairs : List (Path × Action)) : Populated (build pairs) := by
  induction pairs with
  | nil => simp [build, SourceEqualityEdits.empty, Populated]
  | cons pair rest ih => exact insert_populated _ _ _ (build_valid rest) ih

/-- A nonempty input edit list retains at least one callback. -/
theorem build_hasLeaf (pairs : List (Path × Action)) (nonempty : pairs ≠ []) : HasLeaf (build pairs) := by
  cases pairs with
  | nil => exact False.elim (nonempty rfl)
  | cons pair rest => exact insert_hasLeaf _ _ _ (build_valid rest)

/-- Natural selection is the actual signed lookup used by projection. -/
theorem select_natural (values : List A) (index : Nat) : select values (Int.ofNat index) = values[index]? := by
  simp only [select, Int.ofNat_eq_natCast]
  rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg index))]
  rfl

/-- Original row domains pass to the exact selected edit child. -/
theorem ordinary_rows {entries : List (Int × Edits Action)} {entry edges depth free}
    (safe : Safe (.editBelow entries) (.node entry edges depth free : Value Symbol Guard)) : RowsSafe entries edges := by
  intro edge member query child found value selected path action retained
  have original := safe (Int.ofNat query :: path) action
    (below_member entries _ child (lookup_mem _ _ _ (by simpa using found)) path action retained)
  rw [NodeClosed] at original
  exact original edge member value (by simpa only [select_natural] using selected)

/-- The next original child retains the exact source offset. -/
theorem children_tail {entries : List (Int × Edits Action)} {offset : Nat} {value values}
    (safe : ChildrenSafe entries offset (value :: values : List (Value Symbol Guard))) : ChildrenSafe entries (offset + 1) values := by
  intro query child found original selected
  exact safe (query + 1) child (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found) original selected

/-- A recursive input with one certified retained path is closed. -/
theorem recursive_closed {edits : Edits Action} {value : Value Symbol Guard}
    (recursive : SourceEqualityRequiredGraph.Recursive value) (nonempty : HasLeaf edits) (safe : Safe edits value) :
    value.free = [] := by
  obtain ⟨path, action, retained⟩ := nonempty
  have domain := safe path action retained
  cases value <;> cases path <;> simp_all only [SourceEqualityRequiredGraph.Recursive, NodeClosed]

/-- A closed available value satisfies every retained edit-path domain. -/
theorem closed_safe [DecidableEq (EdgeKey Symbol Guard)] (edits : Edits Action) (value : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state)
    (available : Available state value) (closed : value.free = []) : Safe edits value := by
  intro path _ _
  exact SourceCurrentRequiredEndpoints.closed_path path value state semantic available closed

/-- Aligned child transport retains any selected signed path domain. -/
theorem transport_get {values results : List (Value Symbol Guard)} (aligned : All₂ Transport values results)
    (index : Nat) (path : List Int)
    (domain : ∀ value, values[index]? = some value → NodeClosed path value) :
    ∀ result, results[index]? = some result → NodeClosed path result := by
  induction aligned generalizing index with
  | nil => intro result found; cases found
  | cons first rest ih =>
      cases index with
      | zero => intro result found; cases found; exact first path (domain _ rfl)
      | succ index => exact ih index domain

/-- Aligned child transport retains the whole forest path domain. -/
theorem transport_forest {values results : List (Value Symbol Guard)} (aligned : All₂ Transport values results)
    (path : List Int) (domain : ForestClosed path values) : ForestClosed path results := by
  cases path with
  | nil =>
      induction aligned with
      | nil => intro value member; cases member
      | cons first rest ih =>
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · simpa only [NodeClosed] using first [] (by simpa only [NodeClosed] using domain _ List.mem_cons_self)
          · exact ih (fun child included => domain child (List.mem_cons_of_mem _ included)) value member
  | cons index path =>
      by_cases negative : index < 0
      · simp only [ForestClosed, select, negative, ite_true, reduceCtorEq, false_implies, implies_true]
      · intro result found
        have selected : results[index.toNat]? = some result := by simpa only [select, negative, ite_false] using found
        exact transport_get aligned index.toNat path
          (fun value original => domain value (by simpa only [select, negative, ite_false] using original)) result selected

end MicroCFTA.SourceCurrentEditDomains
