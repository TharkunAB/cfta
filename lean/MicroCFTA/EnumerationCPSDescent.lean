import MicroCFTA.EnumerationCPSState
import MicroCFTA.EnumerationProgress

/-!
# Batched suspended-constraint descent

The source folds over obligations and appends each child entry to its bucket.
Every bucket retains input order and repetitions. A valid trie has distinct
child keys and no empty stored child. These invariants connect the batched
worker to the earlier per-child map/filter worker.
-/

namespace MicroCFTA.EnumerationCPSDescent

open EqualityTrie

variable {Variable : Type}

/-- The finite-map lookup interface; an absent child has an empty sequence. -/
abbrev Buckets (Variable : Type) := Nat → List (Suspended Variable)

/-- Append one obligation, as insertWith (flip append) does in the source. -/
def appendChild (buckets : Buckets Variable) (index : Nat) (trie : Trie) (var : Variable) : Buckets Variable :=
  fun child => if child = index then buckets child ++ [⟨trie, var⟩] else buckets child

/-- Traverse one trie child map in its stored key order. -/
def children (buckets : Buckets Variable) (entries : List (Nat × Trie)) (var : Variable) : Buckets Variable :=
  entries.foldl (fun built entry => appendChild built entry.1 entry.2 var) buckets

/-- The per-obligation source fold leaves terminals and empty tries out of all children. -/
def descend (buckets : Buckets Variable) (constraint : Suspended Variable) : Buckets Variable :=
  match constraint.trie with
  | .branch entries => children buckets entries constraint.var
  | .empty | .terminal => buckets

/-- The source outer fold processes each suspended obligation exactly once. -/
def batch (buckets : Buckets Variable) (constraints : List (Suspended Variable)) : Buckets Variable :=
  constraints.foldl descend buckets

/-- Read the contribution of one child map to a selected bucket. -/
def selected (index : Nat) (var : Variable) (entries : List (Nat × Trie)) : List (Suspended Variable) :=
  entries.filterMap fun entry => if index = entry.1 then some ⟨entry.2, var⟩ else none

/-- Folding one child map appends its selected entries in their original order. -/
theorem children_at (buckets : Buckets Variable) (entries : List (Nat × Trie)) (var : Variable) (index : Nat) :
    children buckets entries var index = buckets index ++ selected index var entries := by
  induction entries generalizing buckets with
  | nil => simp [children, selected]
  | cons entry rest ih =>
      obtain ⟨key, trie⟩ := entry
      simp only [children, List.foldl_cons]
      rw [show List.foldl (fun built entry => appendChild built entry.1 entry.2 var)
        (appendChild buckets key trie var) rest index =
          appendChild buckets key trie var index ++ selected index var rest from ih _]
      by_cases same : index = key <;> simp [appendChild, selected, same, List.append_assoc]

/-- A child map with no matching key contributes no suspended obligation. -/
theorem selected_nil (index : Nat) (var : Variable) (entries : List (Nat × Trie))
    (absent : index ∉ entries.map Prod.fst) : selected index var entries = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro entry member
  have different : index ≠ entry.1 := by
    intro same
    exact absent (List.mem_map.mpr ⟨entry, member, same.symm⟩)
  simp [different]

/-- A valid finite child map contributes the single entry returned by lookup. -/
theorem selected_lookup (index : Nat) (var : Variable) (entries : List (Nat × Trie))
    (unique : (entries.map Prod.fst).Nodup) :
    selected index var entries =
      match lookup index entries with | none => [] | some trie => [⟨trie, var⟩] := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, trie⟩ := entry
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      by_cases same : index = key
      · subst index
        have tailEmpty := selected_nil key var rest absent
        simpa only [selected, List.filterMap_cons, lookup, ite_true] using
          congrArg (⟨trie, var⟩ :: ·) tailEmpty
      · simpa [selected, lookup, same] using ih tailUnique

/-- One valid source obligation appends exactly its old per-child descent. -/
theorem descend_at (buckets : Buckets Variable) (constraint : Suspended Variable)
    (valid : Valid constraint.trie) (index : Nat) :
    descend buckets constraint index = buckets index ++ EqualityTrie.descendScs index [constraint] := by
  obtain ⟨trie, var⟩ := constraint
  cases trie with
  | empty => simp [descend, EqualityTrie.descendScs, pathTrieDescend, isEmpty]
  | terminal => simp [descend, EqualityTrie.descendScs, pathTrieDescend, isEmpty]
  | branch entries =>
      rw [Valid] at valid
      obtain ⟨nonempty, unique, validChildren⟩ := valid
      change children buckets entries var index =
        buckets index ++ EqualityTrie.descendScs index [⟨.branch entries, var⟩]
      rw [children_at, selected_lookup index var entries unique]
      cases found : lookup index entries with
      | none => simp [EqualityTrie.descendScs, pathTrieDescend, found, isEmpty]
      | some child =>
          have proper := (validChildren index child (lookup_mem index entries child found)).1
          cases child with
          | empty => exact False.elim (proper rfl)
          | terminal => simp [EqualityTrie.descendScs, pathTrieDescend, found, isEmpty]
          | branch children => simp [EqualityTrie.descendScs, pathTrieDescend, found, isEmpty]

/-- Each batch bucket equals its previous contents followed by exact ordered old descent. -/
theorem batch_at (buckets : Buckets Variable) (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) (index : Nat) :
    batch buckets constraints index = buckets index ++ EqualityTrie.descendScs index constraints := by
  induction constraints generalizing buckets with
  | nil => simp [batch, EqualityTrie.descendScs]
  | cons first rest ih =>
      simp only [batch, List.foldl_cons]
      rw [show List.foldl descend (descend buckets first) rest index =
        descend buckets first index ++ EqualityTrie.descendScs index rest from
          ih (descend buckets first) (fun constraint member => valid constraint (List.mem_cons_of_mem _ member))]
      rw [descend_at buckets first (valid first (by simp)) index]
      cases empty : isEmpty (pathTrieDescend first.trie index) <;>
        simp [EqualityTrie.descendScs, List.append_assoc, empty]

/-- Inherited and fresh obligations retain their exact concatenation order per child. -/
theorem inherited_then_new (inherited added : List (Suspended Variable))
    (oldValid : ∀ constraint ∈ inherited, Valid constraint.trie)
    (newValid : ∀ constraint ∈ added, Valid constraint.trie) (index : Nat) :
    batch (batch (fun _ => []) inherited) added index =
      EqualityTrie.descendScs index (inherited ++ added) := by
  rw [batch_at _ added newValid, batch_at _ inherited oldValid]
  simp [EqualityTrie.descendScs]

/-- Batched source descent retains exactly every suffix and its original equality variable. -/
theorem batch_exact (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) (index : Nat) (var : Variable) (suffix : Path) :
    (∃ constraint ∈ batch (fun _ => []) constraints index,
      constraint.var = var ∧ suffix ∈ fromPathTrie constraint.trie) ↔
      ∃ constraint ∈ constraints, constraint.var = var ∧ index :: suffix ∈ fromPathTrie constraint.trie := by
  rw [batch_at _ constraints valid]
  exact descendScs_exact index constraints valid var suffix

/-- A batched child obligation remains canonical and nonempty. -/
theorem batch_proper (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) (index : Nat)
    (constraint : Suspended Variable) (member : constraint ∈ batch (fun _ => []) constraints index) :
    Valid constraint.trie ∧ isEmpty constraint.trie = false := by
  rw [batch_at _ constraints valid] at member
  simp only [List.nil_append, EqualityTrie.descendScs, List.mem_filter, List.mem_map] at member
  obtain ⟨⟨original, present, rfl⟩, nonempty⟩ := member
  exact ⟨descend_valid original.trie (valid original present) index, by simpa using nonempty⟩

/-- An invalid empty child shows why the source nonempty-child invariant is required. -/
theorem invalid_empty_child_differs (var : Variable) :
    batch (fun _ => []) [⟨.branch [(0, .empty)], var⟩] 0 = [⟨.empty, var⟩] ∧
      EqualityTrie.descendScs 0 [⟨.branch [(0, .empty)], var⟩] = [] := by
  constructor <;> rfl

/-- Stored first indices of one trie, before duplicate keys across obligations are merged. -/
def keysOf : Trie → List Nat
  | .empty | .terminal => []
  | .branch entries => entries.map Prod.fst

/-- The batch inserts exactly these child indices; repeated keys share a bucket. -/
def keys (constraints : List (Suspended Variable)) : List Nat :=
  constraints.flatMap fun constraint => keysOf constraint.trie

/-- A valid trie key is exactly the first index of at least one represented path. -/
theorem key_path_iff (trie : Trie) (valid : Valid trie) (index : Nat) :
    index ∈ keysOf trie ↔ ∃ suffix, index :: suffix ∈ fromPathTrie trie := by
  cases trie with
  | empty => simp [keysOf, fromPathTrie]
  | terminal => simp [keysOf, fromPathTrie]
  | branch entries =>
      rw [Valid] at valid
      constructor
      · intro member
        obtain ⟨⟨key, child⟩, entry, same⟩ := List.mem_map.mp member
        change key = index at same
        subst key
        have proper := valid.2.2 index child entry
        obtain ⟨suffix, present⟩ := valid_has_path child proper.2 proper.1
        exact ⟨suffix, (mem_fromChildren entries _).mpr ⟨index, child, suffix, entry, present, rfl⟩⟩
      · rintro ⟨suffix, present⟩
        obtain ⟨key, child, tail, entry, _, same⟩ := (mem_fromChildren entries _).mp present
        cases same
        exact List.mem_map.mpr ⟨(index, child), entry, rfl⟩

/-- Key membership is equivalent to a nonempty bucket in the actual batched map. -/
theorem key_bucket_iff (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) (index : Nat) :
    index ∈ keys constraints ↔ batch (fun _ => []) constraints index ≠ [] := by
  constructor
  · intro member
    obtain ⟨original, present, key⟩ := List.mem_flatMap.mp member
    obtain ⟨suffix, path⟩ := (key_path_iff original.trie (valid original present) index).mp key
    obtain ⟨constraint, member, _, _⟩ :=
      (batch_exact constraints valid index original.var suffix).mpr ⟨original, present, rfl, path⟩
    exact List.ne_nil_of_mem member
  · intro nonempty
    obtain ⟨constraint, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    have proper := batch_proper constraints valid index constraint member
    have notEmpty : constraint.trie ≠ .empty := by intro same; simp [same, isEmpty] at proper
    obtain ⟨suffix, path⟩ := valid_has_path constraint.trie proper.1 notEmpty
    obtain ⟨original, present, _, path⟩ :=
      (batch_exact constraints valid index constraint.var suffix).mp ⟨constraint, member, rfl, path⟩
    exact List.mem_flatMap.mpr ⟨original, present,
      (key_path_iff original.trie (valid original present) index).mpr ⟨suffix, path⟩⟩

/-- The source lookupMax guard checks the largest inserted child key. -/
def arityCheck (arity : Nat) (constraints : List (Suspended Variable)) : Bool :=
  (maxIndex (keys constraints)).all (· < arity)

/-- The batched lookupMax guard is exactly the existing per-path arity requirement. -/
theorem arityCheck_exact (arity : Nat) (constraints : List EnumerationState.Suspended)
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) :
    arityCheck arity constraints = EnumerationState.arityAllows arity constraints := by
  apply Bool.eq_iff_iff.mpr
  rw [arityCheck, maxIndex_lt, EnumerationState.arityAllows_correct]
  constructor
  · intro bound constraint present index suffix path
    apply bound index
    exact List.mem_flatMap.mpr ⟨constraint, present,
      (key_path_iff constraint.trie (valid constraint present) index).mpr ⟨suffix, path⟩⟩
  · intro bounds index member
    obtain ⟨constraint, present, key⟩ := List.mem_flatMap.mp member
    obtain ⟨suffix, path⟩ := (key_path_iff constraint.trie (valid constraint present) index).mp key
    exact bounds constraint present index suffix path

/-- Every checked inherited bucket addresses an existing child of the transition. -/
theorem checked_bucket_bound (arity : Nat) (constraints : List (Suspended Variable))
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie)
    (checked : arityCheck arity constraints = true) (index : Nat)
    (nonempty : batch (fun _ => []) constraints index ≠ []) : index < arity :=
  (maxIndex_lt (keys constraints) arity).mp checked index ((key_bucket_iff constraints valid index).mpr nonempty)

/-- Batched arity, terminal discharge, and child obligations reconstruct the original requirements. -/
theorem suspended_decomposition (assignment : Nat → Language.Term Symbol)
    (symbol : Symbol) (children : List (Language.Term Symbol)) (constraints : List EnumerationState.Suspended)
    (valid : ∀ constraint ∈ constraints, Valid constraint.trie) :
    (∀ constraint ∈ constraints, EnumerationState.Suspended.Holds assignment (.node symbol children) constraint) ↔
      arityCheck children.length constraints = true ∧
      (∀ constraint ∈ constraints, isTerminal constraint.trie = true →
        Language.Term.node symbol children = assignment constraint.var) ∧
      (∀ index child, children[index]? = some child →
        ∀ constraint ∈ batch (fun _ => []) constraints index,
          EnumerationState.Suspended.Holds assignment child constraint) := by
  simp only [arityCheck_exact children.length constraints valid, batch_at _ constraints valid, List.nil_append]
  exact EnumerationState.suspended_decomposition assignment symbol children constraints valid

/-- A valid edge's new suspended variables preserve every canonical trie. -/
theorem suspendedVars_valid (tries : List Trie) (valid : ∀ trie ∈ tries, Valid trie) (start : Nat) :
    ∀ constraint ∈ EnumerationCorrectness.suspendedVars start tries, Valid constraint.trie := by
  induction tries generalizing start with
  | nil => simp [EnumerationCorrectness.suspendedVars]
  | cons first rest ih =>
      intro constraint member
      rcases List.mem_cons.mp member with same | member
      · subst constraint; exact valid first (by simp)
      · exact ih (fun trie member => valid trie (List.mem_cons_of_mem _ member)) (start + 1) constraint member

/-- Fresh allocation changes variables but retains the edge's own arity guarantees. -/
theorem suspendedVars_arity (arity : Nat) (tries : List Trie)
    (valid : ∀ trie ∈ tries, Valid trie)
    (fits : ∀ trie ∈ tries, ∀ index suffix, index :: suffix ∈ fromPathTrie trie → index < arity)
    (start : Nat) : arityCheck arity (EnumerationCorrectness.suspendedVars start tries) = true := by
  rw [arityCheck_exact arity _ (suspendedVars_valid tries valid start), EnumerationState.arityAllows_correct]
  induction tries generalizing start with
  | nil => simp [EnumerationCorrectness.suspendedVars]
  | cons first rest ih =>
      intro constraint member index suffix path
      rcases List.mem_cons.mp member with same | member
      · subst constraint; exact fits first (by simp) index suffix path
      · exact ih (fun trie member => valid trie (List.mem_cons_of_mem _ member))
          (fun trie member => fits trie (List.mem_cons_of_mem _ member)) (start + 1) constraint member index suffix path

/-- New classes that already fit the edge need no second source arity check. -/
theorem fresh_check_redundant (arity : Nat) (inherited added : List EnumerationState.Suspended)
    (oldValid : ∀ constraint ∈ inherited, Valid constraint.trie)
    (newValid : ∀ constraint ∈ added, Valid constraint.trie)
    (newFits : arityCheck arity added = true) :
    arityCheck arity (inherited ++ added) = arityCheck arity inherited := by
  have allValid : ∀ constraint ∈ inherited ++ added, Valid constraint.trie := by
    intro constraint member
    exact (List.mem_append.mp member).elim (oldValid constraint) (newValid constraint)
  rw [arityCheck_exact arity added newValid] at newFits
  rw [arityCheck_exact arity _ allValid, arityCheck_exact arity inherited oldValid]
  simp only [EnumerationState.arityAllows, List.all_append]
  change (EnumerationState.arityAllows arity inherited && EnumerationState.arityAllows arity added) = _
  rw [newFits, Bool.and_true]
  rfl

end MicroCFTA.EnumerationCPSDescent
