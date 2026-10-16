import MicroCFTA.SourceCurrentConjunctionEmptinessTable

/-!
# Sound finite tables with local physical row receipts

Each stored entry retains its actual operand and requirement lists.
Coverage states a necessary smaller-witness law for those literal rows.
It does not select a global exposure, projection, or row-supply function.
Key faithfulness applies only to resident closed nonempty node records.
The reached physical exploration must still derive these local receipts.
-/
namespace MicroCFTA.SourceCurrentConjunctionTableSoundness
open Language
open SourceCurrentConjunctionEmptinessRows (Accepts)
open SourceCurrentConjunctionEmptinessTable (Entry keys lookup lookup_member lookup_none_iff read classify rows states states_complete)
variable {Node Symbol : Type}

/-- Every stored operand and requirement retains its current physical node domain. -/
structure EntryDomain (empty : Node) (closed : Node → Bool) (resident : Node → Prop) (entry : Entry Node) : Prop where
  closed : entry.nodes.all closed = true
  nonempty : empty ∉ entry.nodes
  available : ∀ node ∈ entry.nodes, resident node
  requirements : ∀ row ∈ entry.rows, ∀ nodes ∈ row, ∀ node ∈ nodes, resident node

/-- Physical receipts concern only literal entries of this finite table. -/
def StoredDomain (empty : Node) (closed : Node → Bool) (resident : Node → Prop) (table : List (Entry Node)) : Prop :=
  ∀ entry ∈ table, EntryDomain empty closed resident entry

/-- An accepted parent needs one actual stored row of smaller common accepted witnesses. -/
def Coverage (meaning : Node → Term Symbol → Prop) (entry : Entry Node) : Prop :=
  ∀ term, Accepts meaning entry.nodes term →
    ∃ row ∈ entry.rows, ∀ nodes ∈ row,
      ∃ part, Accepts meaning nodes part ∧ part.height < term.height

/-- Every reached entry has its own local witness receipt. -/
def Covered (meaning : Node → Term Symbol → Prop) (table : List (Entry Node)) : Prop :=
  ∀ entry ∈ table, Coverage meaning entry

/-- Only resident closed records outside Empty need distinct physical keys. -/
def KeyFaithful (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop) : Prop :=
  ∀ left right, resident left → resident right → left ≠ empty → right ≠ empty →
    closed left = true → closed right = true → key left = key right → left = right

/-- Scoped individual key faithfulness identifies complete ordered conjunction lists. -/
theorem keys_injective (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (faithful : KeyFaithful empty key closed resident) (left right : List Node)
    (leftResident : ∀ node ∈ left, resident node) (rightResident : ∀ node ∈ right, resident node)
    (leftNonempty : empty ∉ left) (rightNonempty : empty ∉ right)
    (leftClosed : left.all closed = true) (rightClosed : right.all closed = true)
    (same : keys key left = keys key right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [keys]
  | cons first rest ih =>
      cases right with
      | nil => simp [keys] at same
      | cons other others =>
          simp only [keys, List.map_cons, List.cons.injEq] at same
          simp only [List.all_cons, Bool.and_eq_true] at leftClosed rightClosed
          have heads := faithful first other (leftResident _ List.mem_cons_self) (rightResident _ List.mem_cons_self)
            (fun equal => leftNonempty (by simp [equal])) (fun equal => rightNonempty (by simp [equal]))
            leftClosed.1 rightClosed.1 same.1
          have tails := ih others
            (fun node member => leftResident node (List.mem_cons_of_mem _ member))
            (fun node member => rightResident node (List.mem_cons_of_mem _ member))
            (fun member => leftNonempty (List.mem_cons_of_mem _ member))
            (fun member => rightNonempty (List.mem_cons_of_mem _ member))
            leftClosed.2 rightClosed.2 same.2
          rw [heads, tails]

/-- Literal key lookup transfers acceptance only between resident closed conjunctions. -/
theorem classify_accepted [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (nodes : List Node) (available : ∀ node ∈ nodes, resident node) (term : Term Symbol)
    (accepted : Accepts meaning nodes term) :
    ConservativeEmptiness.AcceptsRequirement (fun state => Accepts meaning (read key table state))
      (classify empty key closed table nodes) term := by
  by_cases impossible : empty ∈ nodes
  · exact False.elim (emptyFalse term (accepted.2 empty impossible))
  · by_cases allClosed : nodes.all closed = true
    · by_cases present : keys key nodes ∈ table.map (fun entry => keys key entry.nodes)
      · simp only [classify, impossible, ite_false, allClosed, ite_true, present, dite_true,
          ConservativeEmptiness.AcceptsRequirement]
        cases found : lookup key (keys key nodes) table with
        | none => exact False.elim ((lookup_none_iff key _ table).mp found present)
        | some entry =>
            have actual := lookup_member key _ table entry found
            have domain := stored entry actual.1
            have same := keys_injective empty key closed resident faithful entry.nodes nodes domain.available available
              domain.nonempty impossible domain.closed allClosed actual.2
            simpa only [SourceCurrentConjunctionEmptinessTable.read, found, Option.getD_some, same] using accepted
      · simp [classify, impossible, allClosed, present, ConservativeEmptiness.AcceptsRequirement]
    · simp [classify, impossible, allClosed, ConservativeEmptiness.AcceptsRequirement]

private theorem obligation [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (nodes : List Node) (available : ∀ node ∈ nodes, resident node) (part parent : Term Symbol)
    (accepted : Accepts meaning nodes part) (smaller : part.height < parent.height) :
    ConservativeEmptiness.Obligation (fun state => Accepts meaning (read key table state)) Term.height parent
      (classify empty key closed table nodes) := by
  have witness := classify_accepted empty key closed resident table stored faithful meaning emptyFalse nodes available part accepted
  cases classified : classify empty key closed table nodes with
  | empty => simp only [classified, ConservativeEmptiness.AcceptsRequirement] at witness
  | outside => trivial
  | inside state => exact ⟨part, by simpa only [classified, ConservativeEmptiness.AcceptsRequirement] using witness, smaller⟩

/-- Per-entry actual row coverage derives finite fixed-point decomposition. -/
theorem decomposes [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (coverage : Covered meaning table) :
    ConservativeEmptiness.Decomposes (rows empty key closed table)
      (fun state => Accepts meaning (read key table state)) Term.height := by
  intro state term accepted
  cases found : lookup key state.val table with
  | none => exact False.elim ((lookup_none_iff key state.val table).mp found state.property)
  | some entry =>
      have member := (lookup_member key _ table entry found).1
      have original : Accepts meaning entry.nodes term := by
        simpa only [SourceCurrentConjunctionEmptinessTable.read, found, Option.getD_some] using accepted
      obtain ⟨row, rowIn, witnesses⟩ := coverage entry member term original
      refine ⟨row.map (classify empty key closed table), ?_, ?_⟩
      · simp only [rows, found, Option.getD_some]
        exact List.mem_map.mpr ⟨row, rowIn, rfl⟩
      · intro requirement included
        obtain ⟨nodes, nodesIn, rfl⟩ := List.mem_map.mp included
        obtain ⟨part, common, smaller⟩ := witnesses nodes nodesIn
        exact obligation empty key closed resident table stored faithful meaning emptyFalse nodes
          ((stored entry member).requirements row rowIn nodes nodesIn) part term common smaller

/-- A true finite-table verdict excludes common terms without a fixed source row supplier. -/
theorem provablyEmpty_sound [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (coverage : Covered meaning table) (query : List Node) (available : ∀ node ∈ query, resident node)
    (verdict : SourceCurrentConjunctionEmptinessTable.provablyEmpty empty key closed table query = true) :
    ∀ term, ¬Accepts meaning query term := by
  have excluded := ConservativeEmptiness.provablyEmpty_sound (states key table) (states_complete key table)
    (rows empty key closed table) (fun state => Accepts meaning (read key table state)) Term.height
    (decomposes empty key closed resident table stored faithful meaning emptyFalse coverage) _ verdict
  intro term accepted
  exact excluded term (classify_accepted empty key closed resident table stored faithful meaning emptyFalse query available term accepted)

/-- A completed literal equality-stop run has the same sound conservative query answer. -/
theorem grow_sound [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (coverage : Covered meaning table) (query : List Node) (available : ∀ node ∈ query, resident node)
    (fuel : Nat) (known : SourceCurrentConjunctionEmptinessTable.State key table → Bool)
    (done : SourceCurrentConjunctionEmptinessTable.grow empty key closed table fuel (fun _ => false) = some known)
    (verdict : SourceCurrentConjunctionEmptinessTable.canAccept empty key closed table known query = false) :
    ∀ term, ¬Accepts meaning query term := by
  have fixed := SourceCurrentConjunctionEmptinessTable.grow_done_fixed empty key closed table fuel _ known done
  rw [SourceCurrentConjunctionEmptinessTable.sourceStep_eq] at fixed
  intro term accepted
  have witness := classify_accepted empty key closed resident table stored faithful meaning emptyFalse query available term accepted
  have rejected : ConservativeEmptiness.canAccept known (classify empty key closed table query) = false := by
    rwa [← SourceCurrentConjunctionEmptinessTable.canAccept_agrees]
  cases classified : classify empty key closed table query with
  | empty => simp only [classified, ConservativeEmptiness.AcceptsRequirement] at witness
  | outside => simp [classified, ConservativeEmptiness.canAccept] at rejected
  | inside state =>
      have acceptedState : Accepts meaning (read key table state) term := by
        simpa only [classified, ConservativeEmptiness.AcceptsRequirement] using witness
      have marked := ConservativeEmptiness.fixed_no_loss _ _ Term.height
        (decomposes empty key closed resident table stored faithful meaning emptyFalse coverage) known fixed state term acceptedState
      simp [classified, ConservativeEmptiness.canAccept, marked] at rejected

/-- The public initial closed guard and a completed grow receipt give source-shaped exclusion. -/
theorem answer_sound [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool) (resident : Node → Prop)
    (table : List (Entry Node)) (stored : StoredDomain empty closed resident table)
    (faithful : KeyFaithful empty key closed resident)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (coverage : Covered meaning table) (start : Node) (available : resident start)
    (fuel : Nat) (known : SourceCurrentConjunctionEmptinessTable.State key table → Bool)
    (done : SourceCurrentConjunctionEmptinessTable.grow empty key closed table fuel (fun _ => false) = some known)
    (verdict : SourceCurrentConjunctionEmptinessTable.answer empty key closed table known start = true) :
    ∀ term, ¬meaning start term := by
  have refused : SourceCurrentConjunctionEmptinessTable.canAccept empty key closed table known [start] = false := by
    have checked := verdict
    simp only [SourceCurrentConjunctionEmptinessTable.answer, Bool.and_eq_true, Bool.not_eq_true'] at checked
    exact checked.2
  have excluded := grow_sound empty key closed resident table stored faithful meaning emptyFalse coverage [start]
    (by intro node member; exact (List.mem_singleton.mp member) ▸ available) fuel known done refused
  intro term accepted
  exact excluded term ⟨by simp, by simpa using accepted⟩

end MicroCFTA.SourceCurrentConjunctionTableSoundness
