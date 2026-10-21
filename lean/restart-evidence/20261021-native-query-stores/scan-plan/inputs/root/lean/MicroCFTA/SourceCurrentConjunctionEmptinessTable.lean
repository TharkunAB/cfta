import MicroCFTA.SourceCurrentConjunctionEmptinessRows
import MicroCFTA.ConservativeEmptiness

/-!
# Finite tables for the current conjunction emptiness check

The table stores the actual conjunction read at each admitted identity list.
The worklist prepends all new row requirements. Empty, exhausted, open, and
already stored conjunctions are skipped in source order. Completed finite
node exposure and projection remain the input domain of this component.
-/
namespace MicroCFTA.SourceCurrentConjunctionEmptinessTable
open Language SourceCurrentConjunctionEmptinessRows
variable {Node Symbol : Type}

/-- A stored row retains its admitted operands and completed tuple requirements. -/
structure Entry (Node : Type) where
  nodes : List Node
  rows : List (List (List Node))

/-- The source uses an ordered list of untagged resident identities as its map key. -/
def keys (key : Node → Int) (nodes : List Node) : List Int := nodes.map key

/-- First lookup is the logical observation of a finite source map. -/
def lookup (key : Node → Int) (query : List Int) : List (Entry Node) → Option (Entry Node)
  | [] => none
  | first :: rest => if query = keys key first.nodes then some first else lookup key query rest

/-- Absence is exactly absence from the finite list of stored conjunction keys. -/
theorem lookup_none_iff (key : Node → Int) (query : List Int) (table : List (Entry Node)) :
    lookup key query table = none ↔ query ∉ table.map (fun entry => keys key entry.nodes) := by
  induction table with
  | nil => simp [lookup]
  | cons first rest ih => by_cases same : query = keys key first.nodes <;> simp [lookup, same, ih]

/-- A successful read retains an actual entry occurrence and its literal identity list. -/
theorem lookup_member (key : Node → Int) (query : List Int) (table : List (Entry Node)) (entry : Entry Node)
    (found : lookup key query table = some entry) : entry ∈ table ∧ keys key entry.nodes = query := by
  induction table with
  | nil => cases found
  | cons first rest ih =>
      simp only [lookup] at found
      split at found
      · cases found; exact ⟨by simp, (by assumption : query = keys key entry.nodes).symm⟩
      · have checked := ih found; exact ⟨by simp [checked.1], checked.2⟩

/-- Skip tests retain the current source order after the empty-node test. -/
def skip (key : Node → Int) (closed : Node → Bool) (budget : Nat) (table : List (Entry Node)) (nodes : List Node) : Bool :=
  budget == 0 || !(nodes.all closed) || (lookup key (keys key nodes) table).isSome

/-- Admission derives positive budget, closed operands, and a previously absent key. -/
theorem admitted (key : Node → Int) (closed : Node → Bool) (budget : Nat) (table : List (Entry Node)) (nodes : List Node)
    (fresh : skip key closed budget table nodes = false) :
    0 < budget ∧ nodes.all closed = true ∧ lookup key (keys key nodes) table = none := by
  simp only [skip, Bool.or_eq_false_iff, Bool.not_eq_false', beq_eq_false_iff_ne] at fresh
  refine ⟨by omega, fresh.1.2, ?_⟩
  cases found : lookup key (keys key nodes) table with
  | none => rfl
  | some entry => simp [found] at fresh

/-- Drain the source worklist. Only a new admitted conjunction decrements the budget. -/
def explore [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (budget : Nat)
    (table : List (Entry Node)) (pending : List (List Node)) : List (Entry Node) :=
  match pending with
  | [] => table
  | nodes :: rest =>
      if empty ∈ nodes then explore empty key closed supply budget table rest
      else if skip key closed budget table nodes then explore empty key closed supply budget table rest
      else explore empty key closed supply (budget - 1) (⟨nodes, supply nodes⟩ :: table) ((supply nodes).flatten ++ rest)
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have positive := (admitted key closed budget table nodes (Bool.eq_false_iff.mpr (by assumption))).1
    omega

/-- Each stored entry has its actual source rows and passed the closed, nonempty-node tests. -/
def Stored (empty : Node) (closed : Node → Bool) (supply : List Node → List (List (List Node))) (table : List (Entry Node)) : Prop :=
  ∀ entry ∈ table, entry.rows = supply entry.nodes ∧ entry.nodes.all closed = true ∧ empty ∉ entry.nodes

/-- Actual exploration derives stored row receipts and the finite admission bound. -/
theorem explore_stored [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (budget : Nat) (table : List (Entry Node)) (pending : List (List Node))
    (stored : Stored empty closed supply table) :
    Stored empty closed supply (explore empty key closed supply budget table pending) ∧
      (explore empty key closed supply budget table pending).length ≤ table.length + budget := by
  rw [explore.eq_def]
  cases pending with
  | nil => simp only; exact ⟨stored, by omega⟩
  | cons nodes rest =>
      by_cases impossible : empty ∈ nodes
      · simpa only [impossible, ite_true] using explore_stored empty key closed supply budget table rest stored
      · simp only [impossible, ite_false]
        by_cases skipped : skip key closed budget table nodes = true
        · simpa only [skipped, ite_true] using explore_stored empty key closed supply budget table rest stored
        · simp only [skipped, Bool.false_eq_true, ite_false]
          have fresh := admitted key closed budget table nodes (Bool.eq_false_iff.mpr skipped)
          have next : Stored empty closed supply (⟨nodes, supply nodes⟩ :: table) := by
            intro entry member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨rfl, fresh.2.1, impossible⟩
            · exact stored entry member
          obtain ⟨final, bound⟩ := explore_stored empty key closed supply (budget - 1)
            (⟨nodes, supply nodes⟩ :: table) ((supply nodes).flatten ++ rest) next
          exact ⟨final, by simp only [List.length_cons] at bound; omega⟩
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have _positive := (admitted key closed budget table nodes (Bool.eq_false_iff.mpr skipped)).1
    omega

/-- Empty-start exploration supplies all entry receipts without a final-table oracle. -/
theorem entered [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (budget : Nat) (pending : List (List Node)) :
    Stored empty closed supply (explore empty key closed supply budget [] pending) ∧
      (explore empty key closed supply budget [] pending).length ≤ budget := by
  simpa only [List.length_nil, Nat.zero_add] using explore_stored empty key closed supply budget [] pending
    (by intro entry member; cases member)

/-- Old reads and unique identity-list keys survive every completed exploration. -/
theorem explore_retains [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (budget : Nat) (table : List (Entry Node)) (pending : List (List Node)) :
    (∀ ids entry, lookup key ids table = some entry → lookup key ids (explore empty key closed supply budget table pending) = some entry) ∧
      ((table.map (fun entry => keys key entry.nodes)).Nodup →
        ((explore empty key closed supply budget table pending).map (fun entry => keys key entry.nodes)).Nodup) := by
  rw [explore.eq_def]
  cases pending with
  | nil => exact ⟨fun _ _ found => found, id⟩
  | cons nodes rest =>
      by_cases impossible : empty ∈ nodes
      · simpa only [impossible, ite_true] using explore_retains empty key closed supply budget table rest
      · simp only [impossible, ite_false]
        by_cases skipped : skip key closed budget table nodes = true
        · simpa only [skipped, ite_true] using explore_retains empty key closed supply budget table rest
        · simp only [skipped, Bool.false_eq_true, ite_false]
          have fresh := admitted key closed budget table nodes (Bool.eq_false_iff.mpr skipped)
          obtain ⟨retained, unique⟩ := explore_retains empty key closed supply (budget - 1)
            (⟨nodes, supply nodes⟩ :: table) ((supply nodes).flatten ++ rest)
          refine ⟨?_, ?_⟩
          · intro ids entry found
            apply retained ids entry
            by_cases same : ids = keys key nodes
            · subst ids; rw [fresh.2.2] at found; cases found
            · simpa only [lookup, same, ite_false] using found
          · intro original
            apply unique
            simp only [List.map_cons, List.nodup_cons]
            exact ⟨(lookup_none_iff key _ table).mp fresh.2.2, original⟩
termination_by (budget, pending.length)
decreasing_by
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · apply Prod.Lex.left
    have _positive := (admitted key closed budget table nodes (Bool.eq_false_iff.mpr skipped)).1
    omega

/-- Only actual stored identity lists enter the finite fixed-point carrier. -/
abbrev State (key : Node → Int) (table : List (Entry Node)) :=
  { ids : List Int // ids ∈ table.map (fun entry => keys key entry.nodes) }

/-- Attach the actual finite keys without adding an unlisted state. -/
def states (key : Node → Int) (table : List (Entry Node)) : List (State key table) :=
  (table.map (fun entry => keys key entry.nodes)).attach

/-- Every carrier value occurs in the attached finite table key list. -/
theorem states_complete (key : Node → Int) (table : List (Entry Node)) (state : State key table) : state ∈ states key table := by
  simp [states]

/-- Read only the completed original conjunction stored under this actual table key. -/
def read (key : Node → Int) (table : List (Entry Node)) (state : State key table) : List Node :=
  ((lookup key state.val table).getD ⟨[], []⟩).nodes

/-- Free references remain possible even when a matching key is present. -/
def classify [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (nodes : List Node) : ConservativeEmptiness.Requirement (State key table) :=
  if empty ∈ nodes then .empty
  else if nodes.all closed then
    if present : keys key nodes ∈ table.map (fun entry => keys key entry.nodes) then .inside ⟨keys key nodes, present⟩ else .outside
  else .outside

/-- Classify each original stored requirement without changing tuple or requirement order. -/
def rows [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (state : State key table) : List (List (ConservativeEmptiness.Requirement (State key table))) :=
  (((lookup key state.val table).getD ⟨[], []⟩).rows).map (fun row => row.map (classify empty key closed table))

/-- The finite carrier computes the least possible-state fixed point. -/
def provablyEmpty [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (query : List Node) : Bool :=
  ConservativeEmptiness.provablyEmpty (states key table) (rows empty key closed table) (classify empty key closed table query)

/-- Closed nonempty resident keys must distinguish complete individual node records. -/
def KeyFaithful (empty : Node) (key : Node → Int) (closed : Node → Bool) : Prop :=
  ∀ left right, left ≠ empty → right ≠ empty → closed left = true → closed right = true → key left = key right → left = right

/-- Component key faithfulness derives equality of entire closed conjunction lists. -/
theorem keys_injective (empty : Node) (key : Node → Int) (closed : Node → Bool) (faithful : KeyFaithful empty key closed)
    (left right : List Node) (leftNonempty : empty ∉ left) (rightNonempty : empty ∉ right)
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
          have heads := faithful first other (by intro eq; exact leftNonempty (by simp [eq]))
            (by intro eq; exact rightNonempty (by simp [eq])) leftClosed.1 rightClosed.1 same.1
          have tails := ih others (fun member => leftNonempty (List.mem_cons_of_mem _ member)) (fun member => rightNonempty (List.mem_cons_of_mem _ member)) leftClosed.2 rightClosed.2 same.2
          rw [heads, tails]

/-- Actual closed-key readback transfers smaller common witnesses into classified obligations. -/
theorem obligation [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (table : List (Entry Node))
    (stored : Stored empty closed supply table) (faithful : KeyFaithful empty key closed)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (nodes : List Node) (part parent : Term Symbol) (accepted : Accepts meaning nodes part)
    (smaller : part.height < parent.height) :
    ConservativeEmptiness.Obligation (fun state => Accepts meaning (read key table state)) Term.height parent
      (classify empty key closed table nodes) := by
  by_cases impossible : empty ∈ nodes
  · exact False.elim (emptyFalse part (accepted.2 empty impossible))
  · by_cases allClosed : nodes.all closed = true
    · by_cases present : keys key nodes ∈ table.map (fun entry => keys key entry.nodes)
      · simp only [classify, impossible, ite_false, allClosed, ite_true, present, dite_true, ConservativeEmptiness.Obligation]
        cases found : lookup key (keys key nodes) table with
        | none => exact False.elim ((lookup_none_iff key _ table).mp found present)
        | some entry =>
            have actual := lookup_member key _ table entry found
            have record := stored entry actual.1
            have same := keys_injective empty key closed faithful entry.nodes nodes record.2.2 impossible record.2.1 allClosed actual.2
            exact ⟨part, by simpa only [read, found, Option.getD_some, same] using accepted, smaller⟩
      · simp [classify, impossible, allClosed, present, ConservativeEmptiness.Obligation]
    · simp [classify, impossible, allClosed, ConservativeEmptiness.Obligation]

/-- Derived tuple witnesses discharge the fixed-point decomposition obligation. -/
theorem decomposes [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (SourceCurrentConjunctionEmptinessRows.Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (table : List (Entry Node)) (stored : Stored empty closed (tupleRows empty key edges project) table)
    (faithful : KeyFaithful empty key closed) :
    ConservativeEmptiness.Decomposes (rows empty key closed table)
      (fun state => Accepts meaning (read key table state)) Term.height := by
  intro state term accepted
  cases found : lookup key state.val table with
  | none => exact False.elim ((lookup_none_iff key state.val table).mp found state.property)
  | some entry =>
      have record := stored entry (lookup_member key _ table entry found).1
      have original : Accepts meaning entry.nodes term := by simpa only [read, found, Option.getD_some] using accepted
      obtain ⟨row, member, witnesses⟩ := tupleRows_witness empty key meaning emptyFalse edges expose project projectLaw entry.nodes term original
      refine ⟨row.map (classify empty key closed table), ?_, ?_⟩
      · simp only [rows, found, Option.getD_some, record.1]
        exact List.mem_map.mpr ⟨row, member, rfl⟩
      · intro requirement included
        obtain ⟨nodes, nodesIn, rfl⟩ := List.mem_map.mp included
        obtain ⟨part, common, smaller⟩ := witnesses nodes nodesIn
        exact obligation empty key closed _ table stored faithful meaning emptyFalse nodes part term common smaller

/-- A true finite-table verdict excludes every common accepted finite term. -/
theorem sound [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (SourceCurrentConjunctionEmptinessRows.Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (table : List (Entry Node)) (stored : Stored empty closed (tupleRows empty key edges project) table)
    (faithful : KeyFaithful empty key closed) (query : List Node)
    (verdict : provablyEmpty empty key closed table query = true) : ∀ term, ¬Accepts meaning query term := by
  have loss := ConservativeEmptiness.provablyEmpty_sound (states key table) (states_complete key table)
    (rows empty key closed table) (fun state => Accepts meaning (read key table state)) Term.height
    (decomposes empty key closed meaning emptyFalse edges expose project projectLaw table stored faithful) _ verdict
  intro term accepted
  let parent : Term Symbol := match term with | .node symbol _ => .node symbol [term]
  have bound : term.height < parent.height := by cases term; simp [parent, Term.height]
  have checked := obligation empty key closed _ table stored faithful meaning emptyFalse query term parent accepted bound
  cases classified : classify empty key closed table query with
  | empty => simp only [classified, ConservativeEmptiness.Obligation] at checked
  | outside => exact loss term (by simp only [classified, ConservativeEmptiness.AcceptsRequirement])
  | inside state =>
      obtain ⟨part, common, _⟩ := (show ∃ part, Accepts meaning (read key table state) part ∧ part.height < parent.height from by simpa only [classified, ConservativeEmptiness.Obligation] using checked)
      exact loss part (by simpa only [classified, ConservativeEmptiness.AcceptsRequirement] using common)

/-- Empty-start finite exploration and derived tuple coverage give a sound empty verdict. -/
theorem explored_sound [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (SourceCurrentConjunctionEmptinessRows.Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (faithful : KeyFaithful empty key closed) (budget : Nat) (start : Node)
    (verdict : provablyEmpty empty key closed
      (explore empty key closed (tupleRows empty key edges project) budget [] [[start]]) [start] = true) :
    ∀ term, ¬meaning start term := by
  have excluded := sound empty key closed meaning emptyFalse edges expose project projectLaw _
    (entered empty key closed _ budget [[start]]).1 faithful [start] verdict
  intro term accepted
  exact excluded term ⟨by simp, by simpa using accepted⟩

/-- Literal source possibility tests empty first, then open, absent, and known. -/
def canAccept [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (known : State key table → Bool) (nodes : List Node) : Bool :=
  if empty ∈ nodes then false
  else !(nodes.all closed) || (lookup key (keys key nodes) table).isNone ||
    (if present : keys key nodes ∈ table.map (fun entry => keys key entry.nodes) then known ⟨keys key nodes, present⟩ else false)

/-- Literal source possibility agrees with finite requirement classification. -/
theorem canAccept_agrees [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (known : State key table → Bool) (nodes : List Node) :
    canAccept empty key closed table known nodes = ConservativeEmptiness.canAccept known (classify empty key closed table nodes) := by
  by_cases impossible : empty ∈ nodes
  · simp [canAccept, classify, impossible, ConservativeEmptiness.canAccept]
  · by_cases allClosed : nodes.all closed = true
    · by_cases present : keys key nodes ∈ table.map (fun entry => keys key entry.nodes)
      · cases found : lookup key (keys key nodes) table with
        | none => exact False.elim ((lookup_none_iff key _ table).mp found present)
        | some entry => simp [canAccept, classify, impossible, allClosed, present, found, ConservativeEmptiness.canAccept]
      · have absent := (lookup_none_iff key _ table).mpr present
        simp [canAccept, classify, impossible, allClosed, present, absent, ConservativeEmptiness.canAccept]
    · have openInput : nodes.all closed = false := Bool.eq_false_iff.mpr allClosed
      simp [canAccept, classify, impossible, openInput, ConservativeEmptiness.canAccept]

/-- Source row filtering evaluates each tuple's requirements in their stored order. -/
def sourceStep [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (known : State key table → Bool) (state : State key table) : Bool :=
  (((lookup key state.val table).getD ⟨[], []⟩).rows).any (fun row => row.all (canAccept empty key closed table known))

/-- Source Map-filter possibility has exactly the finite OR-of-AND transition. -/
theorem sourceStep_eq [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) : sourceStep empty key closed table = ConservativeEmptiness.step (rows empty key closed table) := by
  funext known state
  have agree : canAccept empty key closed table known = fun nodes => ConservativeEmptiness.canAccept known (classify empty key closed table nodes) :=
    funext (canAccept_agrees empty key closed table known)
  simp only [sourceStep, rows, ConservativeEmptiness.step, List.any_map, List.all_map, Function.comp_def, agree]

/-- One synchronous round per actual entry is an exact fixed point, including conservative open requirements. -/
theorem possible_fixed [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) :
    sourceStep empty key closed table
      (ConservativeEmptiness.possible (states key table) (rows empty key closed table)) =
      ConservativeEmptiness.possible (states key table) (rows empty key closed table) := by
  rw [sourceStep_eq]
  exact ConservativeEmptiness.possible_fixed _ (states_complete key table) _

/-- Finite equality compares exactly the stored key carrier. -/
def same (key : Node → Int) (table : List (Entry Node)) (left right : State key table → Bool) : Bool :=
  (states key table).all (fun state => left state == right state)

/-- Equal stored-key observations determine the entire finite known set. -/
theorem same_eq (key : Node → Int) (table : List (Entry Node)) (left right : State key table → Bool)
    (equal : same key table left right = true) : left = right := by
  funext state
  exact beq_iff_eq.mp (List.all_eq_true.mp equal state (states_complete key table state))

/-- A finite proof counter bounds source equality-stop observations; it is not native work fuel. -/
def grow [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) : Nat → (State key table → Bool) → Option (State key table → Bool)
  | 0, _ => none
  | fuel + 1, known =>
      let next := sourceStep empty key closed table known
      if same key table next known then some known else grow empty key closed table fuel next

/-- Source equality-stop completes within table length plus one comparisons from false. -/
theorem grow_rounds_complete [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (fuel start : Nat) (enough : table.length ≤ start + fuel) :
    grow empty key closed table (fuel + 1)
      (Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start) =
      some (ConservativeEmptiness.possible (states key table) (rows empty key closed table)) := by
  have length : (states key table).length = table.length := by simp [states]
  induction fuel generalizing start with
  | zero =>
      have later : start = (states key table).length + (start - (states key table).length) := by omega
      have stable : Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start =
          ConservativeEmptiness.possible (states key table) (rows empty key closed table) := by
        rw [sourceStep_eq, later]
        exact ConservativeEmptiness.iterate_stable _ (states_complete key table) _ _
      simp only [grow, stable, possible_fixed, same, List.all_eq_true, beq_self_eq_true, implies_true, ite_true]
  | succ fuel ih =>
      rw [grow]
      by_cases stopped : same key table
          (sourceStep empty key closed table (Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start))
          (Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start) = true
      · have fixed := same_eq key table _ _ stopped
        have least := ConservativeEmptiness.possible_least (states key table) (rows empty key closed table)
          (Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start)
          (fun state marked => by rw [← sourceStep_eq empty key closed table, fixed] at marked; exact marked)
        have upper := Productivity.iterate_below_closed (sourceStep empty key closed table) (fun _ => false)
          (ConservativeEmptiness.possible (states key table) (rows empty key closed table))
          (by rw [sourceStep_eq]; exact ConservativeEmptiness.step_monotone _)
          (by intro state impossible; cases impossible)
          (fun state marked => by rw [possible_fixed] at marked; exact marked) start
        have equal : Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start =
            ConservativeEmptiness.possible (states key table) (rows empty key closed table) := by
          funext state
          have first := least state
          have second := upper state
          cases a : Productivity.iterate (sourceStep empty key closed table) (fun _ => false) start state <;>
            cases b : ConservativeEmptiness.possible (states key table) (rows empty key closed table) state <;> simp_all
        simpa only [stopped, ite_true] using congrArg some equal
      · simp only [stopped, Bool.false_eq_true, ite_false]
        exact ih (start + 1) (by omega)

/-- Empty-start exploration bounds both admitted conjunctions and source fixed-point comparisons. -/
theorem explored_grow_complete [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (supply : List Node → List (List (List Node))) (budget : Nat) (pending : List (List Node)) :
    let table := explore empty key closed supply budget [] pending
    grow empty key closed table (budget + 1) (fun _ => false) =
      some (ConservativeEmptiness.possible (states key table) (rows empty key closed table)) := by
  dsimp only
  exact grow_rounds_complete empty key closed _ budget 0 (by simpa using (entered empty key closed supply budget pending).2)

/-- Every completed equality-stop observation is an actual fixed point. -/
theorem grow_done_fixed [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (fuel : Nat) (initial result : State key table → Bool)
    (done : grow empty key closed table fuel initial = some result) :
    sourceStep empty key closed table result = result := by
  induction fuel generalizing initial with
  | zero => simp [grow] at done
  | succ fuel ih =>
      simp only [grow] at done
      split at done
      · rename_i equal
        cases done
        exact same_eq key table _ _ equal
      · exact ih _ done

/-- A completed source equality-stop verdict uses derived tuple decomposition, not a final soundness premise. -/
theorem grow_sound [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (SourceCurrentConjunctionEmptinessRows.Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (faithful : KeyFaithful empty key closed) (budget : Nat) (start : Node)
    (fuel : Nat) (known : State key (explore empty key closed (tupleRows empty key edges project) budget [] [[start]]) → Bool)
    (done : grow empty key closed (explore empty key closed (tupleRows empty key edges project) budget [] [[start]]) fuel
      (fun _ => false) = some known)
    (verdict : canAccept empty key closed (explore empty key closed (tupleRows empty key edges project) budget [] [[start]]) known [start] = false) :
    ∀ term, ¬meaning start term := by
  let table := explore empty key closed (tupleRows empty key edges project) budget [] [[start]]
  have stored := (entered empty key closed (tupleRows empty key edges project) budget [[start]]).1
  have fixed := grow_done_fixed empty key closed table fuel _ known done
  rw [sourceStep_eq] at fixed
  have decomp := decomposes empty key closed meaning emptyFalse edges expose project projectLaw table stored faithful
  intro term accepted
  have common : Accepts meaning [start] term := ⟨by simp, by simpa using accepted⟩
  let parent : Term Symbol := match term with | .node symbol _ => .node symbol [term]
  have bound : term.height < parent.height := by cases term; simp [parent, Term.height]
  have checked := obligation empty key closed _ table stored faithful meaning emptyFalse [start] term parent common bound
  have rejected : ConservativeEmptiness.canAccept known (classify empty key closed table [start]) = false := by
    rwa [← canAccept_agrees]
  cases classified : classify empty key closed table [start] with
  | empty => simp only [classified, ConservativeEmptiness.Obligation] at checked
  | outside => simp [classified, ConservativeEmptiness.canAccept] at rejected
  | inside state =>
      obtain ⟨part, witness, _⟩ := (show ∃ part, Accepts meaning (read key table state) part ∧ part.height < parent.height from by
        simpa only [classified, ConservativeEmptiness.Obligation] using checked)
      have marked := ConservativeEmptiness.fixed_no_loss _ _ Term.height decomp known fixed state part witness
      simp [classified, ConservativeEmptiness.canAccept, marked] at rejected

/-- The current public free-variable guard runs before any table answer is needed. -/
def answer [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (known : State key table → Bool) (start : Node) : Bool :=
  closed start && !(canAccept empty key closed table known [start])

/-- An open initial input returns false, independently of every completed table field. -/
theorem open_answer [DecidableEq Node] (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (table : List (Entry Node)) (known : State key table → Bool) (start : Node) (openInput : closed start = false) :
    answer empty key closed table known start = false := by simp [answer, openInput]

end MicroCFTA.SourceCurrentConjunctionEmptinessTable
