import MicroCFTA.SourceSizedReferenceOrderBound
import MicroCFTA.SourceSizedDecided
import MicroCFTA.CompactEdgeRanks

/-!
# Increasing order in a grouped chain family

The class-list recurrence below follows `Gen/Internal/Table.hs:200-246`.
The seed pays one node. Each group reads its first child state and scales
that child's sizes. The source left fold then adds each group by an
ascending prefix-size product. `Ranked/Internal/Size.hs:495-500,771-788`
specifies that product order. Reconstruction fills the original child slots.

One fixed three-state table has unary A and B chains. Its root has children
A, B, A and equality [0,2]. The computed root class has an increasing
last-child-size subsequence of arbitrary length.

The conclusion concerns this grouped recurrence. Connecting it to the
public dispatcher, its minimum table, and its lazy indexes remains separate.
This file does not disprove `SourceSizedApiLaws.Exact.finite`.
-/

namespace MicroCFTA.SourceSizedGroupedChainOrder

open Language RecursiveSize SourceSizedDecided
open SourceSizedReferenceOrderBound

/-- The source paid constant seed has one empty selection at size one. -/
def seed (size : Nat) : List (List (Term Symbol)) :=
  if size = 1 then [[]] else []

/-- A positive group factor preserves its values and scales their sizes. -/
def scaled (factor : Nat) (inner : Nat → List Value) (size : Nat) : List Value :=
  if factor = 1 then inner size
  else if size % factor = 0 then inner (size / factor) else []

/-- The group uses the source first position as its child-state representative. -/
def groupClass (classAt : State → Nat → List (Term Symbol)) (children : List State)
    (positions : List Nat) (size : Nat) : List (Term Symbol) :=
  match positions with
  | [] => []
  | first :: _ =>
      match children[first]? with
      | none => []
      | some state => scaled positions.length (classAt state) size

/-- Reconstruct the original ordered children from the selected group values. -/
def assemble (symbol : Symbol) (arity : Nat) (groups : List (List Nat))
    (selected : List (Term Symbol)) : Term Symbol :=
  .node symbol (CompactEdgeRanks.childrenOf symbol arity (groups.zip selected))

/-- Execute the literal paid seed and source left fold over equality groups. -/
def rowClass (classAt : State → Nat → List (Term Symbol)) (symbol : Symbol)
    (children : List State) (classes : List (List Nat)) (size : Nat) : List (Term Symbol) :=
  let groups := CompactGroups.childGroups children.length classes
  ((groups.foldl (fun built group => extendForests built (groupClass classAt children group)) seed) size).map
    (assemble symbol children.length groups)

private theorem flatMap_one [DecidableEq Key] (items : List Key) (unique : items.Nodup)
    (chosen : Key) (values : Key → List Value)
    (only : ∀ key ∈ items, key ≠ chosen → values key = []) :
    items.flatMap values = if chosen ∈ items then values chosen else [] := by
  induction items with
  | nil => simp
  | cons key rest ih =>
      have facts := List.nodup_cons.mp unique
      rw [List.flatMap_cons, ih facts.2 (fun key member => only key (by simp [member]))]
      by_cases same : key = chosen
      · subst key; simp [facts.1]
      · rw [only key (by simp) same]
        simp [Ne.symm same]

/-- The first source product reads the child after the seed's one-node pay. -/
theorem consume_seed (children : Nat → List (Term Symbol)) (size : Nat) :
    extendForests seed children size =
      if 0 < size then (children (size - 1)).map (fun child => [child]) else [] := by
  unfold extendForests
  rw [flatMap_one _ List.nodup_range 1 _ (by
    intro prefixSize _ different
    simp [seed, different])]
  by_cases positive : 0 < size
  · have present : 1 ∈ List.range (size + 1) := List.mem_range.mpr (by omega)
    simp [present, positive, seed]
  · have zero : size = 0 := by omega
    subst size
    simp

/-- A nullary source row contains its leaf only at size one. -/
theorem nullary_rowClass (classAt : State → Nat → List (Term Symbol))
    (symbol : Symbol) (size : Nat) :
    rowClass classAt symbol [] [] size = if size = 1 then [.node symbol []] else [] := by
  by_cases one : size = 1 <;>
    simp [rowClass, CompactGroups.childGroups, seed, assemble, CompactEdgeRanks.childrenOf, one]

/-- A unary source row adds its root node to the selected child. -/
theorem unary_rowClass (classAt : State → Nat → List (Term Symbol))
    (symbol : Symbol) (child : State) (size : Nat) :
    rowClass classAt symbol [child] [] size =
      if 0 < size then (classAt child (size - 1)).map (fun term => .node symbol [term]) else [] := by
  change (extendForests seed (classAt child) size).map
    (assemble symbol 1 [[0]]) = _
  rw [consume_seed]
  by_cases positive : 0 < size
  · simp only [ite_eq_left positive, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro term _
    rfl
  · simp only [ite_eq_right positive, List.map_nil]

/-- A chains and B chains use different leaf symbols. -/
def leafSymbol (kind : Bool) : Nat := if kind then 2 else 0

/-- A chains and B chains use different unary symbols. -/
def unarySymbol (kind : Bool) : Nat := if kind then 3 else 1

/-- Depth zero is the leaf; each next depth adds the same unary constructor. -/
def chain (kind : Bool) : Nat → Term Nat
  | 0 => .node (leafSymbol kind) []
  | depth + 1 => .node (unarySymbol kind) [chain kind depth]

/-- The chain class has one member at each positive size. -/
def chainClasses (kind : Bool) : Nat → List (Term Nat)
  | 0 => []
  | depth + 1 => [chain kind depth]

/-- A chain's node count is its unary depth plus one. -/
theorem chain_size (kind : Bool) (depth : Nat) : nodeSize (chain kind depth) = depth + 1 := by
  induction depth with
  | zero => simp [chain, nodeSize]
  | succ depth ih => simp [chain, nodeSize, ih]

/-- The two chain languages are disjoint at every pair of depths. -/
theorem chains_disjoint (first second : Nat) : chain false first ≠ chain true second := by
  cases first <;> cases second <;> simp [chain, leafSymbol, unarySymbol]

/-- The actual grouping of the repeated A child is A first, then B. -/
theorem root_groups : CompactGroups.childGroups 3 [[0, 2]] = [[0, 2], [1]] := by
  cbv

/-- The source group constructor restores the repeated A child at its last slot. -/
theorem assemble_pair (symbol : Symbol) (first second : Term Symbol) :
    assemble symbol 3 [[0, 2], [1]] [first, second] = .node symbol [first, second, first] := by
  rfl

/-- The root class executes the grouped row against the two chain indexes. -/
def familyClass (size : Nat) : List (Term Nat) :=
  rowClass chainClasses 4 [false, true, false] [[0, 2]] size

/-- One finite source table contains the root and the two recursive chains. -/
def table : Option Bool → List (Row (Option Bool) Nat (List (List Nat)))
  | none => [⟨4, [some false, some true, some false], [[0, 2]]⟩]
  | some kind => [⟨leafSymbol kind, [], []⟩, ⟨unarySymbol kind, [some kind], []⟩]

/-- The three-state class worker uses the same chain classes at every query size. -/
def tableClasses : Option Bool → Nat → List (Term Nat)
  | none, size => familyClass size
  | some kind, size => chainClasses kind size

/-- These explicit classes satisfy every literal grouped row equation of the fixed table. -/
theorem table_equation (state : Option Bool) (size : Nat) :
    tableClasses state size = (table state).flatMap fun row =>
      rowClass tableClasses row.label row.children row.constraint size := by
  cases state with
  | none =>
      simp only [table, tableClasses, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      unfold familyClass rowClass
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, root_groups,
        List.foldl_cons, List.foldl_nil]
      rfl
  | some kind =>
      simp only [table, tableClasses, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [nullary_rowClass, unary_rowClass]
      cases size with
      | zero => simp [chainClasses]
      | succ depth =>
          cases depth with
          | zero => simp [chainClasses, chain, tableClasses]
          | succ depth => simp [chainClasses, chain, tableClasses]

/-- The root uses one scaled A product and then the unscaled B product. -/
theorem familyClass_eq (size : Nat) :
    familyClass size =
      (extendForests (extendForests seed (scaled 2 (chainClasses false)))
        (chainClasses true) size).map (assemble 4 3 [[0, 2], [1]]) := by
  unfold familyClass rowClass
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, root_groups,
    List.foldl_cons, List.foldl_nil]
  rfl

/-- One increasing candidate has A depth `offset` and the required B depth. -/
def sample (m offset : Nat) : Term Nat :=
  .node 4 [chain false offset, chain true (2 * (m - offset - 1)), chain false offset]

/-- Retain A depths zero through m-1 in their increasing order. -/
def family (m : Nat) : List (Term Nat) := (List.range m).map (sample m)

/-- The proposed subsequence has exactly m terms. -/
theorem family_length (m : Nat) : (family m).length = m := by simp [family]

/-- Every selected term has the requested exact node count. -/
theorem sample_size (m offset : Nat) (within : offset < m) :
    nodeSize (sample m offset) = 2 * m + 2 := by
  simp only [sample, nodeSize, List.foldr_cons, List.foldr_nil, chain_size]
  omega

/-- The selected last-child sizes are strictly increasing. -/
theorem family_increasing (m : Nat) :
    (family m).Pairwise (fun first second => lastChildSize first < lastChildSize second) := by
  apply List.pairwise_map.mpr
  exact List.pairwise_lt_range.imp (fun earlier => by
    simpa [sample, lastChildSize, chain_size] using Nat.add_lt_add_right earlier 1)

private theorem increasing_indices_sublist (indices : List Nat) (limit : Nat)
    (increasing : indices.Pairwise (· < ·)) (bounded : ∀ index ∈ indices, index < limit) :
    indices.Sublist (List.range limit) := by
  induction indices using RecursiveSize.snoc_induction generalizing limit with
  | empty => exact List.nil_sublist _
  | step before last ih =>
      have parts := List.pairwise_append.mp increasing
      have previous := ih last parts.1
        (fun index present => parts.2.2 index present last (by simp))
      have appended : (before ++ [last]).Sublist (List.range (last + 1)) := by
        rw [List.range_succ]
        exact previous.append (.refl _)
      have lastBound := bounded last (by simp)
      exact appended.trans (List.range_sublist.mpr (by omega))

private theorem flatMap_sublist {A B : Type} (block : A → List B)
    {before after : List A} (included : before.Sublist after) :
    (before.flatMap block).Sublist (after.flatMap block) := by
  induction after generalizing before with
  | nil => cases included; exact .slnil
  | cons item rest ih =>
      cases included with
      | cons _ tail =>
          exact (ih tail).trans (List.sublist_append_right (block item) (rest.flatMap block))
      | cons_cons _ tail => exact (List.Sublist.refl (block item)).append (ih tail)

private theorem selected_sublist_flatMap {A B : Type} (block : A → List B)
    {owners : List A} {selected : List B}
    (paired : All₂ (fun owner value => value ∈ block owner) owners selected) :
    selected.Sublist (owners.flatMap block) := by
  induction paired with
  | nil => exact .slnil
  | cons member tail ih => exact (List.singleton_sublist.mpr member).append ih

private theorem map_paired {A B C : Type} (items : List A) (left : A → B) (right : A → C)
    (relation : B → C → Prop) (each : ∀ item ∈ items, relation (left item) (right item)) :
    All₂ relation (items.map left) (items.map right) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
      exact .cons (each item (by simp))
        (ih (fun value present => each value (List.mem_cons_of_mem item present)))

private theorem scaled_chain (factor depth : Nat) (positive : 0 < factor) (kind : Bool) :
    scaled factor (chainClasses kind) (factor * (depth + 1)) = [chain kind depth] := by
  by_cases one : factor = 1
  · subst factor
    simp [scaled, chainClasses]
  · simp [scaled, one, Nat.mul_div_cancel_left (depth + 1) positive, chainClasses]

private theorem first_group_member (offset : Nat) :
    [chain false offset] ∈
      extendForests seed (scaled 2 (chainClasses false)) (2 * offset + 3) := by
  apply List.mem_flatMap.mpr
  refine ⟨1, List.mem_range.mpr (by omega), ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨[], by simp [seed], ?_⟩
  apply List.mem_map.mpr
  refine ⟨chain false offset, ?_, rfl⟩
  have size : 2 * offset + 3 - 1 = 2 * (offset + 1) := by omega
  rw [size, scaled_chain 2 offset (by omega) false]
  simp

/-- The actual grouped root recurrence contains m terms with increasing
last-child sizes at size 2*m+2. -/
theorem family_increasing_sublist (m : Nat) :
    (family m).Sublist (familyClass (2 * m + 2)) := by
  let prefixSize := fun offset => 2 * offset + 3
  let choice := fun offset =>
    [chain false offset, chain true (2 * (m - offset - 1))]
  let built := extendForests seed (scaled 2 (chainClasses false))
  let block := fun left => (built left).flatMap fun selected =>
    (chainClasses true (2 * m + 2 - left)).map fun child => selected ++ [child]
  have increasing : ((List.range m).map prefixSize).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    exact List.pairwise_lt_range.imp (fun earlier => by
      dsimp [prefixSize]
      omega)
  have bounded : ∀ index ∈ (List.range m).map prefixSize, index < 2 * m + 3 := by
    intro index present
    obtain ⟨offset, within, rfl⟩ := List.mem_map.mp present
    have bound := List.mem_range.mp within
    dsimp [prefixSize]
    omega
  have indices := increasing_indices_sublist _ _ increasing bounded
  have paired : All₂ (fun owner value => value ∈ block owner)
      ((List.range m).map prefixSize) ((List.range m).map choice) := by
    apply map_paired
    intro offset within
    have bound := List.mem_range.mp within
    apply List.mem_flatMap.mpr
    refine ⟨[chain false offset], first_group_member offset, ?_⟩
    apply List.mem_map.mpr
    refine ⟨chain true (2 * (m - offset - 1)), ?_, rfl⟩
    have size : 2 * m + 2 - prefixSize offset = 2 * (m - offset - 1) + 1 := by
      dsimp [prefixSize]
      omega
    rw [size]
    simp [chainClasses]
  have selected := (selected_sublist_flatMap block paired).trans (flatMap_sublist block indices)
  have mapped := selected.map (assemble 4 3 [[0, 2], [1]])
  rw [familyClass_eq]
  change ((List.range m).map (fun offset =>
    Term.node 4 [chain false offset, chain true (2 * (m - offset - 1)), chain false offset])).Sublist
      (((List.range (2 * m + 3)).flatMap block).map (assemble 4 3 [[0, 2], [1]]))
  simpa only [List.map_map, Function.comp_def, choice, assemble_pair] using mapped

/-- No fixed reference graph has all the class lists of this grouped recurrence.
The conclusion does not attach the recurrence to the public dispatcher. -/
theorem familyClass_not_reference {State : Type} (A : Automaton State Nat) (root : State) :
    ∃ size, familyClass size ≠ SourceSizedReference.classes A size root := by
  let m := (A root).length + 1
  refine ⟨2 * m + 2, ?_⟩
  intro same
  have included := family_increasing_sublist m
  rw [same] at included
  have bound := classes_increasing_sublist_bound A root (2 * m + 2)
    (family m) included (family_increasing m)
  rw [family_length] at bound
  dsimp [m] at bound
  omega

end MicroCFTA.SourceSizedGroupedChainOrder
