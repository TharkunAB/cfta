import MicroCFTA.EqualityReduction
import MicroCFTA.GuardConjunction

/-!
# Recursive barriers in equality reduction

The gate reads node tags and cached recursion metadata. It never unfolds a
binder. Every recursive call consumes a child index. Classes rejected by the
gate remain in the edge constraint and are still checked at membership.
-/
namespace MicroCFTA.RecursiveReductionBarrier
open Language EqualityNormalize EqualityReduction

/-- The source node cases inspected by the gate. Constructor rows retain only children. -/
inductive View (Node : Type) where
  | empty | reference | binder | union
  | branches (children : List (List Node))

/-- The source uses cached nested-binder depth and free-reference sets. -/
structure Read (Node : Type) where
  view : Node → View Node
  nested : Node → Nat
  free : Node → List Nat

/-- The fast path excludes every stored binder and free reference below the node. -/
def finite (read : Read Node) (node : Node) : Bool :=
  read.nested node == 0 && (read.free node).isEmpty

/-- Rec, Mu, and interned union are opaque barriers, even at a path endpoint. -/
def isOpaque : View Node → Bool
  | .reference | .binder | .union => true
  | _ => false

/-- Source `nodeMeetsRecursion`, with no binder unfolding or reference lookup. -/
def nodeMeets (read : Read Node) : Path → Node → Bool
  | path, node =>
    if isOpaque (read.view node) then true
    else if finite read node then false
    else match path with
      | [] => true
      | index :: rest => match read.view node with
        | .branches edges => edges.any (fun children =>
            ((children[index]?).map (nodeMeets read rest)).getD false)
        | _ => false

/-- Source `meetsRecursion` starts below the constrained edge's root. -/
def meets (read : Read Node) (children : List Node) : Path → Bool
  | [] => false
  | index :: rest => ((children[index]?).map (nodeMeets read rest)).getD false

/-- A class is skipped when any one of its paths reaches a barrier. -/
def blocked (read : Read Node) (children : List Node) (paths : Class) : Bool :=
  paths.any (meets read children)

/-- Install the exact source gate without changing any narrowing primitive. -/
def guarded (read : Read Node) (ops : Operations Node Symbol) : Operations Node Symbol :=
  { ops with blocked := blocked read }

/-- The metadata shortcut is exactly zero nested binders and no free reference. -/
theorem finite_iff (read : Read Node) (node : Node) :
    finite read node = true ↔ read.nested node = 0 ∧ read.free node = [] := by
  simp [finite]

/-- Every explicit recursive or union node is blocked before the metadata shortcut. -/
theorem opaque_blocked (read : Read Node) (node : Node) (path : Path)
    (barrier : isOpaque (read.view node) = true) : nodeMeets read path node = true := by
  cases path <;> simp [nodeMeets, barrier]

/-- A nonopaque node with finite metadata is safe at every requested position. -/
theorem finite_clear (read : Read Node) (node : Node) (path : Path)
    (plain : isOpaque (read.view node) = false) (closed : finite read node = true) :
    nodeMeets read path node = false := by cases path <;> simp [nodeMeets, plain, closed]

/-- An endpoint is safe exactly when it is nonopaque and contains no recursive data. -/
theorem endpoint_clear (read : Read Node) (node : Node) :
    nodeMeets read [] node = false ↔ isOpaque (read.view node) = false ∧
      read.nested node = 0 ∧ read.free node = [] := by
  simp only [nodeMeets]
  cases kind : isOpaque (read.view node) <;> cases closed : finite read node <;>
    simp_all [finite]

/-- The branch case is exactly the source traversal through each edge's child list. -/
theorem branch_step (read : Read Node) (node : Node) (edges : List (List Node))
    (view : read.view node = .branches edges) (openNode : finite read node = false)
    (index : Nat) (rest : Path) :
    nodeMeets read (index :: rest) node = edges.any (fun children => meets read children (index :: rest)) := by
  simp [nodeMeets, view, isOpaque, openNode, meets]

/-- Selected classes are precisely the original classes whose complete path checks all pass. -/
theorem selected_iff (read : Read Node) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node) (paths : Class) :
    paths ∈ selectedClasses (guarded read ops) classes nodes ↔
      paths ∈ classes ∧ ∀ path ∈ paths, meets read nodes path = false := by
  simp [selectedClasses, guarded, blocked, List.any_eq_false]

/-- Finite nonopaque children remain eligible for every requested path. -/
theorem finite_children_clear (read : Read Node) (nodes : List Node)
    (plain : ∀ node ∈ nodes, isOpaque (read.view node) = false)
    (closed : ∀ node ∈ nodes, finite read node = true) (path : Path) : meets read nodes path = false := by
  cases path with
  | nil => rfl
  | cons index rest =>
      simp only [meets]
      cases found : nodes[index]? with
      | none => rfl
      | some node =>
          have member := List.mem_of_getElem? found
          simp only [Option.map_some, Option.getD_some]
          exact finite_clear read node rest (plain node member) (closed node member)

/-- The new gate leaves the selected class list unchanged for finite nonopaque children. -/
theorem finite_classes_selected (read : Read Node) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node)
    (plain : ∀ node ∈ nodes, isOpaque (read.view node) = false)
    (closed : ∀ node ∈ nodes, finite read node = true) :
    selectedClasses (guarded read ops) classes nodes = classes := by
  apply List.filter_eq_self.mpr
  intro paths _
  simp [guarded, blocked, List.any_eq_false, finite_children_clear read nodes plain closed]

/-- A blocked path removes the whole class from narrowing, not from the edge's stored constraint. -/
theorem class_skipped (read : Read Node) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node) (paths : Class) (path : Path)
    (member : path ∈ paths) (barrier : meets read nodes path = true) :
    paths ∉ selectedClasses (guarded read ops) classes nodes := by
  intro selected
  have clear := ((selected_iff read ops classes nodes paths).mp selected).2 path member
  rw [barrier] at clear
  cases clear

/-- Gate selection preserves every original class; it changes no primitive language law. -/
theorem guarded_laws (read : Read Node) (ops : Operations Node Symbol) (laws : Laws ops) : Laws (guarded read ops) where
  empty := laws.empty
  intersect := laws.intersect
  project := laws.project
  require_narrow := laws.require_narrow
  require_keep := laws.require_keep
  edit_narrow := laws.edit_narrow
  edit_keep := laws.edit_keep
  contradiction := laws.contradiction

/-- The repaired gate preserves every term satisfying the unchanged equality constraints. -/
theorem completed_exact [DecidableEq Node] (read : Read Node) (ops : Operations Node Symbol) (laws : Laws ops)
    (localClasses inherited : Constraints) (active : Active localClasses) (fuel : Nat) (before after : List Node)
    (completed : reduce (guarded read ops) localClasses inherited fuel before = some after) (term : Term Symbol) :
    (Forest ops after term ∧ Satisfies term localClasses ∧ Satisfies term inherited) ↔
      Forest ops before term ∧ Satisfies term localClasses ∧ Satisfies term inherited :=
  constrained_reduce_exact (guarded read ops) (guarded_laws read ops laws)
    localClasses inherited active fuel before after completed term

/-- If every class encounters a barrier, the selected narrowing list is empty. -/
theorem all_skipped (read : Read Node) (ops : Operations Node Symbol)
    (classes : Constraints) (nodes : List Node)
    (barriers : ∀ paths ∈ classes, ∃ path ∈ paths, meets read nodes path = true) :
    selectedClasses (guarded read ops) classes nodes = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro paths member
  obtain ⟨path, present, blocked⟩ := barriers paths ((selected_iff read ops classes nodes paths).mp member).1
  exact class_skipped read ops classes nodes paths path present blocked member

/-- A fully blocked consistent pass reaches the source identity fixed point immediately. -/
theorem blocked_pass_identity [DecidableEq Node] (read : Read Node) (ops : Operations Node Symbol)
    (localClasses inherited : Constraints) (nodes : List Node)
    (consistent : ops.contradictory localClasses inherited = false)
    (noEmpty : ops.empty ∉ nodes) (requireEmpty : ops.requireAll [] nodes = nodes)
    (barriers : ∀ paths ∈ localClasses, ∃ path ∈ paths, meets read nodes path = true) :
    pass (guarded read ops) localClasses inherited nodes = nodes := by
  unfold pass
  split
  · rfl
  · change (if ops.contradictory localClasses inherited then _ else _) = _
    rw [consistent]
    simp only [Bool.false_eq_true, ↓reduceIte, all_skipped read ops localClasses nodes barriers,
      List.flatten_nil, List.foldr_nil]
    change propagate (guarded read ops) (ops.requireAll [] nodes) = nodes
    rw [requireEmpty]
    simp [propagate, guarded, noEmpty]

/-- Recursive classes that the gate skips do not enter the unbounded reduction loop. -/
theorem blocked_terminates [DecidableEq Node] (read : Read Node) (ops : Operations Node Symbol)
    (localClasses inherited : Constraints) (nodes : List Node)
    (consistent : ops.contradictory localClasses inherited = false)
    (noEmpty : ops.empty ∉ nodes) (requireEmpty : ops.requireAll [] nodes = nodes)
    (barriers : ∀ paths ∈ localClasses, ∃ path ∈ paths, meets read nodes path = true) :
    reduce (guarded read ops) localClasses inherited 1 nodes = some nodes := by
  simp [reduce, blocked_pass_identity read ops localClasses inherited nodes consistent noEmpty requireEmpty barriers]

/-- One step in the gate's child traversal always consumes one path index. -/
theorem descent_decreases (index : Nat) (rest : Path) : rest.length < (index :: rest).length := by simp

/-- A bounded instrument rejects a path if its recursion budget is exhausted. -/
def nodeMeetsBounded (read : Read Node) : Nat → Path → Node → Bool
  | 0, _, _ => true
  | fuel + 1, path, node =>
    if isOpaque (read.view node) then true
    else if finite read node then false
    else match path with
      | [] => true
      | index :: rest => match read.view node with
        | .branches edges => edges.any (fun children =>
            ((children[index]?).map (nodeMeetsBounded read fuel rest)).getD false)
        | _ => false

/-- Path length alone bounds the entire recursive descent, even if the viewed graph has cycles. -/
theorem bounded_exact (read : Read Node) (fuel : Nat) (path : Path) (node : Node)
    (enough : path.length < fuel) : nodeMeetsBounded read fuel path node = nodeMeets read path node := by
  induction fuel generalizing path node with
  | zero => omega
  | succ fuel ih =>
      cases path with
      | nil => simp only [nodeMeetsBounded, nodeMeets]
      | cons index rest =>
          simp only [nodeMeetsBounded, nodeMeets]
          by_cases barrier : isOpaque (read.view node) = true
          · simp [barrier]
          · simp only [barrier]
            by_cases closed : finite read node = true
            · simp [closed]
            · simp only [closed]
              cases view : read.view node <;> simp only [Bool.false_eq_true, ↓reduceIte]
              rename_i edges
              congr 1
              funext children
              cases found : children[index]? with
              | none => rfl
              | some child => simpa only [Option.map_some, Option.getD_some] using ih rest child (by simpa using enough)

/-- An executable fixture separates recursive paths from an acyclic sibling. -/
def fixture : Read Nat where
  view
    | 0 => .binder
    | 1 => .branches [[0]]
    | 2 => .branches [[]]
    | 3 => .branches [[2, 0]]
    | 4 => .reference
    | _ => .union
  nested
    | 0 | 1 | 3 => 1
    | _ => 0
  free
    | 4 => [7]
    | _ => []

/-- The exact gate blocks recursive endpoints and crossings but permits the unaffected sibling. -/
theorem fixture_cases :
    meets fixture [0, 2] [0] = true ∧
    meets fixture [1, 2] [0] = true ∧
    meets fixture [0, 2] [0, 0] = true ∧
    meets fixture [1, 2] [0, 0] = true ∧
    meets fixture [4, 2] [0] = true ∧
    meets fixture [5, 2] [0] = true ∧
    blocked fixture [3, 2] [[0, 0], [1]] = false := by decide +kernel

namespace LeafTriple
open SourceGuards GuardConjunction

/-- One simultaneous equality round on three equally labelled finite leaf nodes. -/
def round [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool)
    (state : Guard Formula × Guard Formula × Guard Formula) : Guard Formula × Guard Formula × Guard Formula :=
  let (a, b, c) := state
  (merge le (merge le c b) a, merge le (merge le c a) b, merge le (merge le b a) c)

/-- The source identity-based loop restricted to those leaf residual guards. -/
def run [DecidableEq (Guard Formula)] (le : Guard Formula → Guard Formula → Bool) :
    Nat → (Guard Formula × Guard Formula × Guard Formula) → Option (Guard Formula × Guard Formula × Guard Formula)
  | 0, _ => none
  | fuel + 1, before =>
    let after := round le before
    if after = before then some before else run le fuel after

/-- One round computes exactly one canonical common residual, irrespective of the initial guard syntax. -/
theorem round_normalizes [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (a b c : Guard Formula) :
    round le (a, b, c) =
      let common := normalize le (.and [a, b, c])
      (common, common, common) := by
  have first : merge le (merge le c b) a = normalize le (.and [a, b, c]) := by
    apply normalize_eq le trans total antisymm
    intro atom
    simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, merge_mem]
    grind
  have second : merge le (merge le c a) b = normalize le (.and [a, b, c]) := by
    apply normalize_eq le trans total antisymm
    intro atom
    simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, merge_mem]
    grind
  have third : merge le (merge le b a) c = normalize le (.and [a, b, c]) := by
    apply normalize_eq le trans total antisymm
    intro atom
    simp only [atoms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, merge_mem]
    grind
  simp only [round, first, second, third]

/-- A second equality round cannot grow the canonical finite leaf representation. -/
theorem round_fixed [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (state : Guard Formula × Guard Formula × Guard Formula) :
    round le (round le state) = round le state := by
  rcases state with ⟨a, b, c⟩
  rw [round_normalizes le trans total antisymm a b c]
  simp only [round, merge_normalized_self le trans total antisymm]

/-- The former three-leaf growth case now terminates after at most two executed passes. -/
theorem terminates_two [DecidableEq (Guard Formula)]
    (le : Guard Formula → Guard Formula → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (antisymm : ∀ a b, le a b → le b a → a = b)
    (state : Guard Formula × Guard Formula × Guard Formula) : run le 2 state = some (round le state) := by
  by_cases fixed : round le state = state
  · simp [run, fixed]
  · simp [run, fixed, round_fixed le trans total antisymm state]

end LeafTriple

end MicroCFTA.RecursiveReductionBarrier
