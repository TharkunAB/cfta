import MicroCFTA.MergedFreshOrdinaryGraphOrigins
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

/-!
# Finite open observations of the actual repaired epsilon graph

Depth zero retains all exposed bare reference names. Each additional depth
also retains complete row symbols and guards, with ordered child relations.
Rows match by occurrence. Normalization need not preserve their list order.
The view heap determines every Mu successor by actual repaired execution.
-/
namespace MicroCFTA.SourceCurrentOpenObservations
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedBinderProtocol (Reference NodeKey)
open InternedEdgeResidency (nodeEdges)
open MergedFreshOrdinaryGraph
open Productivity Language

/-- An actual epsilon path exposes this exact bare reference. -/
def ReferenceOrigin [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (name : Reference) : Prop :=
  Reachable (successors view) roots (.reference name)

/-- Matching rows retain the full symbol and guard and relate children in order. -/
def RowMatch (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : EdgeValue Symbol Guard) : Prop :=
  first.entry.key.symbol = second.entry.key.symbol ∧
    first.entry.key.constraint = second.entry.key.constraint ∧
    All₂ relation first.children second.children

/-- Common-name observations retain references at every depth and rows up to the selected depth. -/
def Same [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → State Symbol Guard → List (Value Symbol Guard) → List (Value Symbol Guard) → Prop
  | 0, view, first, second => ∀ name, ReferenceOrigin view first name ↔ ReferenceOrigin view second name
  | depth + 1, view, first, second =>
      (∀ name, ReferenceOrigin view first name ↔ ReferenceOrigin view second name) ∧
      (∀ row, Origin view first row → ∃ other, Origin view second other ∧
        RowMatch (fun left right => Same depth view [left] [right]) row other) ∧
      (∀ row, Origin view second row → ∃ other, Origin view first other ∧
        RowMatch (fun left right => Same depth view [left] [right]) row other)

private theorem all_refl {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    (reflexive : ∀ value, relation value value) (values : List (Value Symbol Guard)) :
    All₂ relation values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (reflexive value) ih

private theorem all_symm {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    (symmetric : ∀ first second, relation first second → relation second first)
    {first second : List (Value Symbol Guard)} (actual : All₂ relation first second) :
    All₂ relation second first := by
  induction actual with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (symmetric _ _ pair) ih

private theorem all_trans {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    (transitive : ∀ first middle last, relation first middle → relation middle last → relation first last)
    {first middle last : List (Value Symbol Guard)}
    (left : All₂ relation first middle) (right : All₂ relation middle last) :
    All₂ relation first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons pair rest ih =>
      cases right with
      | cons next later => exact .cons (transitive _ _ _ pair next) (ih later)

/-- Every actual seed list has the same finite observations as itself. -/
theorem Same.refl [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (roots : List (Value Symbol Guard)) : Same depth view roots roots := by
  induction depth generalizing roots with
  | zero => exact fun _ => Iff.rfl
  | succ depth ih =>
      have row (value : EdgeValue Symbol Guard) :
          RowMatch (fun left right => Same depth view [left] [right]) value value :=
        ⟨rfl, rfl, all_refl (fun child => ih [child]) value.children⟩
      exact ⟨fun _ => Iff.rfl, fun value origin => ⟨value, origin, row value⟩,
        fun value origin => ⟨value, origin, row value⟩⟩

/-- Both directions of row matching preserve symmetry without an ordering assumption on rows. -/
theorem Same.symm [DecidableEq (EdgeKey Symbol Guard)] {depth : Nat} {view : State Symbol Guard}
    {first second : List (Value Symbol Guard)} (actual : Same depth view first second) :
    Same depth view second first := by
  induction depth generalizing first second with
  | zero => exact fun name => (actual name).symm
  | succ depth ih =>
      have reverse {left right : EdgeValue Symbol Guard}
          (matched : RowMatch (fun a b => Same depth view [a] [b]) left right) :
          RowMatch (fun a b => Same depth view [a] [b]) right left :=
        ⟨matched.1.symm, matched.2.1.symm, all_symm (fun _ _ pair => ih pair) matched.2.2⟩
      exact ⟨fun name => (actual.1 name).symm,
        fun row origin => let ⟨other, present, matched⟩ := actual.2.2 row origin
          ⟨other, present, reverse matched⟩,
        fun row origin => let ⟨other, present, matched⟩ := actual.2.1 row origin
          ⟨other, present, reverse matched⟩⟩

/-- Ordered child relations compose through the same intermediate row occurrence. -/
theorem Same.trans [DecidableEq (EdgeKey Symbol Guard)] {depth : Nat} {view : State Symbol Guard}
    {first middle last : List (Value Symbol Guard)}
    (left : Same depth view first middle) (right : Same depth view middle last) :
    Same depth view first last := by
  induction depth generalizing first middle last with
  | zero => exact fun name => (left name).trans (right name)
  | succ depth ih =>
      have compose {a b c : EdgeValue Symbol Guard}
          (first : RowMatch (fun x y => Same depth view [x] [y]) a b)
          (second : RowMatch (fun x y => Same depth view [x] [y]) b c) :
          RowMatch (fun x y => Same depth view [x] [y]) a c :=
        ⟨first.1.trans second.1, first.2.1.trans second.2.1,
          all_trans (fun _ _ _ one two => ih one two) first.2.2 second.2.2⟩
      refine ⟨fun name => (left.1 name).trans (right.1 name), ?_, ?_⟩
      · intro row origin
        obtain ⟨next, present, matched⟩ := left.2.1 row origin
        obtain ⟨last, final, matchedLast⟩ := right.2.1 next present
        exact ⟨last, final, compose matched matchedLast⟩
      · intro row origin
        obtain ⟨next, present, matched⟩ := right.2.2 row origin
        obtain ⟨first, initial, matchedFirst⟩ := left.2.2 next present
        exact ⟨first, initial, compose matched matchedFirst⟩

/-- Dropping one row depth preserves the reference observations and every remaining row relation. -/
theorem Same.lower [DecidableEq (EdgeKey Symbol Guard)] {depth : Nat} {view : State Symbol Guard}
    {first second : List (Value Symbol Guard)} (actual : Same (depth + 1) view first second) :
    Same depth view first second := by
  induction depth generalizing first second with
  | zero => exact actual.1
  | succ depth ih =>
      have lower {left right : EdgeValue Symbol Guard}
          (matched : RowMatch (fun a b => Same (depth + 1) view [a] [b]) left right) :
          RowMatch (fun a b => Same depth view [a] [b]) left right :=
        ⟨matched.1, matched.2.1, All₂.imp (fun _ _ pair => ih pair) matched.2.2⟩
      exact ⟨actual.1,
        fun row origin => let ⟨other, present, matched⟩ := actual.2.1 row origin
          ⟨other, present, lower matched⟩,
        fun row origin => let ⟨other, present, matched⟩ := actual.2.2 row origin
          ⟨other, present, lower matched⟩⟩

/-- Exact reference and physical row origins supply all finite observations. -/
theorem of_origins [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (first second : List (Value Symbol Guard))
    (references : ∀ name, ReferenceOrigin view first name ↔ ReferenceOrigin view second name)
    (rows : ∀ row, Origin view first row ↔ Origin view second row) : Same depth view first second := by
  cases depth with
  | zero => exact references
  | succ depth =>
      have matched (row : EdgeValue Symbol Guard) :
          RowMatch (fun a b => Same depth view [a] [b]) row row :=
        ⟨rfl, rfl, all_refl (fun child => Same.refl depth view [child]) row.children⟩
      exact ⟨references, fun row origin => ⟨row, (rows row).mp origin, matched row⟩,
        fun row origin => ⟨row, (rows row).mpr origin, matched row⟩⟩

/-- Every exposed reference starts at one actual seed occurrence. -/
theorem reference_seeds [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (name : Reference) :
    ReferenceOrigin view roots name ↔ ∃ root ∈ roots, ReferenceOrigin view [root] name := by
  constructor
  · intro actual
    induction actual with
    | seed present => exact ⟨_, present, .seed List.mem_cons_self⟩
    | step _ next ih =>
        obtain ⟨root, present, path⟩ := ih
        exact ⟨root, present, .step path next⟩
  · rintro ⟨root, present, actual⟩
    exact EpsilonUnion.change_seeds _ [root] roots
      (fun value member => (List.mem_singleton.mp member) ▸ Reachable.seed present) _ actual

/-- A nonreference root delegates every exposed reference to its actual epsilon successors. -/
theorem reference_expand [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (root : Value Symbol Guard) (different : ∀ name, root ≠ .reference name) (name : Reference) :
    ReferenceOrigin view [root] name ↔ ReferenceOrigin view (successors view root) name := by
  constructor
  · intro actual
    have separated : Value.reference name = root ∨
        Reachable (successors view) (successors view root) (.reference name) := by
      induction actual with
      | seed present => exact Or.inl (List.mem_singleton.mp present)
      | step _ next ih =>
          rcases ih with rfl | path
          · exact Or.inr (.seed next)
          · exact Or.inr (.step path next)
    exact separated.elim (fun same => False.elim (different name same.symm)) id
  · intro actual
    exact EpsilonUnion.change_seeds _ (successors view root) [root]
      (fun value member => Reachable.step (.seed List.mem_cons_self) member) _ actual

/-- Bare references remain observable even though they have no constructor rows. -/
theorem reference_exact [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (first second : Reference) : ReferenceOrigin view [.reference first] second ↔ second = first := by
  constructor
  · intro actual
    have same : Value.reference second = (Value.reference first : Value Symbol Guard) := by
      induction actual with
      | seed present => exact List.mem_singleton.mp present
      | step _ next ih => simp only [ih, successors, List.not_mem_nil] at next
    exact Value.reference.inj same
  · intro same
    subst second
    exact .seed List.mem_cons_self

/-- A union and its literal seed members have the same open observations at every depth. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (entry : Interned NodeKey) (members : List (Value Symbol Guard)) (level : Nat) (free : List Reference) :
    Same depth view [.union entry members level free] members := by
  apply of_origins depth view _ _
  · intro name
    exact reference_expand view _ (fun _ impossible => by cases impossible) name
  · intro row
    exact (origin_union view entry members level free row).trans (origin_seeds view members row).symm

/-- A literal completed Mu unfolding preserves every open observation in that exact view heap. -/
theorem unfold [DecidableEq (EdgeKey Symbol Guard)] (depth : Nat) (view : State Symbol Guard)
    (entry : Interned NodeKey) (body cachedDepth ordinary result : Value Symbol Guard)
    (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body cachedDepth ordinary) view =
      .done result after) : Same depth view [.mu entry body cachedDepth ordinary] [result] := by
  apply of_origins depth view _ _
  · intro name
    have expanded := reference_expand view (.mu entry body cachedDepth ordinary)
      (fun _ impossible => by cases impossible) name
    simpa only [successors, actual] using expanded
  · exact fun row => origin_unfold view entry body cachedDepth ordinary result after actual row

/-- Complete initial semantic caches construct their own Mu unfolding and all its open observations. -/
theorem unfold_complete [DecidableEq (EdgeKey Symbol Guard)] (view : State Symbol Guard)
    (entry : Interned NodeKey) (body cachedDepth ordinary : Value Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap view) (covered : Covered [] view)
    (available : Available view (.mu entry body cachedDepth ordinary)) :
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body cachedDepth ordinary) view = .done result after ∧
      SourceRecursiveIntersectionSemanticHeap.SemanticHeap after ∧ Covered [] after ∧ Available after result ∧
      Grows view after ∧ Extends view.nodes.issued after.nodes.issued ∧
      ∀ depth, Same depth view [.mu entry body cachedDepth ordinary] [result] := by
  obtain ⟨result, after, actual, context, heap, retained, output, growth, history⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body cachedDepth ordinary) view
      semantic.1 available semantic.2 covered
  exact ⟨result, after, actual, ⟨context, heap⟩, retained, output, growth, history,
    fun depth => unfold depth view entry body cachedDepth ordinary result after actual⟩

end MicroCFTA.SourceCurrentOpenObservations
