import MicroCFTA.SourceCurrentPositiveInheritedChildSeparation

/-!
# Positive path counts under inherited equality classes

The finite count identifies positive paths under the current inherited relation.
Actual physical child descent reflects the combined relation. A supplied
backwards relation bounds each child count. A nonplain source row makes the
bound strict. This module does not produce that relation from runtime work.
-/
namespace MicroCFTA.SourceCurrentPositiveQuotientCount
open EqualityNormalize SourceEqualityClassOrder InternedConstructorTemplates
open SourceCurrentRequiredPositivePosition (PositiveAt)
open SourceCurrentNormalizedChildSeparation (Rel)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Row" => EdgeValue Symbol Guard

/- Copy PositiveOwnerPair23–74 exactly. Both earlier enumerations are private. -/
private def candidates : Nat → Node → List Path
  | 0, _ => []
  | fuel + 1, .node _ rows _ _ =>
      [] :: rows.flatMap (fun row => row.children.zipIdx.flatMap
        (fun child => (candidates fuel child.1).map (child.2 :: ·)))
  | fuel + 1, .union _ members _ _ =>
      [] :: members.flatMap (candidates fuel)
  | _ + 1, _ => [[]]

private theorem candidates_complete {value path} (positive : PositiveAt value path) :
    ∀ fuel, InternedValueMass.value value < fuel → path ∈ candidates fuel value := by
  induction positive with
  | root rowIndex row selected nonplain =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel => exact List.mem_cons_self
  | @child entry rows depth free rowIndex childIndex row child selected chosen path rest ih =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel =>
          have smaller := InternedValueMass.node_child_lt entry rows depth free row
            (List.mem_of_getElem? selected) child (List.mem_of_getElem? chosen)
          have present := ih fuel (by omega)
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨row, List.mem_of_getElem? selected, ?_⟩
          apply List.mem_flatMap.mpr
          refine ⟨(child, childIndex), List.mk_mem_zipIdx_iff_getElem?.mpr chosen, ?_⟩
          exact List.mem_map.mpr ⟨path, present, rfl⟩
  | @member entry members depth free memberIndex child selected path rest ih =>
      intro fuel bounded
      cases fuel with
      | zero => omega
      | succ fuel =>
          have smaller := InternedValueMass.union_member_lt entry members depth free child
            (List.mem_of_getElem? selected)
          exact List.mem_cons_of_mem [] (List.mem_flatMap.mpr
            ⟨child, List.mem_of_getElem? selected, ih fuel (by omega)⟩)

private noncomputable def positivePaths (value : Node) : List Path := by
  classical
  exact ((candidates (InternedValueMass.value value + 1) value).filter
    (fun path => decide (PositiveAt value path))).eraseDups

private theorem positivePaths_spec {value path} :
    path ∈ positivePaths value ↔ PositiveAt value path := by
  classical
  simp only [positivePaths, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun positive =>
    ⟨candidates_complete positive _ (by omega), positive⟩⟩

private theorem rel_symm {classes : Constraints} {left right : Path}
    (related : Rel classes left right) : Rel classes right left := by
  induction related with
  | refl path => exact .refl path
  | member paths selected left right first second suffix =>
      exact .member paths selected right left second first suffix
  | trans _ _ first second => exact .trans second first

private theorem rel_covers {classes others : Constraints} (covered : Covers classes others)
    {left right : Path} (related : Rel classes left right) : Rel others left right := by
  induction related with
  | refl path => exact .refl path
  | member paths selected left right first second suffix =>
      obtain ⟨larger, included, preserves⟩ := covered paths selected
      exact .member larger included left right (preserves left first) (preserves right second) suffix
  | trans _ _ first second => exact .trans first second

private theorem consistent {classes : Constraints}
    (fixed : congruenceStep classes = some classes) : isContradicting classes = false := by
  dsimp only [congruenceStep] at fixed
  split at fixed
  · cases fixed
  · rename_i condition
    have same := Option.some.inj fixed
    rw [same] at condition
    exact Bool.eq_false_iff.mpr condition


private theorem root_separate {classes : Constraints}
    (fixed : congruenceStep classes = some classes) {path : Path} (nonempty : path ≠ []) :
    ¬ Rel classes [] path := by
  intro related
  rcases SourceCurrentNormalizedChildSeparation.single fixed related with same |
      ⟨paths, selected, a, aMember, b, bMember, suffix, firstSame, secondSame⟩
  · exact nonempty same.symm
  have empty := List.append_eq_nil_iff.mp firstSame.symm
  rcases empty with ⟨rfl, rfl⟩
  simp only [List.append_nil] at secondSame
  have different : [] ≠ b := by
    intro same
    apply nonempty
    exact secondSame.trans same.symm
  exact consistent_subsumption_irreflexive _ (consistent fixed) paths selected
    ⟨[], aMember, b, bMember, ⟨b, rfl⟩, different⟩

private def relationSetoid (classes : Constraints) : Setoid Path where
  r := Rel classes
  iseqv := ⟨Rel.refl, fun related => rel_symm related, fun first second => .trans first second⟩

/-- Count the inherited-relation classes represented by positive natural child paths. -/
noncomputable def count (inherited : List Record) (value : Node) : Nat := by
  classical
  exact (((positivePaths value).map (Quotient.mk (relationSetoid (inherited.map Record.paths)))).eraseDups).length

/-- Actual descended records bound every backwards-linked child and strictly count a nonplain row. -/
theorem child_count
    (parents inherited : List Record)
    (coherent : ∀ record ∈ parents, SourceEqualityClassOrder.Coherent record)
    (fixed : congruenceStep (parents.map Record.paths) = some (parents.map Record.paths))
    (covered : Covers (inherited.map Record.paths) (parents.map Record.paths))
    (index : Nat) (child : Node) {entry depth free} {rows : List Row}
    (row : Row) (member : row ∈ rows)
    (back : ∀ q, PositiveAt child q →
      ∃ j p original, row.children[j]? = some original ∧ PositiveAt original p ∧
        Rel (parents.map Record.paths) (index :: q) (j :: p)) :
    count (SourceEqualityDescend.records index parents) child ≤
        count inherited (.node entry rows depth free) ∧
      (SourceMemoGate.plain row.entry.key.constraint = false →
        count (SourceEqualityDescend.records index parents) child <
          count inherited (.node entry rows depth free)) := by
  classical
  let fromPath : Path → Quotient (relationSetoid
      ((SourceEqualityDescend.records index parents).map Record.paths)) := Quotient.mk _
  let toPath : Path → Quotient (relationSetoid (inherited.map Record.paths)) := Quotient.mk _
  let owner : Node := .node entry rows depth free
  let sources := ((positivePaths child).map fromPath).eraseDups
  let targets := ((positivePaths owner).map toPath).eraseDups
  change sources.length ≤ targets.length ∧
    (SourceMemoGate.plain row.entry.key.constraint = false → sources.length < targets.length)
  have distinct : sources.Nodup := SymbolicDriver.eraseDups_nodup _
  obtain ⟨rowIndex, selected⟩ := List.mem_iff_getElem?.mp member
  let relation := fun (source : Quotient (relationSetoid
        ((SourceEqualityDescend.records index parents).map Record.paths)))
      (target : Quotient (relationSetoid (inherited.map Record.paths))) =>
    ∃ q ∈ positivePaths child, ∃ t ∈ positivePaths owner,
      fromPath q = source ∧ toPath t = target ∧ Rel (parents.map Record.paths) (index::q) t
  have total : ∀ source ∈ sources, ∃ target ∈ targets.erase (toPath []), relation source target := by
    intro source present
    obtain ⟨q, qMember, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp present)
    obtain ⟨j, p, original, chosen, positive, related⟩ := back q (positivePaths_spec.mp qMember)
    have targetMember : j::p ∈ positivePaths owner := positivePaths_spec.mpr
      (.child rowIndex j row original selected chosen positive)
    have different : toPath (j::p) ≠ toPath [] := by
      intro equal
      have inheritedRelated : Rel (inherited.map Record.paths) [] (j::p) := Quotient.exact equal.symm
      exact root_separate fixed (by simp) (rel_covers covered inheritedRelated)
    refine ⟨toPath (j::p), (List.mem_erase_of_ne different).mpr ?_,
      q, qMember, j::p, targetMember, rfl, rfl, related⟩
    exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨j::p, targetMember, rfl⟩)
  have injective : ∀ first ∈ sources, ∀ second ∈ sources,
      ∀ target ∈ targets.erase (toPath []), relation first target → relation second target → first = second := by
    intro first _ second _ target _ firstRelated secondRelated
    obtain ⟨q, _qMember, t, _tMember, sourceEq, targetEq, firstBack⟩ := firstRelated
    obtain ⟨r, _rMember, u, _uMember, nextEq, otherEq, secondBack⟩ := secondRelated
    have equal : toPath t = toPath u := targetEq.trans otherEq.symm
    have inheritedRelated : Rel (inherited.map Record.paths) t u := Quotient.exact equal
    have related := Rel.trans firstBack (Rel.trans (rel_covers covered inheritedRelated) (rel_symm secondBack))
    have domainEq : fromPath q = fromPath r := Quotient.sound
      (SourceCurrentPositiveInheritedChildSeparation.child_reflect parents coherent fixed index related)
    exact sourceEq.symm.trans (domainEq.trans nextEq)
  have counted := SymbolicDriver.relation_cardinality_le sources (targets.erase (toPath [])) (toPath [])
    distinct relation total injective
  refine ⟨Nat.le_trans counted List.length_erase_le, ?_⟩
  intro nonplain
  have rootPosition : [] ∈ positivePaths owner := positivePaths_spec.mpr
    (.root rowIndex row selected nonplain)
  have root : toPath [] ∈ targets := List.mem_eraseDups.mpr (List.mem_map.mpr ⟨[], rootPosition, rfl⟩)
  have shorter := List.length_erase_of_mem root
  have nonempty := List.length_pos_of_mem root
  omega

private theorem candidates_length_le (fuel : Nat) (value : Node) :
    (candidates fuel value).length ≤ InternedValueMass.value value := by
  induction fuel generalizing value with
  | zero => simp only [candidates, List.length_nil, Nat.zero_le]
  | succ fuel ih =>
      have membersBound (members : List Node) :
          (members.flatMap (candidates fuel)).length ≤ InternedValueMass.values members := by
        induction members with
        | nil => simp only [List.flatMap_nil, List.length_nil, InternedValueMass.values, Nat.le_refl]
        | cons first rest restIH =>
          have one := ih first
          simp only [List.flatMap_cons, List.length_append, InternedValueMass.values]
          omega
      have childrenBound (children : List Node) (start : Nat) :
          ((children.zipIdx start).flatMap (fun child =>
            (candidates fuel child.1).map (child.2 :: ·))).length ≤ InternedValueMass.values children := by
        induction children generalizing start with
        | nil => simp only [List.zipIdx_nil, List.flatMap_nil, List.length_nil, InternedValueMass.values, Nat.le_refl]
        | cons first rest restIH =>
          have one := ih first
          have later := restIH (start + 1)
          simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.length_map, InternedValueMass.values]
          omega
      have rowsBound (rows : List Row) :
          (rows.flatMap (fun row => row.children.zipIdx.flatMap
            (fun child => (candidates fuel child.1).map (child.2 :: ·)))).length ≤ InternedValueMass.edges rows := by
        induction rows with
        | nil => simp only [List.flatMap_nil, List.length_nil, InternedValueMass.edges, Nat.le_refl]
        | cons first rest restIH =>
          have one := childrenBound first.children 0
          have mass := InternedValueMass.edge_children first
          simp only [List.flatMap_cons, List.length_append, InternedValueMass.edges]
          omega
      cases value with
      | empty => simp only [candidates, InternedValueMass.value, List.length_cons, List.length_nil, Nat.le_refl]
      | reference name => simp only [candidates, InternedValueMass.value, List.length_cons, List.length_nil, Nat.le_refl]
      | node entry rows depth free =>
          have bounded := rowsBound rows
          simp only [candidates, InternedValueMass.value, List.length_cons]
          omega
      | union entry members depth free =>
          have bounded := membersBound members
          simp only [candidates, InternedValueMass.value, List.length_cons]
          omega
      | mu entry body depth ordinary =>
          simp only [candidates, InternedValueMass.value, List.length_cons, List.length_nil]
          omega

theorem count_le_mass (inherited : List Record) (value : Node) :
    count inherited value ≤ InternedValueMass.value value := by
  classical
  have dedup {Item : Type} [DecidableEq Item] (values : List Item) : values.eraseDups.length ≤ values.length :=
    List.Nodup.length_le_of_subset (SymbolicDriver.eraseDups_nodup values)
      (by intro item member; exact List.mem_eraseDups.mp member)
  unfold count
  have first := dedup ((positivePaths value).map
    (Quotient.mk (relationSetoid (inherited.map Record.paths))))
  simp only [List.length_map] at first
  apply Nat.le_trans first
  unfold positivePaths
  exact Nat.le_trans (dedup _) (Nat.le_trans (List.length_filter_le _ _) (candidates_length_le _ _))

end MicroCFTA.SourceCurrentPositiveQuotientCount
