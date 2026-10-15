import MicroCFTA.SourceEqualityPCSGuard
import MicroCFTA.ConservativeEmptinessRows
import MicroCFTA.MergedAlternativesGroups

/-!
# Current conjunction rows for conservative emptiness

The worker retains the literal source edge-tuple fold. A tuple has the tail
nodes first and the original head last. Requirements contain child columns
and one projected conjunction for each combined equality class. Local node
exposure and path readback remain explicit resident-operation contracts.
-/
namespace MicroCFTA.SourceCurrentConjunctionEmptinessRows
open Language EqualityNormalize EqualityReduction
variable {Node Symbol : Type}

/-- A completed edge retains its symbol, child forest, and accessor classes. -/
structure Edge (Node Symbol : Type) where
  symbol : Symbol
  children : List Node
  classes : Option Constraints

/-- One accepted edge includes its actual equality accessor meaning. -/
def EdgeAccepts (meaning : Node → Term Symbol → Prop) (edge : Edge Node Symbol) (term : Term Symbol) : Prop :=
  ∃ terms, term = .node edge.symbol terms ∧ All₂ meaning edge.children terms ∧
    SourceEqualityGuardReadback.Sat term edge.classes

/-- A conjunction has at least one operand and accepts a common finite term. -/
def Accepts (meaning : Node → Term Symbol → Prop) (nodes : List Node) (term : Term Symbol) : Prop :=
  nodes ≠ [] ∧ ∀ node ∈ nodes, meaning node term

/-- Prepend matching edges in the exact nested source list order. -/
def extend [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (node : Node) (tuples : List (List (Edge Node Symbol))) : List (List (Edge Node Symbol)) :=
  tuples.flatMap fun tuple => match tuple with
    | [] => []
    | first :: _ => ((edges node).filter fun edge =>
        decide (edge.symbol = first.symbol ∧ edge.children.length = first.children.length)).map (· :: tuple)

/-- The initial head edge is the last component of each completed tuple. -/
def edgeTuples [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol)) :
    List Node → List (List (Edge Node Symbol))
  | [] => []
  | node :: rest => rest.foldr (extend edges) ((edges node).map (fun edge => [edge]))

/-- Every tuple in the source fold has at least one edge. -/
theorem edgeTuples_nonempty [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (nodes : List Node) : ∀ tuple ∈ edgeTuples edges nodes, tuple ≠ [] := by
  cases nodes with
  | nil => simp [edgeTuples]
  | cons node rest =>
      change ∀ tuple ∈ rest.foldr (extend edges) ((edges node).map (fun edge => [edge])), tuple ≠ []
      induction rest with
      | nil => simp
      | cons first rest ih =>
          intro tuple member
          obtain ⟨old, oldIn, present⟩ := List.mem_flatMap.mp member
          cases old with
          | nil => simp at present
          | cons edge tail =>
              obtain ⟨added, _, rfl⟩ := List.mem_map.mp present
              simp

private theorem fold_selection [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (nodes original : List Node) (tuples : List (List (Edge Node Symbol)))
    (seed : ∀ tuple ∈ tuples, All₂ (fun edge node => edge ∈ edges node) tuple original) :
    ∀ tuple ∈ nodes.foldr (extend edges) tuples,
      All₂ (fun edge node => edge ∈ edges node) tuple (nodes ++ original) := by
  induction nodes with
  | nil => exact seed
  | cons node rest ih =>
      intro tuple member
      obtain ⟨old, oldIn, selected⟩ := List.mem_flatMap.mp member
      cases old with
      | nil => simp at selected
      | cons first tail =>
          obtain ⟨added, addedIn, rfl⟩ := List.mem_map.mp selected
          exact .cons (List.mem_filter.mp addedIn).1 (ih _ oldIn)

/-- Tuple fields follow the source rotation: tail operands, then the original head. -/
theorem edgeTuples_selection [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (first : Node) (rest : List Node) (tuple : List (Edge Node Symbol))
    (member : tuple ∈ edgeTuples edges (first :: rest)) :
    All₂ (fun edge node => edge ∈ edges node) tuple (rest ++ [first]) := by
  apply fold_selection edges rest [first] ((edges first).map (fun edge => [edge])) ?_ tuple member
  intro tuple included
  obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp included
  exact .cons edgeIn .nil

private theorem fold_coverage [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (meaning : Node → Term Symbol → Prop) (term : Term Symbol)
    (expose : ∀ node, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (nodes : List Node) (all : ∀ node ∈ nodes, meaning node term)
    (tuples : List (List (Edge Node Symbol)))
    (seed : ∃ tuple ∈ tuples, tuple ≠ [] ∧ ∀ edge ∈ tuple, EdgeAccepts meaning edge term) :
    ∃ tuple ∈ nodes.foldr (extend edges) tuples, tuple ≠ [] ∧ ∀ edge ∈ tuple, EdgeAccepts meaning edge term := by
  induction nodes with
  | nil => exact seed
  | cons node rest ih =>
      obtain ⟨tuple, member, nonempty, accepted⟩ := ih (fun node included => all node (by simp [included]))
      obtain ⟨edge, edgeIn, edgeAccepted⟩ := expose node (all node (by simp))
      cases tuple with
      | nil => exact False.elim (nonempty rfl)
      | cons first tail =>
          have witness := edgeAccepted
          obtain ⟨terms, shape, forest, _⟩ := edgeAccepted
          obtain ⟨otherTerms, otherShape, otherForest, _⟩ := accepted first (by simp)
          have shapes := Term.node.inj (shape.symm.trans otherShape)
          have arities := forest.length_eq.trans (shapes.2 ▸ otherForest.length_eq.symm)
          refine ⟨edge :: first :: tail, List.mem_flatMap.mpr ⟨first :: tail, member, ?_⟩, by simp, ?_⟩
          · exact List.mem_map.mpr ⟨edge, List.mem_filter.mpr ⟨edgeIn, by simpa only [decide_eq_true_eq] using And.intro shapes.1 arities⟩, rfl⟩
          · intro chosen included
            rcases List.mem_cons.mp included with rfl | included
            · exact witness
            · exact accepted chosen included

/-- Individual accepted-node exposure derives one accepted tuple; tuple coverage is not a premise. -/
theorem edgeTuples_coverage [DecidableEq Symbol] (edges : Node → List (Edge Node Symbol))
    (meaning : Node → Term Symbol → Prop)
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (nodes : List Node) (term : Term Symbol) (accepted : Accepts meaning nodes term) :
    ∃ tuple ∈ edgeTuples edges nodes, tuple ≠ [] ∧ ∀ edge ∈ tuple, EdgeAccepts meaning edge term := by
  cases nodes with
  | nil => exact False.elim (accepted.1 rfl)
  | cons first rest =>
      obtain ⟨edge, member, witness⟩ := expose first term (accepted.2 first (by simp))
      exact fold_coverage edges meaning term (fun node => expose node term) rest
        (fun node included => accepted.2 node (by simp [included])) _
        ⟨[edge], List.mem_map.mpr ⟨edge, member, rfl⟩, by simp, by simpa⟩

/-- Combine every accessor in the literal source right-fold order. -/
noncomputable def combined (tuple : List (Edge Node Symbol)) : Option Constraints :=
  tuple.foldr (fun edge rest => SourceCompactGuards.combineEqualities edge.classes rest) (some [])

/-- The completed normalized combination retains every edge equality. -/
theorem combined_sat (tuple : List (Edge Node Symbol)) (term : Term Symbol) :
    SourceEqualityGuardReadback.Sat term (combined tuple) ↔
      ∀ edge ∈ tuple, SourceEqualityGuardReadback.Sat term edge.classes := by
  induction tuple with
  | nil => simp [combined, SourceEqualityGuardReadback.Sat, Satisfies]
  | cons edge rest ih =>
      change SourceEqualityGuardReadback.Sat term (SourceCompactGuards.combineEqualities edge.classes (combined rest)) ↔ _
      rw [SourceEqualityPCSGuard.combine_sat, ih]
      simp

/-- Each live combined result has only nontrivial classes. -/
theorem combined_active (tuple : List (Edge Node Symbol)) : SourceCompactGuards.ActiveOption (combined tuple) := by
  cases tuple with
  | nil => intro classes same; cases same; intro paths member; cases member
  | cons edge rest => exact SourceCompactGuards.combine_active edge.classes (combined rest)

/-- Completed resident conjunctions use identity order, with one copy of each node. -/
def conjunction [DecidableEq Node] (empty : Node) (key : Node → Int) (nodes : List Node) : List Node :=
  if empty ∈ nodes then [empty] else nodes.eraseDups.mergeSort (fun first second => decide (key first ≤ key second))

/-- Canonicalization preserves exactly common-term acceptance, including the empty-node shortcut. -/
theorem conjunction_exact [DecidableEq Node] (empty : Node) (key : Node → Int)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (nodes : List Node) (term : Term Symbol) :
    Accepts meaning (conjunction empty key nodes) term ↔ Accepts meaning nodes term := by
  by_cases impossible : empty ∈ nodes
  · simp only [conjunction, impossible, ite_true, Accepts]
    constructor
    · intro accepted; exact False.elim (emptyFalse term (accepted.2 empty (by simp)))
    · intro accepted; exact False.elim (emptyFalse term (accepted.2 empty impossible))
  · simp only [conjunction, impossible, ite_false, Accepts]
    have members : ∀ node, node ∈ nodes.eraseDups.mergeSort (fun first second => decide (key first ≤ key second)) ↔ node ∈ nodes :=
      fun node => List.mem_mergeSort.trans List.mem_eraseDups
    constructor
    · rintro ⟨nonempty, accepted⟩
      exact ⟨fun same => nonempty (by simp [same]), fun node member => accepted node ((members node).mpr member)⟩
    · rintro ⟨nonempty, accepted⟩
      refine ⟨?_, fun node member => accepted node ((members node).mp member)⟩
      intro same
      cases nodes with
      | nil => exact nonempty rfl
      | cons first rest => have present := (members first).mpr (by simp); simp [same] at present

/-- Each equal-arity column accepts the corresponding common child term. -/
theorem columns_accept (meaning : Node → Term Symbol → Prop) (rows : List (List Node))
    (nonempty : rows ≠ []) (terms : List (Term Symbol))
    (accepted : ∀ row ∈ rows, All₂ meaning row terms) :
    All₂ (Accepts meaning) (MergedAlternativesGroups.columns rows terms.length) terms := by
  induction terms generalizing rows with
  | nil => exact .nil
  | cons term terms ih =>
      have heads : Accepts meaning (rows.filterMap List.head?) term := by
        refine ⟨?_, ?_⟩
        · cases rows with
          | nil => exact False.elim (nonempty rfl)
          | cons row rest =>
              have related := accepted row (by simp)
              cases related with
              | cons first tail => simp
        · intro node member
          obtain ⟨row, rowIn, selected⟩ := List.mem_filterMap.mp member
          have related := accepted row rowIn
          cases related with
          | cons first tail => cases selected; exact first
      apply All₂.cons heads
      apply ih (rows.map List.tail) (by simpa using nonempty)
      intro row member
      obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
      have related := accepted original originalIn
      cases related with
      | cons first tail => exact tail

/-- Requirements use source column order, then stored class order and row-major path order. -/
def requirements [DecidableEq Node] (empty : Node) (key : Node → Int)
    (project : List Node → Path → Node) (arity : Nat) (classes : Constraints) (childLists : List (List Node)) :
    List (List Node) :=
  (MergedAlternativesGroups.columns childLists arity).map (conjunction empty key) ++
    classes.map (fun paths => conjunction empty key (childLists.flatMap fun children => paths.map (project children)))

/-- A satisfied active class has one common proper subtree in every projected operand. -/
theorem class_accepts [DecidableEq Node] (empty : Node) (key : Node → Int)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (project : List Node → Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (childLists : List (List Node)) (nonempty : childLists ≠ []) (symbol : Symbol) (terms : List (Term Symbol))
    (forests : ∀ children ∈ childLists, All₂ meaning children terms)
    (paths : Class) (active : Nontrivial paths) (satisfied : ClassSat (.node symbol terms) paths) :
    ∃ part, Accepts meaning (conjunction empty key (childLists.flatMap fun children => paths.map (project children))) part ∧
      part.height < (Term.node symbol terms).height := by
  obtain ⟨first, firstIn, second, secondIn, different⟩ := active
  have active : Nontrivial paths := ⟨first, firstIn, second, secondIn, different⟩
  obtain ⟨part, found⟩ := class_member_exists (.node symbol terms) paths active satisfied first firstIn
  have proper := class_nonroot paths active (.node symbol terms) satisfied
  refine ⟨part, (conjunction_exact empty key meaning emptyFalse _ part).mpr ⟨?_, ?_⟩, ?_⟩
  · cases childLists with
    | nil => exact False.elim (nonempty rfl)
    | cons children rest =>
        have included : project children first ∈ (children :: rest).flatMap (fun children => paths.map (project children)) :=
          List.mem_flatMap.mpr ⟨children, by simp, List.mem_map.mpr ⟨first, firstIn, rfl⟩⟩
        intro same
        simp [same] at included
  · intro node member
    obtain ⟨children, childrenIn, projected⟩ := List.mem_flatMap.mp member
    obtain ⟨path, pathIn, rfl⟩ := List.mem_map.mp projected
    obtain ⟨common, firstFound, pathFound⟩ := class_pair_equal (.node symbol terms) paths active satisfied first path firstIn pathIn
    have same := Option.some.inj (firstFound.symm.trans found)
    subst common
    exact projectLaw children symbol terms path part (proper path pathIn) (forests children childrenIn) pathFound
  · have bound := atPath_height_bound (.node symbol terms) part first found
    have positive : 0 < first.length := by
      cases first with
      | nil => exact False.elim (proper [] firstIn rfl)
      | cons index rest => simp
    omega

/-- Every literal requirement of an accepted tuple has a smaller common finite witness. -/
theorem requirements_witness [DecidableEq Node] (empty : Node) (key : Node → Int)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (project : List Node → Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (tuple : List (Edge Node Symbol)) (nonempty : tuple ≠ []) (term : Term Symbol)
    (accepted : ∀ edge ∈ tuple, EdgeAccepts meaning edge term) (classes : Constraints)
    (live : combined tuple = some classes) :
    ∀ requirement ∈ requirements empty key project ((tuple.head?).map (fun edge => edge.children.length) |>.getD 0)
      classes (tuple.map Edge.children),
      ∃ part, Accepts meaning requirement part ∧ part.height < term.height := by
  cases tuple with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      have firstAccepted := accepted first (by simp)
      obtain ⟨terms, rfl, forest, _⟩ := firstAccepted
      have forests : ∀ children ∈ (first :: rest).map Edge.children, All₂ meaning children terms := by
        intro children member
        obtain ⟨edge, edgeIn, rfl⟩ := List.mem_map.mp member
        obtain ⟨other, shape, related, _⟩ := accepted edge edgeIn
        have same := (Term.node.inj shape).2
        simpa only [← same] using related
      have satisfied : Satisfies (.node first.symbol terms) classes := by
        have sat := (combined_sat (first :: rest) (.node first.symbol terms)).mpr (fun edge member => (accepted edge member).choose_spec.2.2)
        simpa only [live, SourceEqualityGuardReadback.Sat] using sat
      have active := combined_active (first :: rest) classes live
      intro requirement included
      rcases List.mem_append.mp included with child | group
      · obtain ⟨column, columnIn, rfl⟩ := List.mem_map.mp child
        have columns := columns_accept meaning ((first :: rest).map Edge.children) (by simp) terms forests
        have columnIn : column ∈ MergedAlternativesGroups.columns ((first :: rest).map Edge.children) terms.length := by
          simpa only [List.head?_cons, Option.map_some, Option.getD_some, forest.length_eq] using columnIn
        obtain ⟨part, partIn, common⟩ := SymbolicSmartRows.all₂_child (Accepts meaning) _ terms columns column columnIn
        refine ⟨part, (conjunction_exact empty key meaning emptyFalse column part).mpr common, ?_⟩
        have bound := height_le_forestHeight terms part partIn
        simpa only [Term.height, forestHeight] using Nat.lt_succ_of_le bound
      · obtain ⟨paths, pathIn, rfl⟩ := List.mem_map.mp group
        exact class_accepts empty key meaning emptyFalse project projectLaw _ (by simp) first.symbol terms forests paths
          (active paths pathIn) (satisfied paths pathIn)

/-- Contradictory tuples are omitted before their requirements are built. -/
noncomputable def tupleRows [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → Path → Node) (nodes : List Node) : List (List (List Node)) :=
  (edgeTuples edges nodes).filterMap fun tuple => (combined tuple).map fun classes =>
    requirements empty key project ((tuple.head?).map (fun edge => edge.children.length) |>.getD 0) classes (tuple.map Edge.children)

/-- Local accepted-edge and path readback derive full tuple-row coverage and strict witness descent. -/
theorem tupleRows_witness [DecidableEq Symbol] [DecidableEq Node] (empty : Node) (key : Node → Int)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (nodes : List Node) (term : Term Symbol) (accepted : Accepts meaning nodes term) :
    ∃ row ∈ tupleRows empty key edges project nodes,
      ∀ requirement ∈ row, ∃ part, Accepts meaning requirement part ∧ part.height < term.height := by
  obtain ⟨tuple, member, nonempty, common⟩ := edgeTuples_coverage edges meaning expose nodes term accepted
  have sat := (combined_sat tuple term).mpr (fun edge member => (common edge member).choose_spec.2.2)
  cases live : combined tuple with
  | none => simp only [live, SourceEqualityGuardReadback.Sat] at sat
  | some classes =>
      refine ⟨requirements empty key project ((tuple.head?).map (fun edge => edge.children.length) |>.getD 0) classes (tuple.map Edge.children),
        List.mem_filterMap.mpr ⟨tuple, member, by rw [live]; rfl⟩, ?_⟩
      exact requirements_witness empty key meaning emptyFalse project projectLaw tuple nonempty term common classes live

end MicroCFTA.SourceCurrentConjunctionEmptinessRows
