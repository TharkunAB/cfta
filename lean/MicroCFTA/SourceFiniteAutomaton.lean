import MicroCFTA.SourceCompactGuards

/-!
# Source rows instantiate the mixed finite compiler

The source parser, compact gate, and symbolic workers supply the local
compiler laws. Class representatives below are proof witnesses only. The
operational edge plan stores the original parsed groups.
-/
namespace MicroCFTA.SourceFiniteAutomaton
open Language SourceGuards SourceObservations SourceSymbolicIndex SymbolicDriver
open SymbolicGraphView SymbolicInternedView CompactGroups CompactEdgeRanks
open FiniteAutomatonDriver

variable {Order : Type}

/-- Source row data after its symbol and canonical-child ordering. -/
structure Rows (Formula : Type) where
  graph : Graph (Label Formula)
  constraints : SymbolicDriver.Edge (Label Formula) → Constraint Formula
  equalities : SymbolicDriver.Edge (Label Formula) → Option (List (List Path))
  ordered : Nat → List (SymbolicDriver.Edge (Label Formula))
  permutation : ∀ node, (ordered node).Perm (graph.edges node)
  tied : Nat → Bool

/-- Retain the complete actual source guard on every row. -/
noncomputable def guard [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (edge : SymbolicDriver.Edge (Label Formula)) :=
  acceptsConstraint formulas solver (rows.constraints edge)

/-- The independent source row used for language acceptance. -/
noncomputable def row [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (edge : SymbolicDriver.Edge (Label Formula)) : Language.Edge Nat (Label Formula) :=
  ⟨edge.symbol, edge.children, guard formulas solver rows edge⟩

/-- The actual direct-child parser and group merge used by buildEdge. -/
def edgeSpec (rows : Rows Formula) (edge : SymbolicDriver.Edge (Label Formula)) : EdgeSpec Nat (Label Formula) :=
  ⟨edge.symbol, edge.children, (rows.equalities edge).bind fun paths =>
    (SourceCompactGuards.parse edge.children.length paths).map (childGroups edge.children.length)⟩

/-- A specification retains enough group data to recover a valid equality presentation. -/
def HasLayout (edge : EdgeSpec Node Symbol) : Prop :=
  ∃ classes, ValidClasses edge.children.length classes ∧ edge.groups = some (childGroups edge.children.length classes)

/-- Erased equality metadata is recovered only for proof, without changing any source plan. -/
noncomputable def classes (edge : EdgeSpec Node Symbol) : List (List Nat) := by
  classical
  exact if found : HasLayout edge then Classical.choose found else []

/-- Every successful source parse supplies the driver's full layout invariant. -/
theorem parsed_layout (rows : Rows Formula) (edge : SymbolicDriver.Edge (Label Formula)) :
    ParsedLayout classes (edgeSpec rows edge) := by
  classical
  intro groups found
  obtain ⟨paths, stored, parsed⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨positions, parsed, same⟩ := Option.map_eq_some_iff.mp parsed
  have valid := (SourceCompactGuards.parse_exact edge.children.length paths positions).mp parsed |>.2
  have layout : HasLayout (edgeSpec rows edge) :=
    ⟨positions, valid, by simp [edgeSpec, stored, parsed]⟩
  have chosen := Classical.choose_spec layout
  have definition : classes (edgeSpec rows edge) = Classical.choose layout := by simp [classes, layout]
  rw [definition]
  exact ⟨chosen.1, Option.some.inj (found.symm.trans chosen.2)⟩

/-- Two presentations of the same stored groups enforce the same equality conditions. -/
theorem classes_equivalent (rows : Rows Formula) (edge : SymbolicDriver.Edge (Label Formula))
    (paths : List (List Path)) (positions : List (List Nat))
    (stored : rows.equalities edge = some paths)
    (parsed : SourceCompactGuards.parse edge.children.length paths = some positions)
    (value : Nat → Value) :
    (∀ group ∈ classes (edgeSpec rows edge), EqualAt value group) ↔
      ∀ group ∈ positions, EqualAt value group := by
  have found : (edgeSpec rows edge).groups = some (childGroups edge.children.length positions) := by
    simp [edgeSpec, stored, parsed]
  obtain ⟨valid, same⟩ := parsed_layout rows edge _ found
  have original := (SourceCompactGuards.parse_exact edge.children.length paths positions).mp parsed |>.2
  rw [← childGroups_exact value _ _ valid, ← childGroups_exact value _ _ original]
  rw [same]

/-- Parsed source rows have exactly the original accepted edge language. -/
theorem edge_language [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (domain : Nat → Term (Label Formula) → Prop)
    (edge : SymbolicDriver.Edge (Label Formula))
    (normalized : SourceCompactGuards.Normalized (rows.constraints edge) (rows.equalities edge))
    (direct : SourceCompactGuards.deep (rows.equalities edge) = false) (term : Term (Label Formula)) :
    FiniteAutomatonDriver.EdgeLanguage domain classes (edgeSpec rows edge) term ↔
      AutomatonAmbiguity.EdgeLanguage domain (row formulas solver rows edge) term := by
  have exactGuard := SourceCompactGuards.normalized_exact formulas solver _ _ normalized
  cases stored : rows.equalities edge with
  | none =>
      have empty : ∀ term, (row formulas solver rows edge).guard term = false := by
        intro term
        simpa only [row, guard, stored, ConstraintIndicators.equalityValue] using exactGuard term
      simp only [FiniteAutomatonDriver.EdgeLanguage, edgeSpec, stored, Option.bind_none, Option.isSome_none,
        Bool.false_eq_true, false_and, AutomatonAmbiguity.EdgeLanguage, empty]
      simp
  | some paths =>
      cases parsed : SourceCompactGuards.parse edge.children.length paths with
      | none =>
          have rejected : ¬AutomatonAmbiguity.EdgeLanguage domain (row formulas solver rows edge) term := by
            rintro ⟨values, rfl, related, accepted⟩
            have lengths := related.length_eq
            have failed := SourceCompactGuards.parse_failure edge.symbol values paths
              (by simpa only [stored] using direct) (by simpa only [← lengths, row] using parsed)
            have equal := exactGuard (.node edge.symbol values)
            simp only [stored, ConstraintIndicators.equalityValue, failed] at equal
            rw [show (row formulas solver rows edge).guard (.node (row formulas solver rows edge).label values) = false from equal] at accepted
            cases accepted
          simp [FiniteAutomatonDriver.EdgeLanguage, edgeSpec, stored, parsed, rejected]
      | some positions =>
          have guardLaw : ∀ values : List (Term (Label Formula)), values.length = edge.children.length →
              ((row formulas solver rows edge).guard (.node edge.symbol values) = true ↔
                ∀ group ∈ classes (edgeSpec rows edge), EqualAt (childValue (.node edge.symbol []) values) group) := by
            intro values lengths
            change acceptsConstraint formulas solver (rows.constraints edge) _ = true ↔ _
            rw [exactGuard, stored]
            simp only [ConstraintIndicators.equalityValue]
            rw [SourceCompactGuards.parsed_guard edge.symbol values paths positions
              (by simpa only [lengths] using parsed)]
            exact (classes_equivalent rows edge paths positions stored parsed _).symm
          simpa only [FiniteAutomatonDriver.EdgeLanguage, edgeSpec, row, stored, Option.bind_some, parsed,
            Option.map_some, Option.isSome_some, true_and] using
            edgeTerms_source domain (row formulas solver rows edge) (classes (edgeSpec rows edge)) guardLaw term

/-- The source's distinct-symbol cardinality check in an equivalent list view. -/
noncomputable def shared [DecidableEq Formula] (edges : List (SymbolicDriver.Edge (Label Formula))) : Bool := by
  classical
  exact decide (¬(edges.map SymbolicDriver.Edge.symbol).Nodup)

/-- Duplicate removal retains a sublist of the original symbols. -/
theorem eraseDups_sublist [BEq Value] (values : List Value) : values.eraseDups.Sublist values := by
  cases values with
  | nil => exact .refl _
  | cons first rest =>
      rw [List.eraseDups_cons]
      exact ((eraseDups_sublist (rest.filter (fun value => !value == first))).trans (List.filter_sublist)).cons_cons first
termination_by values.length
decreasing_by have bound := List.length_filter_le (fun value => !value == first) rest; simp; omega

/-- The source set-size comparison is exactly the duplicate-symbol test. -/
theorem distinct_count [BEq Value] [LawfulBEq Value] (values : List Value) :
    values.eraseDups.length = values.length ↔ values.Nodup := by
  constructor
  · intro same
    have identical := (eraseDups_sublist values).eq_of_length same
    rw [← identical]
    exact SymbolicDriver.eraseDups_nodup _
  · intro unique
    apply List.Perm.length_eq
    exact (List.perm_ext_iff_of_nodup (SymbolicDriver.eraseDups_nodup values) unique).mpr (fun _ => List.mem_eraseDups)

/-- The compact flag uses the literal source comparison of distinct and total symbol counts. -/
theorem shared_count [DecidableEq Formula] (edges : List (SymbolicDriver.Edge (Label Formula))) :
    shared edges = ((edges.map SymbolicDriver.Edge.symbol).eraseDups.length != edges.length) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [shared, decide_eq_true_eq, bne_iff_ne, ne_eq]
  rw [← distinct_count]
  simp

/-- A constructor with an accepted finite term has at least one stored row. -/
theorem accepted_nonempty [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (node : Nat) (term : Term (Label Formula))
    (accepted : Accepts (automaton rows.graph (guard formulas solver rows)) node term) :
    (rows.graph.edges node).isEmpty = false := by
  cases accepted with
  | node edge terms member runs checked =>
      obtain ⟨original, present, _⟩ := List.mem_map.mp member
      cases entries : rows.graph.edges node with
      | nil => simp [entries] at present
      | cons first rest => rfl

/-- The source acyclic nonempty-intersection test, viewed through its constructor rows. -/
def overlapTest (rows : Rows Formula) (first second : Nat) : Bool :=
  !(rows.graph.edges (rows.graph.intersect first second)).isEmpty

/-- The exact fallback Boolean, including guard and path scans. -/
noncomputable def flags [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (node : Nat) : Flags where
  sharedSymbols := shared (rows.graph.edges node)
  ambiguous := AutomatonAmbiguity.ambiguous (overlapTest rows) ((rows.graph.edges node).map (row formulas solver rows))
  tied := rows.tied node
  residual := (rows.ordered node).any (fun edge => (SourceCompactGuards.positive (rows.constraints edge).guard).isNone)
  deepPath := (rows.ordered node).any (fun edge => SourceCompactGuards.deep (rows.equalities edge))

/-- A compact choice supplies each row's positive-guard and direct-path facts. -/
theorem compact_facts [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (node : Nat) (compact : useSymbolic (flags formulas solver rows node) = false)
    (edge : SymbolicDriver.Edge (Label Formula)) (member : edge ∈ rows.ordered node) :
    (SourceCompactGuards.positive (rows.constraints edge).guard).isSome = true ∧
      SourceCompactGuards.deep (rows.equalities edge) = false := by
  have parts :
      ((rows.ordered node).any (fun edge => (SourceCompactGuards.positive (rows.constraints edge).guard).isNone) = false) ∧
      ((rows.ordered node).any (fun edge => SourceCompactGuards.deep (rows.equalities edge)) = false) := by
    simp only [useSymbolic, flags, Bool.or_eq_false_iff] at compact
    exact ⟨compact.1.2, compact.2⟩
  have positive := (List.any_eq_false.mp parts.1) edge member
  have direct := (List.any_eq_false.mp parts.2) edge member
  constructor
  · cases extracted : SourceCompactGuards.positive (rows.constraints edge).guard <;> simp_all
  · simpa using direct

/-- Distinct root labels make every edge pair disjoint without an intersection query. -/
theorem distinct_symbols [DecidableEq Symbol] (domain : State → Term Symbol → Prop)
    (edges : List (Language.Edge State Symbol)) (distinct : (edges.map Language.Edge.label).Nodup) :
    edges.Pairwise (fun first second => ∀ term,
      AutomatonAmbiguity.EdgeLanguage domain first term → ¬AutomatonAmbiguity.EdgeLanguage domain second term) := by
  have pairs : edges.Pairwise (fun first second => first.label ≠ second.label) := by
    simpa only [List.Nodup, List.pairwise_map] using distinct
  apply pairs.imp
  intro first second different term a b
  obtain ⟨left, leftShape, _, _⟩ := a
  obtain ⟨right, rightShape, _, _⟩ := b
  exact different (Term.node.inj (leftShape.symm.trans rightShape)).1

/-- Passing the actual fallback gate gives disjoint complete row languages. -/
theorem compact_disjoint [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula)
    (view : ClosedOperationRows rows.graph (guard formulas solver rows))
    (node : Nat) (compact : useSymbolic (flags formulas solver rows node) = false) :
    ((rows.ordered node).map (row formulas solver rows)).Pairwise (fun first second => ∀ term,
      AutomatonAmbiguity.EdgeLanguage (Accepts (automaton rows.graph (guard formulas solver rows))) first term →
      ¬AutomatonAmbiguity.EdgeLanguage (Accepts (automaton rows.graph (guard formulas solver rows))) second term) := by
  classical
  apply ((rows.permutation node).symm.map (row formulas solver rows)).pairwise
  case hsymm =>
    intro first second separate term a b
    exact separate term b a
  by_cases shares : shared (rows.graph.edges node) = true
  · have unambiguous : AutomatonAmbiguity.ambiguous (overlapTest rows)
        ((rows.graph.edges node).map (row formulas solver rows)) = false := by
      have parts := compact
      simp only [useSymbolic, flags, shares, Bool.true_and, Bool.or_eq_false_iff] at parts
      exact parts.1.1.1
    apply AutomatonAmbiguity.compact_disjoint _ _ ?_ _ unambiguous
    intro first second term a b
    have accepted := (productRows_exact _ _ view.intersection first second term).mpr ⟨a, b⟩
    simp [overlapTest, accepted_nonempty formulas solver rows _ term accepted]
  · apply distinct_symbols
    have nodup : ((rows.graph.edges node).map SymbolicDriver.Edge.symbol).Nodup := by simpa [shared] using shares
    simpa only [List.map_map, Function.comp_def, row] using nodup

/-- The concrete finite driver retains source row order, parsed groups, and intersection requests. -/
noncomputable def source [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (symbolic : Nat → Except Unit (CompactEdgeRanks.Index (Term (Label Formula)))) :
    Source Nat (Label Formula) Unit where
  edges node := (rows.ordered node).map (edgeSpec rows)
  flags := flags formulas solver rows
  meet := rows.graph.intersect
  symbolic := symbolic

/-- The public reachable-row support precheck uses the actual source indicator compiler. -/
def indicatorsAvailable (rows : Rows Formula) (reachable : List Nat) : Bool :=
  reachable.all fun node => (rows.graph.edges node).all fun edge =>
    (SourceIndicatorCompiler.constraintIndicators (rows.constraints edge).equalities (rows.constraints edge).guard).toOption.isSome

/-- Successful source row compilation discharges the public indicator-support precheck. -/
theorem indicators_available (rows : Rows Formula) (reachable : List Nat)
    (compiled : CompiledRows rows.graph rows.constraints) : indicatorsAvailable rows reachable = true := by
  simp only [indicatorsAvailable, List.all_eq_true]
  intro node _ edge member
  rw [compiled node edge member]
  rfl

/-- An unsupported reachable guard makes the precheck fail, with its original error payload retained. -/
theorem indicators_unsupported (rows : Rows Formula) (reachable : List Nat) (node : Nat)
    (present : node ∈ reachable) (edge : SymbolicDriver.Edge (Label Formula))
    (member : edge ∈ rows.graph.edges node) (bad : Guard Formula)
    (failed : SourceIndicatorCompiler.constraintIndicators (rows.constraints edge).equalities (rows.constraints edge).guard = .error bad) :
    indicatorsAvailable rows reachable = false := by
  cases available : indicatorsAvailable rows reachable with
  | false => rfl
  | true =>
      have every := List.all_eq_true.mp available node present
      have supported := List.all_eq_true.mp every edge member
      simp [failed, Except.toOption] at supported

/-- Reordering rows preserves their independent finite accepted language. -/
theorem source_rows [DecidableEq Formula] (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : Rows Formula) (node : Nat) (term : Term (Label Formula)) :
    Accepts (automaton rows.graph (guard formulas solver rows)) node term ↔
      ∃ edge ∈ rows.ordered node, AutomatonAmbiguity.EdgeLanguage
        (Accepts (automaton rows.graph (guard formulas solver rows))) (row formulas solver rows edge) term := by
  constructor
  · intro accepted
    cases accepted with
    | node edge children member runs checked =>
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact ⟨original, (rows.permutation node).mem_iff.mpr present, children, rfl, runs, checked⟩
  · rintro ⟨edge, member, children, rfl, runs, checked⟩
    exact .node (row formulas solver rows edge) children
      (List.mem_map.mpr ⟨edge, (rows.permutation node).mem_iff.mp member, rfl⟩) runs checked

/-- All finite-driver semantic fields follow from source parser, gate, and worker proofs. -/
theorem source_semantics [DecidableEq Formula] [Ord (Label Formula)] [Ord Order]
    (formulas : Formulas Formula) (solver : Entailment Formula) (rows : Rows Formula)
    (order : Label Formula → Order)
    (workers : ∀ node, SourceFiniteBackend.Stable rows.graph order node
      (Accepts (automaton rows.graph (guard formulas solver rows)) node))
    (view : ClosedOperationRows rows.graph (guard formulas solver rows))
    (normalization : ∀ node edge, edge ∈ rows.ordered node →
      (SourceCompactGuards.positive (rows.constraints edge).guard).isSome = true →
      SourceCompactGuards.Normalized (rows.constraints edge) (rows.equalities edge)) :
    Semantics (source formulas solver rows (fun node => SourceFiniteBackend.compile (workers node)))
      (Accepts (automaton rows.graph (guard formulas solver rows))) classes := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro node empty term accepted
    obtain ⟨edge, member, _⟩ := (source_rows formulas solver rows node term).mp accepted
    have mapped : edgeSpec rows edge ∈ (rows.ordered node).map (edgeSpec rows) := List.mem_map.mpr ⟨edge, member, rfl⟩
    have noRows : (rows.ordered node).map (edgeSpec rows) = [] := List.isEmpty_iff.mp empty
    rw [noRows] at mapped
    cases mapped
  · intro node _
    exact SourceFiniteBackend.compile_exact (workers node)
  · exact productRows_exact _ _ view.intersection
  · intro node _ edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact parsed_layout rows original
  · intro node compact term
    rw [source_rows formulas solver rows node term]
    constructor
    · rintro ⟨edge, member, accepted⟩
      have facts := compact_facts formulas solver rows node compact edge member
      exact ⟨edgeSpec rows edge, List.mem_map.mpr ⟨edge, member, rfl⟩,
        (edge_language formulas solver rows _ edge (normalization node edge member facts.1) facts.2 term).mpr accepted⟩
    · rintro ⟨specification, member, accepted⟩
      obtain ⟨edge, originalMember, rfl⟩ := List.mem_map.mp member
      have facts := compact_facts formulas solver rows node compact edge originalMember
      exact ⟨edge, originalMember,
        (edge_language formulas solver rows _ edge (normalization node edge originalMember facts.1) facts.2 term).mp accepted⟩
  · intro node compact
    have separate := compact_disjoint formulas solver rows view node compact
    rw [List.pairwise_map] at separate
    change ((rows.ordered node).map (edgeSpec rows)).Pairwise _
    rw [List.pairwise_map]
    apply separate.imp_of_mem
    intro first second firstMember secondMember separate term a b
    have firstFacts := compact_facts formulas solver rows node compact first firstMember
    have secondFacts := compact_facts formulas solver rows node compact second secondMember
    exact separate term
      ((edge_language formulas solver rows _ first (normalization node first firstMember firstFacts.1) firstFacts.2 term).mp a)
      ((edge_language formulas solver rows _ second (normalization node second secondMember secondFacts.1) secondFacts.2 term).mp b)

/-- Source allocation and closed product branches bound every actual compact recursive request. -/
theorem source_decrease [DecidableEq Formula] [DecidableEq Payload]
    (formulas : Formulas Formula) (solver : Entailment Formula) (rows : Rows Formula)
    (shape : Payload → List (Language.Edge Nat (Label Formula)))
    (view : ClosedOperationRows rows.graph (guard formulas solver rows))
    (allocated : AllocatedRows shape (automaton rows.graph (guard formulas solver rows)))
    (symbolic : Nat → Except Unit (CompactEdgeRanks.Index (Term (Label Formula)))) :
    let budget := closedSourceBudget rows.graph (guard formulas solver rows) view id (allocated_rank shape _ allocated)
    ∀ node requested, requested ∈ requests (source formulas solver rows symbolic) node →
      budget.value requested < budget.value node := by
  intro budget
  apply requests_decrease
  · intro node specification present child childMember
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    exact GraphBudget.child_smaller _ (rowBudget rows.graph (guard formulas solver rows) budget)
      node (row formulas solver rows edge)
      (List.mem_map.mpr ⟨edge, (rows.permutation node).mem_iff.mp member, rfl⟩) child childMember
  · intro first second
    exact (budget.intersection first second).1

/-- Source worker termination and ordering produce the complete backend family without a semantic premise. -/
theorem source_workers [DecidableEq Formula] [Ord (Label Formula)] [Ord Order] [DecidableEq Payload]
    (formulas : Formulas Formula) (solver : Entailment Formula) (rows : Rows Formula)
    (shape : Payload → List (Language.Edge Nat (Label Formula))) (order : Label Formula → Order)
    (compiled : CompiledRows rows.graph rows.constraints)
    (view : ClosedOperationRows rows.graph (guard formulas solver rows))
    (allocated : AllocatedRows shape (automaton rows.graph (guard formulas solver rows)))
    (fallback : Term (Label Formula)) :
    Nonempty (∀ node, SourceFiniteBackend.Stable rows.graph order node
      (Accepts (automaton rows.graph (guard formulas solver rows)) node)) := by
  classical
  exact ⟨fun node => Classical.choice
    (SourceFiniteBackend.source_stable formulas solver shape rows.graph order rows.constraints compiled view allocated fallback node)⟩

/-- Cached class invariants and actual source equalities readback discharge normalization completely. -/
theorem source_normalization_readback (rows : Rows Formula)
    (cachedActive : ∀ node edge, edge ∈ rows.ordered node →
      SourceCompactGuards.ActiveOption (rows.constraints edge).equalities)
    (equalityReadback : ∀ node edge, edge ∈ rows.ordered node →
      rows.equalities edge = SourceCompactGuards.sourceEqualities (rows.constraints edge)) :
    ∀ node edge, edge ∈ rows.ordered node →
      (SourceCompactGuards.positive (rows.constraints edge).guard).isSome = true →
      SourceCompactGuards.Normalized (rows.constraints edge) (rows.equalities edge) := by
  intro node edge member positive
  rw [equalityReadback node edge member]
  exact .source (cachedActive node edge member) positive

/-- Actual source data give total mixed compilation and an exact public rank API.
The only index witnesses used here are derived from the proved source workers. -/
theorem exact_index_api [DecidableEq Formula] [Ord (Label Formula)] [Ord Order] [DecidableEq Payload]
    (formulas : Formulas Formula) (solver : Entailment Formula) (rows : Rows Formula)
    (shape : Payload → List (Language.Edge Nat (Label Formula))) (order : Label Formula → Order)
    (compiled : CompiledRows rows.graph rows.constraints)
    (view : ClosedOperationRows rows.graph (guard formulas solver rows))
    (allocated : AllocatedRows shape (automaton rows.graph (guard formulas solver rows)))
    (cachedActive : ∀ node edge, edge ∈ rows.ordered node →
      SourceCompactGuards.ActiveOption (rows.constraints edge).equalities)
    (equalityReadback : ∀ node edge, edge ∈ rows.ordered node →
      rows.equalities edge = SourceCompactGuards.sourceEqualities (rows.constraints edge))
    (fallback : Term (Label Formula)) (reachable : List Nat) :
    ∃ workers : ∀ node, SourceFiniteBackend.Stable rows.graph order node
        (Accepts (automaton rows.graph (guard formulas solver rows)) node),
      let compiler := source formulas solver rows (fun node => SourceFiniteBackend.compile (workers node))
      let budget := closedSourceBudget rows.graph (guard formulas solver rows) view id (allocated_rank shape _ allocated)
      ∀ root,
        (FiniteAutomatonDriver.compile compiler (indicatorsAvailable rows reachable) (budget.value root + 1) root = .error .emptyGenerator ↔
          ∀ term, ¬Accepts (automaton rows.graph (guard formulas solver rows)) root term) ∧
        FiniteAutomatonDriver.compile compiler (indicatorsAvailable rows reachable) (budget.value root + 1) root ≠ .error .executionBound ∧
        ∀ index, FiniteAutomatonDriver.compile compiler (indicatorsAvailable rows reachable) (budget.value root + 1) root = .ok index →
          0 < index.count ∧ Correct index ∧
          (∀ term, (∃ rank, index.select rank = some term) ↔
            Accepts (automaton rows.graph (guard formulas solver rows)) root term) ∧
          (∀ rank, (∃ term, index.select rank = some term) ↔ rank < index.count) ∧
          (∀ term, index.rank term = none ↔ ¬Accepts (automaton rows.graph (guard formulas solver rows)) root term) ∧
          (∀ first second term, index.select first = some term → index.select second = some term → first = second) := by
  obtain ⟨workers⟩ := source_workers formulas solver rows shape order compiled view allocated fallback
  refine ⟨workers, ?_⟩
  intro compiler budget root
  simp only [indicators_available rows reachable compiled]
  have semantics := source_semantics formulas solver rows order workers view
    (source_normalization_readback rows cachedActive equalityReadback)
  have decrease := source_decrease formulas solver rows shape view allocated (fun node => SourceFiniteBackend.compile (workers node))
  refine ⟨compile_empty_iff compiler budget.value decrease _ classes semantics root,
    compile_no_execution_error compiler budget.value decrease true root, ?_⟩
  intro index successful
  have exact := compile_correct compiler budget.value decrease _ classes semantics root index successful
  have api := FiniteAutomatonDriver.exact_index_api _ index exact
  exact ⟨exact.1, exact.2.1, exact.2.2, api.1, api.2.1, api.2.2⟩

end MicroCFTA.SourceFiniteAutomaton
