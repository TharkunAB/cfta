import MicroCFTA.SourceSizedConjunctionLanguage
import MicroCFTA.SourceEqualityMkEdgeArity
import MicroCFTA.GraphRewrite

/-!
# Original guarded language after conjunction preparation

Actual classification preserves the complete original constraint meaning.
The internal ActiveOption premise records normalized stored equality classes.
Ready physical equality values derive this premise for their readback fields.
Attaching every input table row to those values remains a construction
obligation. The language laws allow arbitrary, including infinite, State.
They do not assert enumeration order or native container correspondence.
-/
namespace MicroCFTA.SourceSizedConjunctionGuarded
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceSizedDecided
open SourceSizedFiniteKeys SourceSizedConjunctionWorklist

variable {State Formula : Type} [DecidableEq State]

/-- Interpret every original row with its complete stored constraint. -/
noncomputable def originalGraph [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula)) : Automaton State (Label Formula) :=
  automaton (lookup original) (acceptsConstraint formulas solver)

/-- Completed cached equality payloads imply the internal classification invariant. -/
theorem active_of_cached (original : Table State (Label Formula) (Constraint Formula))
    (cached : ∀ owner row, row ∈ lookup original owner →
      SourceEqualityGuardReadback.Cached row.constraint.equalities) :
    ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities :=
  fun owner row member => SourceEqualityGuardReadback.active (cached owner row member)

/-- An actual ready stored-field inventory derives ActiveOption at every original row. -/
theorem active_of_ready (original : Table State (Label Formula) (Constraint Formula))
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (inventory : ∀ owner row, row ∈ lookup original owner →
      ∃ (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula),
        SourceEqualityConstraintAllocation.Ready cache stored ∧
          row.constraint = SourceEqualityAccessorAllocation.constraint stored guard) :
    ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities := by
  intro owner row member
  obtain ⟨stored, guard, ready, same⟩ := inventory owner row member
  rw [same]
  exact SourceEqualityMkEdgeArity.ready_active stored guard ready

section Language
variable [DecidableEq Formula]

/-- Successful classification preserves one row-selection step under any child language. -/
theorem classify_rows (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (owner : State) (domain : State → Term (Label Formula) → Prop)
    (symbol : Label Formula) (values : List (Term (Label Formula))) :
    (∃ row ∈ lookup original owner, row.label = symbol ∧
      All₂ domain row.children values ∧
        acceptsConstraint formulas solver row.constraint (.node symbol values) = true) ↔
    (∃ row ∈ lookup classified owner, row.label = symbol ∧
      All₂ domain row.children values ∧
        SourceSizedConjunctionSemantics.holds row.constraint (.node symbol values) = true) := by
  constructor
  · rintro ⟨row, rowIn, label, children, accepted⟩
    subst symbol
    obtain ⟨output, outputIn, checked⟩ := SourceSizedConjunctionClassified.lookup_source
      original classified classification owner row rowIn
    have shape := SourceSizedEqualChildren.classify_shape row output checked
    have preserved := (SourceSizedEqualChildren.classify_semantics formulas solver row output checked
      (active owner row rowIn) domain values).mp ⟨children, accepted⟩
    have valid : CompactGroups.ValidClasses values.length output.constraint := by
      rw [← preserved.1.length_eq]
      exact SourceSizedConjunctionClassified.lookup_bounded original classified classification
        owner output outputIn
    refine ⟨output, outputIn, shape.1, preserved.1, ?_⟩
    rw [← shape.1]
    exact (SourceSizedConjunctionSemantics.holds_node output.label values output.constraint valid).mpr
      preserved.2
  · rintro ⟨output, outputIn, label, children, accepted⟩
    subst symbol
    obtain ⟨row, rowIn, checked, label, _⟩ := SourceSizedConjunctionClassified.lookup_origin
      original classified classification owner output outputIn
    have valid : CompactGroups.ValidClasses values.length output.constraint := by
      rw [← children.length_eq]
      exact SourceSizedConjunctionClassified.lookup_bounded original classified classification
        owner output outputIn
    have equal := (SourceSizedConjunctionSemantics.holds_node output.label values output.constraint valid).mp
      accepted
    have preserved := (SourceSizedEqualChildren.classify_semantics formulas solver row output checked
      (active owner row rowIn) domain values).mpr ⟨children, equal⟩
    refine ⟨row, rowIn, label.symm, preserved.1, ?_⟩
    simpa only [label] using preserved.2

omit [DecidableEq State] [DecidableEq Formula] in
private theorem row_node {Payload : Type}
    (rows : State → List (Row State (Label Formula) Payload))
    (holds : Payload → Term (Label Formula) → Bool) (owner : State)
    (symbol : Label Formula) (values : List (Term (Label Formula))) :
    Accepts (automaton rows holds) owner (.node symbol values) ↔
      ∃ row ∈ rows owner, row.label = symbol ∧
        All₂ (Accepts (automaton rows holds)) row.children values ∧
          holds row.constraint (.node symbol values) = true := by
  rw [accepts_node_iff]
  constructor
  · rintro ⟨edge, member, label, children, guard⟩
    obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
    exact ⟨row, rowIn, label, children, guard⟩
  · rintro ⟨row, rowIn, label, children, guard⟩
    exact ⟨row.edge holds, List.mem_map.mpr ⟨row, rowIn, rfl⟩, label, children, guard⟩

/-- Actual classification preserves original guarded acceptance, even on cyclic graphs. -/
theorem classify_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (owner : State) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup classified)) owner term ↔
      Accepts (originalGraph formulas solver original) owner term := by
  unfold originalGraph
  apply GraphRewrite.rows_preserve_language
  intro selected tree
  cases tree with
  | node symbol values =>
      rw [row_node]
      change (∃ edge ∈ (lookup classified selected).map
          (Row.edge SourceSizedConjunctionSemantics.holds), edge.label = symbol ∧
          All₂ (Accepts (originalGraph formulas solver original)) edge.children values ∧
          edge.guard (.node symbol values) = true) ↔ _
      constructor
      · rintro ⟨edge, member, label, children, guard⟩
        obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
        exact (classify_rows formulas solver original classified classification active selected
          (Accepts (originalGraph formulas solver original)) symbol values).mpr
            ⟨row, rowIn, label, children, guard⟩
      · intro accepted
        obtain ⟨row, rowIn, label, children, guard⟩ :=
          (classify_rows formulas solver original classified classification active selected
            (Accepts (originalGraph formulas solver original)) symbol values).mp accepted
        exact ⟨row.edge SourceSizedConjunctionSemantics.holds,
          List.mem_map.mpr ⟨row, rowIn, rfl⟩, label, children, guard⟩

variable [Ord State]

/-- Actual classification and preparation denote the original conjunction at every stored key. -/
theorem prepare_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (root : State) (returned : Stored State (Label Formula))
    (success : prepare classified root = .ready returned)
    (key : List State) (present : key ∈ returned.map Prod.fst) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup returned)) key term ↔
      ∀ owner ∈ key, Accepts (originalGraph formulas solver original) owner term := by
  rw [SourceSizedConjunctionLanguage.classify_prepare_language
    original classified classification root returned success key present term]
  constructor
  · intro every owner member
    exact (classify_language formulas solver original classified classification active owner term).mp
      (every owner member)
  · intro every owner member
    exact (classify_language formulas solver original classified classification active owner term).mpr
      (every owner member)

/-- The actual singleton-root preparation preserves the complete original guarded language. -/
theorem prepare_root_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (active : ∀ owner row, row ∈ lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities)
    (root : State) (returned : Stored State (Label Formula))
    (success : prepare classified root = .ready returned) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup returned)) [root] term ↔
      Accepts (originalGraph formulas solver original) root term :=
  (SourceSizedConjunctionLanguage.classify_prepare_root_language
    original classified classification root returned success term).trans
      (classify_language formulas solver original classified classification active root term)

/-- Ready physical input fields discharge ActiveOption in the actual root-language composition. -/
theorem prepare_root_language_of_ready (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (inventory : ∀ owner row, row ∈ lookup original owner →
      ∃ (stored : SourceEqualityConstraintAllocation.Value) (guard : Guard Formula),
        SourceEqualityConstraintAllocation.Ready cache stored ∧
          row.constraint = SourceEqualityAccessorAllocation.constraint stored guard)
    (root : State) (returned : Stored State (Label Formula))
    (success : prepare classified root = .ready returned) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup returned)) [root] term ↔
      Accepts (originalGraph formulas solver original) root term :=
  prepare_root_language formulas solver original classified classification
    (active_of_ready original cache inventory) root returned success term

end Language
end MicroCFTA.SourceSizedConjunctionGuarded
