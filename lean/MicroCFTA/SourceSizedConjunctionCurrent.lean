import MicroCFTA.SourceSizedConjunctionPreparation
import MicroCFTA.SourceConstraintEntryRaw

/-!
# Current raw constraint language after conjunction preparation

The actual equality accessor can discard trivial stored classes. Its
positive guard classes remain active. Normalization preserves their PCS
meaning, so an accepted accessor result retains the complete positive guard.
Successful classification and preparation therefore preserve the current
source entry without an ActiveOption premise on public raw input fields.

These laws cover returned graph languages. They do not prove grouped output
order, native container representation, or total native execution cost.
-/
namespace MicroCFTA.SourceSizedConjunctionCurrent
open Language SourceGuards SourceObservations SourceSymbolicIndex SymbolicDriver
open SourceCompactGuards SourceSizedDecided SourceSizedFiniteKeys SourceSizedConjunctionWorklist

variable {State Symbol Formula : Type}

/-- Actual normalization preserves arbitrary PCS input, including trivial classes. -/
theorem normalize_pcs (classes : EqualityNormalize.Constraints) (term : Term Symbol) :
    ConstraintIndicators.equalityValue (classTest term) (SourceCompactGuards.normalize classes) = true ↔
      EqualityNormalize.Satisfies term classes := by
  unfold SourceCompactGuards.normalize
  rw [arrayNormalize_eq]
  exact (SymbolicEqualityBridge.result_value_exact term _
    (fun output success => (EqualityNormalize.mkEqConstraints_invariants _ classes output success).1)).trans
      (EqualityNormalize.mkEqConstraints_correct term _ classes
        (EqualityTermination.mkEqConstraints_terminates classes))

/-- Combining a raw stored field with an active guard cannot lose the guard meaning. -/
theorem combine_retains_right (stored added : Option EqualityNormalize.Constraints)
    (active : ActiveOption added) (term : Term Symbol)
    (accepted : ConstraintIndicators.equalityValue (classTest term) (combineEqualities stored added) = true) :
    ConstraintIndicators.equalityValue (classTest term) added = true := by
  cases added with
  | none =>
      cases stored <;> simp [combineEqualities, ConstraintIndicators.equalityValue] at accepted
  | some classes =>
      cases classes with
      | nil => rfl
      | cons first rest =>
          cases stored with
          | none => simp [combineEqualities, ConstraintIndicators.equalityValue] at accepted
          | some original =>
              have combined : ConstraintIndicators.equalityValue (classTest term)
                  (SourceCompactGuards.normalize (original ++ first :: rest)) = true := by
                cases original <;> simpa only [combineEqualities] using accepted
              have satisfied := (normalize_pcs (original ++ first :: rest) term).mp combined
              apply (SymbolicEqualityBridge.active_classes_exact term (first :: rest)
                (active (first :: rest) rfl)).mpr
              intro paths member
              exact satisfied paths (List.mem_append_right original member)

/-- Actual accessor acceptance retains the complete syntactically positive guard. -/
theorem positive_guard [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (positiveGuard : (positive constraint.guard).isSome = true)
    (term : Term (Label Formula))
    (accepted : ConstraintIndicators.equalityValue (classTest term) (sourceEqualities constraint) = true) :
    SourceBooleanEntry.evaluateGuard formulas solver constraint.guard term = .yes := by
  obtain ⟨raw, extracted⟩ := Option.isSome_iff_exists.mp positiveGuard
  obtain ⟨added, actual, active, readback⟩ :=
    positiveNormalized_exact (Symbol := Label Formula) constraint.guard raw extracted
  have guardAccepted : ConstraintIndicators.equalityValue (classTest term) added = true := by
    cases added with
    | none =>
        apply combine_retains_right constraint.equalities none active term
        simpa only [sourceEqualities, actual] using accepted
    | some classes =>
        cases classes with
        | nil => rfl
        | cons first rest =>
            apply combine_retains_right constraint.equalities (some (first :: rest)) active term
            simpa only [sourceEqualities, actual] using accepted
  apply (positive_exact formulas solver constraint.guard raw extracted term).mpr
  rw [← readback term]
  exact guardAccepted

/-- For positive guards the complete entry equals its accessor, as a proved result. -/
theorem positive_entry [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (positiveGuard : (positive constraint.guard).isSome = true)
    (term : Term (Label Formula)) :
    SourceConstraintEntryRaw.acceptsConstraint formulas solver constraint term =
      ConstraintIndicators.equalityValue (classTest term) (sourceEqualities constraint) := by
  apply Bool.eq_iff_iff.mpr
  simp only [SourceConstraintEntryRaw.acceptsConstraint, Bool.and_eq_true_iff, decide_eq_true_eq]
  exact ⟨And.left, fun accepted => ⟨accepted,
    positive_guard formulas solver constraint positiveGuard term accepted⟩⟩

/-- Successful current row grouping preserves the complete raw source entry. -/
theorem equalChildren_guard [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (row : Row State (Label Formula) (Constraint Formula)) (classes : List (List Nat))
    (success : SourceSizedEqualChildren.equalChildren row = some classes)
    (values : List (Term (Label Formula))) (arity : values.length = row.children.length) :
    SourceConstraintEntryRaw.acceptsConstraint formulas solver row.constraint (.node row.label values) = true ↔
      CompactGroups.GroupsEqual
        (CompactEdgeRanks.childValue (.node row.label []) values) classes := by
  obtain ⟨positiveGuard, paths, parsed, read, checked, rfl⟩ :=
    (SourceSizedEqualChildren.equalChildren_exact row classes).mp success
  have valid := ((parse_exact row.children.length paths parsed).mp checked).2
  rw [positive_entry formulas solver row.constraint positiveGuard (.node row.label values), read]
  change paths.all (classTest (.node row.label values)) = true ↔
    CompactGroups.GroupsEqual (CompactEdgeRanks.childValue (.node row.label []) values)
      (SourceSizedEqualChildren.classesOf (CompactGroups.childGroups row.children.length parsed))
  rw [SourceSizedEqualChildren.classesOf_exact, CompactGroups.childGroups_exact _ _ _ valid]
  exact parsed_guard row.label values paths parsed (by rw [arity]; exact checked)

/-- Actual row relabeling preserves arbitrary child domains and current source acceptance. -/
theorem classify_semantics [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (row : Row State (Label Formula) (Constraint Formula))
    (output : Row State (Label Formula) (List (List Nat)))
    (success : SourceSizedEqualChildren.classify row = some output)
    (domain : State → Term (Label Formula) → Prop) (values : List (Term (Label Formula))) :
    (All₂ domain row.children values ∧
      SourceConstraintEntryRaw.acceptsConstraint formulas solver row.constraint (.node row.label values) = true) ↔
    (All₂ domain output.children values ∧
      CompactGroups.GroupsEqual
        (CompactEdgeRanks.childValue (.node output.label []) values) output.constraint) := by
  have frame := SourceSizedEqualChildren.classify_shape row output success
  constructor
  · rintro ⟨children, accepted⟩
    refine ⟨by simpa only [frame.2.1] using children, ?_⟩
    simpa only [frame.1] using
      (equalChildren_guard formulas solver row output.constraint frame.2.2 values
        children.length_eq.symm).mp accepted
  · rintro ⟨children, accepted⟩
    have original : All₂ domain row.children values := by simpa only [frame.2.1] using children
    refine ⟨original, (equalChildren_guard formulas solver row output.constraint frame.2.2 values
      original.length_eq.symm).mpr ?_⟩
    simpa only [frame.1] using accepted

section Language
variable [DecidableEq State] [DecidableEq Formula]

/-- Interpret the original table with its actual accessor and complete public guard. -/
noncomputable def originalGraph (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula)) : Automaton State (Label Formula) :=
  automaton (lookup original) (SourceConstraintEntryRaw.acceptsConstraint formulas solver)

/-- Complete table classification preserves one row-selection step at arbitrary child languages. -/
theorem classify_rows (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (owner : State) (domain : State → Term (Label Formula) → Prop)
    (symbol : Label Formula) (values : List (Term (Label Formula))) :
    (∃ row ∈ lookup original owner, row.label = symbol ∧
      All₂ domain row.children values ∧
        SourceConstraintEntryRaw.acceptsConstraint formulas solver row.constraint (.node symbol values) = true) ↔
    (∃ row ∈ lookup classified owner, row.label = symbol ∧
      All₂ domain row.children values ∧
        SourceSizedConjunctionSemantics.holds row.constraint (.node symbol values) = true) := by
  constructor
  · rintro ⟨row, rowIn, label, children, accepted⟩
    subst symbol
    obtain ⟨output, outputIn, checked⟩ := SourceSizedConjunctionClassified.lookup_source
      original classified classification owner row rowIn
    have shape := SourceSizedEqualChildren.classify_shape row output checked
    have preserved := (classify_semantics formulas solver row output checked domain values).mp ⟨children, accepted⟩
    have valid : CompactGroups.ValidClasses values.length output.constraint := by
      rw [← preserved.1.length_eq]
      exact SourceSizedConjunctionClassified.lookup_bounded original classified classification owner output outputIn
    refine ⟨output, outputIn, shape.1, preserved.1, ?_⟩
    rw [← shape.1]
    exact (SourceSizedConjunctionSemantics.holds_node output.label values output.constraint valid).mpr preserved.2
  · rintro ⟨output, outputIn, label, children, accepted⟩
    subst symbol
    obtain ⟨row, rowIn, checked, label, _⟩ := SourceSizedConjunctionClassified.lookup_origin
      original classified classification owner output outputIn
    have valid : CompactGroups.ValidClasses values.length output.constraint := by
      rw [← children.length_eq]
      exact SourceSizedConjunctionClassified.lookup_bounded original classified classification owner output outputIn
    have equal := (SourceSizedConjunctionSemantics.holds_node output.label values output.constraint valid).mp accepted
    have preserved := (classify_semantics formulas solver row output checked domain values).mpr ⟨children, equal⟩
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

/-- Actual whole-table classification preserves language on arbitrary, including cyclic, state spaces. -/
theorem classify_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (owner : State) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup classified)) owner term ↔
      Accepts (originalGraph formulas solver original) owner term := by
  unfold originalGraph
  apply GraphRewrite.rows_preserve_language
  intro selected tree
  cases tree with
  | node symbol values =>
      rw [row_node]
      change (∃ edge ∈ (lookup classified selected).map (Row.edge SourceSizedConjunctionSemantics.holds),
          edge.label = symbol ∧ All₂ (Accepts (originalGraph formulas solver original)) edge.children values ∧
          edge.guard (.node symbol values) = true) ↔ _
      constructor
      · rintro ⟨edge, member, label, children, guard⟩
        obtain ⟨row, rowIn, rfl⟩ := List.mem_map.mp member
        exact (classify_rows formulas solver original classified classification selected
          (Accepts (originalGraph formulas solver original)) symbol values).mpr
            ⟨row, rowIn, label, children, guard⟩
      · intro accepted
        obtain ⟨row, rowIn, label, children, guard⟩ :=
          (classify_rows formulas solver original classified classification selected
            (Accepts (originalGraph formulas solver original)) symbol values).mp accepted
        exact ⟨row.edge SourceSizedConjunctionSemantics.holds,
          List.mem_map.mpr ⟨row, rowIn, rfl⟩, label, children, guard⟩

variable [Ord State]

/-- Actual exploration at a singleton root preserves the current raw input language. -/
theorem prepare_root_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (classified : Classified State (Label Formula))
    (classification : SourceSizedConjunctionClassified.classifyTable original = some classified)
    (root : State) (returned : Stored State (Label Formula))
    (success : prepare classified root = .ready returned) (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup returned)) [root] term ↔
      Accepts (originalGraph formulas solver original) root term :=
  (SourceSizedConjunctionLanguage.classify_prepare_root_language
    original classified classification root returned success term).trans
      (classify_language formulas solver original classified classification root term)

variable [Ord (List State)] [Ord (Label Formula)]

/-- The complete literal pipeline preserves actual current acceptance without normalized-input assumptions. -/
theorem root_language (formulas : Formulas Formula) (solver : Entailment Formula)
    (original : Table State (Label Formula) (Constraint Formula))
    (root : State) (output : Stored State (Label Formula))
    (success : SourceSizedConjunctionPreparation.prepare original root = some output)
    (term : Term (Label Formula)) :
    Accepts (SourceSizedConjunctionLanguage.graph (lookup output)) [root] term ↔
      Accepts (originalGraph formulas solver original) root term := by
  obtain ⟨classified, classification, returned, ready, same⟩ :=
    SourceSizedConjunctionPreparation.success_origin original root output success
  rw [same]
  exact (SourceSizedConjunctionSortedLanguage.sorted_table_language classified root returned ready [root] term).trans
    (prepare_root_language formulas solver original classified classification root returned ready term)

end Language
end MicroCFTA.SourceSizedConjunctionCurrent
