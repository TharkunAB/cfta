import MicroCFTA.SourceSynthesisCurrentTypeReification
import MicroCFTA.SourceSynthesisPr210Substitution

/-!
# Raw instances from current generalized annotations

Actual source acceptance supplies one admitted image per demanded variable.
The original PCS classes make repeated occurrences use the same image.
Each accepted annotation yields its own raw simultaneous substitution.
This result concerns generalized type annotations. It does not establish
whole Program soundness, query coverage, or native worker behavior.
-/
namespace MicroCFTA.SourceSynthesisCurrentGeneralizeReification
open Language
open InternedGuardedSyntax (evaluate edgeMeaning forest)
open SourceSynthesisTypeSyntax (Ty Library Query Expr allTypes arrowType arrowMarker variableSymbol)
open SourceSynthesisGeneralizeSyntax
  (Guard top generalize replace finish rootSymbol occurrences childrenOccurrences shift
    variables pathsOf equalityClasses eqGuard mem_variables mem_pathsOf)
open SourceSynthesisGeneralizeFiniteInstances (instantiate)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax mapChildren mapEdges)
open SourceSynthesisCurrentContext (context constructorCatalog context_types)
open SourceSynthesisCurrentTypeAdmission (RawAdmitted)
open SourceSynthesisPr210TypeReflection (encodeTy candidateRigid)
open SourceSynthesisPr210Substitution (encodeTy_aliasSafe substTy_encodeTy)
open SourceSynthesisTypeSubstitutionWitnesses (substTy instantiate_rigid_of_compatible)
open SourceSynthesisEncodedSubstitutionLift
  (decodeVariable variable_key_roundtrip liftSubstitution liftSubstitution_variable)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "marker" => (Term.node (literal "(->)") [])

private theorem node_inverse (holds : Guard → Term Symbol → Bool)
    (name : String) (guard : Guard) (children : List (Expr Guard)) (term : Term Symbol)
    (accepted : evaluate holds []
      (mapSyntax literal (.node [.mk name guard children])) term) :
    ∃ terms, term = .node (literal name) terms ∧
      forest holds [] (mapChildren literal children) terms ∧ holds guard term = true := by
  simp only [mapSyntax, mapEdges] at accepted
  rw [evaluate] at accepted
  obtain ⟨⟨edge, member⟩, checked⟩ := accepted
  have same := List.mem_singleton.mp member
  subst edge
  rw [edgeMeaning] at checked
  exact checked

private theorem leaf_inverse (holds : Guard → Term Symbol → Bool)
    (name : String) (term : Term Symbol)
    (accepted : evaluate holds [] (mapSyntax literal (.node [.mk name top []])) term) :
    term = .node (literal name) [] := by
  obtain ⟨terms, shape, checked, _held⟩ := node_inverse holds name top [] term accepted
  cases terms with
  | nil => exact shape
  | cons first rest => simp only [mapChildren, forest] at checked

private theorem arrow_inverse (holds : Guard → Term Symbol → Bool)
    (argument result : Expr Guard) (term : Term Symbol)
    (accepted : evaluate holds [] (mapSyntax literal (arrowType top argument result)) term) :
    ∃ first second, term = .node (literal "->") [marker, first, second] ∧
      evaluate holds [] (mapSyntax literal argument) first ∧
      evaluate holds [] (mapSyntax literal result) second := by
  obtain ⟨terms, shape, checked, _held⟩ := node_inverse holds "->" top
    [arrowMarker top, argument, result] term (by simpa only [arrowType] using accepted)
  rcases terms with _ | ⟨actualMarker, _ | ⟨first, _ | ⟨second, _ | ⟨_, _⟩⟩⟩⟩ <;>
    simp only [mapChildren, forest, and_false] at checked
  have markerShape := leaf_inverse holds "(->)" actualMarker
    (by simpa only [arrowMarker] using checked.1)
  exact ⟨first, second, by simpa only [markerShape] using shape, checked.2.1, checked.2.2.1⟩

private theorem all₂_at_left {α β : Type} (relation : α → β → Prop)
    {inputs : List α} {outputs : List β} (checked : All₂ relation inputs outputs) :
    ∀ (index : Nat) (input : α), inputs[index]? = some input →
      ∃ output, outputs[index]? = some output ∧ relation input output := by
  induction checked with
  | nil => intro index input found; simp at found
  | @cons input output _inputs _outputs own _rest ih =>
      intro index selected found
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero] at found
          cases found
          exact ⟨output, rfl, own⟩
      | succ index => exact ih index selected (by simpa only [List.getElem?_cons_succ] using found)

private theorem all₂_map_exact {α β : Type} (relation : α → β → Prop)
    {inputs : List α} {outputs : List β} (checked : All₂ relation inputs outputs)
    (image : α → β)
    (exactAt : ∀ (index : Nat) (input : α) (output : β), inputs[index]? = some input →
      outputs[index]? = some output → relation input output → output = image input) :
    outputs = inputs.map image := by
  revert exactAt
  induction checked with
  | nil => intro _exactAt; rfl
  | @cons input output _inputs _outputs own _rest ih =>
      intro exactAt
      have first := exactAt 0 input output rfl rfl own
      have later := ih (fun index selected actual selectedAt actualAt related =>
        exactAt (index + 1) selected actual
          (by simpa only [List.getElem?_cons_succ] using selectedAt)
          (by simpa only [List.getElem?_cons_succ] using actualAt) related)
      simp only [List.map_cons, first, later]

private theorem shift_member (index : Nat) (items : List (String × List Nat))
    (name : String) (path : List Nat) :
    (name, path) ∈ shift index items ↔ ∃ rest, path = index :: rest ∧ (name, rest) ∈ items := by
  simp only [shift, List.mem_map]
  constructor
  · rintro ⟨⟨symbol, rest⟩, member, same⟩
    cases same
    exact ⟨rest, rfl, member⟩
  · rintro ⟨rest, rfl, member⟩
    exact ⟨(name, rest), member, rfl⟩

private theorem children_origin (index : Nat) (types : List Ty) :
    ∀ name path, (name, path) ∈ childrenOccurrences index types →
      ∃ offset typ rest, types[offset]? = some typ ∧ path = (index + offset) :: rest ∧
        (name, rest) ∈ occurrences typ := by
  induction types generalizing index with
  | nil => intro name path member; simp only [childrenOccurrences, List.not_mem_nil] at member
  | cons first rest ih =>
      intro name path member
      rw [childrenOccurrences] at member
      rcases List.mem_append.mp member with own | later
      · obtain ⟨tail, same, found⟩ := (shift_member index _ name path).mp own
        exact ⟨0, first, tail, rfl, by simpa only [Nat.add_zero] using same, found⟩
      · obtain ⟨offset, typ, tail, atIndex, same, found⟩ := ih (index + 1) name path later
        refine ⟨offset + 1, typ, tail, ?_, ?_, found⟩
        · simpa only [List.getElem?_cons_succ] using atIndex
        · have equal : index + 1 + offset = index + (offset + 1) := by omega
          simpa only [equal] using same

private theorem children_occurrence (index : Nat) (types : List Ty) (offset : Nat)
    (typ : Ty) (found : types[offset]? = some typ) (name : String) (path : List Nat)
    (included : (name, path) ∈ occurrences typ) :
    (name, (index + offset) :: path) ∈ childrenOccurrences index types := by
  induction types generalizing index offset with
  | nil => simp at found
  | cons first rest ih =>
      cases offset with
      | zero =>
          simp only [List.getElem?_cons_zero] at found
          cases found
          rw [childrenOccurrences]
          exact List.mem_append.mpr (.inl
            ((shift_member index _ name _).mpr ⟨path, by simp, included⟩))
      | succ offset =>
          rw [childrenOccurrences]
          apply List.mem_append.mpr
          apply Or.inr
          have retained := ih (index + 1) offset
            (by simpa only [List.getElem?_cons_succ] using found)
          have equal : index + 1 + offset = index + (offset + 1) := by omega
          simpa only [equal] using retained

private def ReplacementFacts (holds : Guard → Term Symbol → Bool) (types : Expr Guard)
    (typ : Ty) (term : Term Symbol) : Prop :=
  (∀ name path, (name, path) ∈ occurrences typ →
    ∃ image, term.atPath path = some image ∧
      evaluate holds [] (mapSyntax literal types) image) ∧
  ∀ substitution : String → Term Symbol,
    (∀ name path, (name, path) ∈ occurrences typ →
      term.atPath path = some (substitution name)) → term = instantiate substitution typ

private theorem node_facts (holds : Guard → Term Symbol → Bool) (types : Expr Guard)
    (typ : Ty) (symbol : Symbol) (front : List (Term Symbol))
    (children : List Ty) (terms : List (Term Symbol))
    (paths : occurrences typ = childrenOccurrences front.length children)
    (shape : ∀ substitution, instantiate substitution typ =
      .node symbol (front ++ children.map (instantiate substitution)))
    (checked : All₂ (ReplacementFacts holds types) children terms) :
    ReplacementFacts holds types typ (.node symbol (front ++ terms)) := by
  constructor
  · intro name path included
    rw [paths] at included
    obtain ⟨index, child, tail, childAt, same, own⟩ :=
      children_origin front.length children name path included
    obtain ⟨actual, actualAt, facts⟩ := all₂_at_left _ checked index child childAt
    obtain ⟨image, selected, admitted⟩ := facts.1 name tail own
    refine ⟨image, ?_, admitted⟩
    rw [same, Term.atPath, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, actualAt, Option.bind_some]
    exact selected
  · intro substitution agree
    have mapped : terms = children.map (instantiate substitution) := by
      apply all₂_map_exact _ checked (instantiate substitution)
      intro index child actual childAt actualAt facts
      apply facts.2 substitution
      intro name path member
      have included : (name, (front.length + index) :: path) ∈ occurrences typ := by
        rw [paths]
        exact children_occurrence front.length children index child childAt name path member
      have selected := agree name _ included
      rw [Term.atPath, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, actualAt, Option.bind_some] at selected
      exact selected
    rw [shape substitution, mapped]

private theorem replace_facts (holds : Guard → Term Symbol → Bool) (types : Expr Guard)
    (typ : Ty) : ∀ term,
    evaluate holds [] (mapSyntax literal (replace types typ)) term →
      ReplacementFacts holds types typ term := by
  induction typ using Ty.rec
    (motive_2 := fun children => ∀ terms,
      forest holds [] (mapChildren literal (children.map (replace types))) terms →
        All₂ (ReplacementFacts holds types) children terms) with
  | tVar name =>
      intro term accepted
      constructor
      · intro key path member
        have same : (key, path) = (variableSymbol name, []) :=
          List.mem_singleton.mp (by simpa only [occurrences] using member)
        cases same
        exact ⟨term, rfl, by simpa only [replace] using accepted⟩
      · intro substitution agree
        simp only [instantiate]
        exact Option.some.inj (agree (variableSymbol name) [] (by simp only [occurrences, List.mem_singleton]))
  | tFun argument result first second =>
      intro term accepted
      obtain ⟨left, right, same, leftAccepted, rightAccepted⟩ := arrow_inverse holds
        (replace types argument) (replace types result) term (by simpa only [replace] using accepted)
      rw [same]
      apply node_facts holds types (.tFun argument result) (literal "->") [marker]
        [argument, result] [left, right]
      · simp only [occurrences, childrenOccurrences, List.length_cons, List.length_nil, List.append_nil]
      · intro substitution
        simp only [instantiate, List.map_cons, List.map_nil]
        rfl
      · exact .cons (first left leftAccepted) (.cons (second right rightAccepted) .nil)
  | tCons name arguments children =>
      intro term accepted
      have ordinary
          (paths : occurrences (.tCons name arguments) = childrenOccurrences 0 arguments)
          (replaced : replace types (.tCons name arguments) =
            .node [.mk name top (arguments.map (replace types))])
          (instantiated : ∀ substitution, instantiate substitution (.tCons name arguments) =
            .node (literal name) (arguments.map (instantiate substitution))) :
          ReplacementFacts holds types (.tCons name arguments) term := by
        obtain ⟨terms, same, acceptedChildren, _held⟩ := node_inverse holds name top
          (arguments.map (replace types)) term (by simpa only [replaced] using accepted)
        rw [same]
        exact node_facts holds types (.tCons name arguments) (literal name) [] arguments terms
          paths instantiated (children terms acceptedChildren)
      cases arguments with
      | nil =>
          by_cases recognized : SourceSynthesisGeneralizeSyntax.isVariableSymbol name = true
          · constructor
            · intro key path member
              have same : (key, path) = (name, []) := List.mem_singleton.mp
                (by simpa only [occurrences, recognized, ↓reduceIte] using member)
              cases same
              exact ⟨term, rfl, by simpa only [replace, recognized, ↓reduceIte] using accepted⟩
            · intro substitution agree
              simp only [instantiate, recognized, ↓reduceIte]
              exact Option.some.inj
                (agree name [] (by simp only [occurrences, recognized, ↓reduceIte, List.mem_singleton]))
          · exact ordinary (by simp only [occurrences, recognized, Bool.false_eq_true, ↓reduceIte, childrenOccurrences])
              (by simp only [replace, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil])
              (by intro substitution; simp only [instantiate, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil])
      | cons first rest =>
          cases rest with
          | nil =>
              exact ordinary (by simp only [occurrences])
                (by simp only [replace, List.map_cons, List.map_nil])
                (by intro substitution; simp only [instantiate, List.map_cons, List.map_nil])
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  exact ordinary (by simp only [occurrences])
                    (by simp only [replace, List.map_cons])
                    (by intro substitution; simp only [instantiate, List.map_cons])
              | nil =>
                  by_cases alias : name = "Fun"
                  · obtain ⟨left, right, same, leftAccepted, rightAccepted⟩ := arrow_inverse holds
                      (replace types first) (replace types second) term
                      (by simpa only [replace, alias, ↓reduceIte] using accepted)
                    rw [same]
                    apply node_facts holds types (.tCons name [first, second]) (literal "->")
                      [marker] [first, second] [left, right]
                    · simp only [occurrences, alias, ↓reduceIte, childrenOccurrences,
                        List.length_cons, List.length_nil, List.append_nil]
                    · intro substitution
                      simp only [instantiate, alias, ↓reduceIte, List.map_cons, List.map_nil]
                      rfl
                    · apply children [left, right]
                      simp only [List.map_cons, List.map_nil, mapChildren, forest]
                      exact ⟨leftAccepted, rightAccepted, True.intro⟩
                  · exact ordinary (by simp only [occurrences, alias, ↓reduceIte])
                      (by simp only [replace, alias, ↓reduceIte, List.map_cons, List.map_nil])
                      (by intro substitution; simp only [instantiate, alias, ↓reduceIte, List.map_cons, List.map_nil])
  | nil =>
      rename_i terms accepted
      cases terms with
      | nil => exact .nil
      | cons first rest => simp only [List.map_nil, mapChildren, forest] at accepted
  | cons first rest own later =>
      rename_i terms accepted
      cases terms with
      | nil => simp only [List.map_cons, mapChildren, forest] at accepted
      | cons term terms =>
          simp only [List.map_cons, mapChildren, forest] at accepted
          exact .cons (own term accepted.1) (later terms accepted.2)

private theorem one_occurrence_sat (typ : Ty) (name : String) (term : Term Symbol)
    (found : occurrences typ = [(name, [])]) :
    EqualityNormalize.Satisfies term (equalityClasses typ) := by
  have classes : equalityClasses typ = [[[]]] := by
    simp [equalityClasses, variables, pathsOf, found, List.eraseDups_cons]
  rw [classes]
  intro paths member
  have same := List.mem_singleton.mp member
  subst paths
  intro first firstIn second secondIn different
  have firstEq := List.mem_singleton.mp firstIn
  have secondEq := List.mem_singleton.mp secondIn
  exact False.elim (different (firstEq.trans secondEq.symm))

private theorem node_guard_parts [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (name : String) (classes : EqualityNormalize.Constraints) (children : List (Expr Guard))
    (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [.mk name (eqGuard classes) children])) term) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (.node [.mk name top children])) term ∧
      EqualityNormalize.Satisfies term classes := by
  obtain ⟨terms, same, checked, held⟩ := node_inverse _ name (eqGuard classes) children term accepted
  constructor
  · simp only [mapSyntax, mapEdges]
    rw [evaluate]
    refine ⟨⟨.mk (literal name) top (mapChildren literal children), List.mem_cons_self⟩, ?_⟩
    rw [edgeMeaning]
    exact ⟨terms, same, checked, SourceEqualityPCSConstructors.top_true formulas solver term⟩
  · have satisfied := ((SourceEqualityPCSGuard.holds_exact formulas solver _ term).mp held).1
    rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source] at satisfied
    exact (SourceEqualityPCSGuard.normalize_sat classes term).mp satisfied

private theorem generalize_parts [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (catalog : List (String × Nat))
    (typ : Ty) (term : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (generalize (allTypes top catalog) typ)) term) :
    evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (replace (allTypes top catalog) typ)) term ∧
      EqualityNormalize.Satisfies term (equalityClasses typ) := by
  have lift (name : String) (children : List (Expr Guard))
      (shape : replace (allTypes top catalog) typ = .node [.mk name top children])
      (root : rootSymbol typ = name) :
      evaluate (SourceEqualityPCSGuard.holds formulas solver) []
        (mapSyntax literal (replace (allTypes top catalog) typ)) term ∧
        EqualityNormalize.Satisfies term (equalityClasses typ) := by
    have generalized : generalize (allTypes top catalog) typ =
        .node [.mk name (eqGuard (equalityClasses typ)) children] := by
      rw [generalize, shape, finish, root]
    have parts := node_guard_parts formulas solver name (equalityClasses typ) children term
      (by simpa only [generalized] using accepted)
    exact ⟨by simpa only [shape] using parts.1, parts.2⟩
  cases typ with
  | tVar name =>
      refine ⟨?_, one_occurrence_sat _ (variableSymbol name) _ (by simp only [occurrences])⟩
      simpa only [generalize, replace, allTypes, finish] using accepted
  | tFun argument result =>
      exact lift "->" [arrowMarker top, replace (allTypes top catalog) argument,
        replace (allTypes top catalog) result]
        (by simp only [replace, arrowType]) (by simp only [rootSymbol])
  | tCons name arguments =>
      cases arguments with
      | nil =>
          by_cases recognized : SourceSynthesisGeneralizeSyntax.isVariableSymbol name = true
          · refine ⟨?_, one_occurrence_sat _ name _ (by simp only [occurrences, recognized, ↓reduceIte])⟩
            simpa only [generalize, replace, recognized, ↓reduceIte, allTypes, finish] using accepted
          · exact lift name [] (by simp only [replace, recognized, Bool.false_eq_true, ↓reduceIte]) rfl
      | cons first rest =>
          cases rest with
          | nil =>
              exact lift name [replace (allTypes top catalog) first]
                (by simp only [replace, List.map_cons, List.map_nil]) (by simp only [rootSymbol])
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  exact lift name
                    ((first :: second :: third :: tail).map (replace (allTypes top catalog)))
                    (by simp only [replace]) (by simp only [rootSymbol])
              | nil =>
                  by_cases alias : name = "Fun"
                  · exact lift "->" [arrowMarker top, replace (allTypes top catalog) first,
                      replace (allTypes top catalog) second]
                      (by simp only [replace, alias, ↓reduceIte, arrowType])
                      (by simp only [rootSymbol, alias, ↓reduceIte])
                  · exact lift name [replace (allTypes top catalog) first, replace (allTypes top catalog) second]
                      (by simp only [replace, alias, ↓reduceIte])
                      (by simp only [rootSymbol, alias, ↓reduceIte])

private theorem uniform_images (holds : Guard → Term Symbol → Bool) (types : Expr Guard)
    (typ : Ty) (term : Term Symbol) (facts : ReplacementFacts holds types typ term)
    (satisfied : EqualityNormalize.Satisfies term (equalityClasses typ)) :
    ∃ substitution : String → Term Symbol,
      (∀ name ∈ variables typ, evaluate holds [] (mapSyntax literal types) (substitution name)) ∧
      ∀ name path, (name, path) ∈ occurrences typ → term.atPath path = some (substitution name) := by
  classical
  have available : ∀ name, name ∈ variables typ →
      ∃ image, evaluate holds [] (mapSyntax literal types) image ∧
        ∀ path, (name, path) ∈ occurrences typ → term.atPath path = some image := by
    intro name member
    obtain ⟨chosen, included⟩ := (mem_variables name typ).mp member
    obtain ⟨image, selected, admitted⟩ := facts.1 name chosen included
    refine ⟨image, admitted, ?_⟩
    intro path present
    by_cases same : path = chosen
    · simpa only [same] using selected
    · have classMember : pathsOf name typ ∈ equalityClasses typ :=
        List.mem_map.mpr ⟨name, member, rfl⟩
      obtain ⟨common, atPath, atChosen⟩ := satisfied _ classMember path
        ((mem_pathsOf name typ path).mpr present) chosen
        ((mem_pathsOf name typ chosen).mpr included) same
      have imageSame : common = image := Option.some.inj (atChosen.symm.trans selected)
      exact atPath.trans (congrArg some imageSame)
  let substitution (name : String) : Term Symbol :=
    if present : name ∈ variables typ then Classical.choose (available name present)
    else .node (literal "unused") []
  refine ⟨substitution, ?_, ?_⟩
  · intro name present
    simpa only [substitution, dite_eq_left present] using (Classical.choose_spec (available name present)).1
  · intro name path present
    have included := (mem_variables name typ).mpr ⟨path, present⟩
    simpa only [substitution, dite_eq_left included] using
      (Classical.choose_spec (available name included)).2 path present

/-- Actual generalized acceptance yields a raw instance with only demanded admitted images. -/
theorem generalize_instance [DecidableEq FullSyntax.Formula]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (lib : Library) (query : Query) (scheme : Ty) (annotation : Term Symbol)
    (accepted : evaluate (SourceEqualityPCSGuard.holds formulas solver) []
      (mapSyntax literal (generalize (context lib query).types (encodeTy scheme)))
      annotation) :
    ∃ rho : String → Ty,
      annotation = candidateRigid (substTy rho scheme) ∧
      ∀ name, variableSymbol name ∈ variables (encodeTy scheme) →
        RawAdmitted (constructorCatalog lib query) (rho name) := by
  classical
  let holds := SourceEqualityPCSGuard.holds formulas solver
  let catalog := constructorCatalog lib query
  let types := allTypes top catalog
  have actual : evaluate holds [] (mapSyntax literal (generalize types (encodeTy scheme))) annotation := by
    simpa only [holds, types, catalog, context_types] using accepted
  obtain ⟨replaced, satisfied⟩ := generalize_parts formulas solver catalog (encodeTy scheme) annotation actual
  have facts := replace_facts holds types (encodeTy scheme) annotation replaced
  obtain ⟨substitution, images, paths⟩ := uniform_images holds types (encodeTy scheme) annotation facts satisfied
  have representatives : ∀ name, variableSymbol name ∈ variables (encodeTy scheme) →
      ∃ raw, RawAdmitted catalog raw ∧ candidateRigid raw = substitution (variableSymbol name) := by
    intro name present
    apply SourceSynthesisCurrentTypeReification.universe_reify holds
      (SourceEqualityPCSConstructors.top_true formulas solver) lib query (substitution (variableSymbol name))
    simpa only [context_types, types, catalog] using images (variableSymbol name) present
  let rho (name : String) : Ty :=
    if present : variableSymbol name ∈ variables (encodeTy scheme) then
      Classical.choose (representatives name present) else .tVar "a"
  have chosen : ∀ name, variableSymbol name ∈ variables (encodeTy scheme) →
      RawAdmitted catalog (rho name) ∧ candidateRigid (rho name) = substitution (variableSymbol name) := by
    intro name present
    simpa only [rho, dite_eq_left present] using Classical.choose_spec (representatives name present)
  let lifted := liftSubstitution (fun name => encodeTy (rho name))
  have lifted_eq : ∀ key ∈ variables (encodeTy scheme), lifted key = substitution key := by
    intro key present
    have roundtrip := variable_key_roundtrip (encodeTy scheme) (encodeTy_aliasSafe scheme) key present
    have rawPresent : variableSymbol (decodeVariable key) ∈ variables (encodeTy scheme) := by
      rw [roundtrip]
      exact present
    change candidateRigid (rho (decodeVariable key)) = substitution key
    simpa only [roundtrip] using (chosen (decodeVariable key) rawPresent).2
  have assembled : annotation = instantiate lifted (encodeTy scheme) := by
    apply facts.2 lifted
    intro name path present
    rw [lifted_eq name ((mem_variables name (encodeTy scheme)).mpr ⟨path, present⟩)]
    exact paths name path present
  have compatible := instantiate_rigid_of_compatible (encodeTy scheme)
    (fun name => encodeTy (rho name)) lifted (encodeTy_aliasSafe scheme)
    (fun name _present => liftSubstitution_variable (fun raw => encodeTy (rho raw)) name)
  have instanceEquality : instantiate lifted (encodeTy scheme) = candidateRigid (substTy rho scheme) := by
    simpa only [candidateRigid, substTy_encodeTy] using compatible
  exact ⟨rho, assembled.trans instanceEquality, fun name present => (chosen name present).1⟩

end MicroCFTA.SourceSynthesisCurrentGeneralizeReification
