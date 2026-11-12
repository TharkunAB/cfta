import MicroCFTA.SourceSynthesisCurrentTypeFieldCalls
import MicroCFTA.SourceSynthesisCurrentProgramStructure

/-!
# Type operands of the current source

The list observers retain source order and duplicate operands.
ProgramSyntax supplies the row layouts. The lists alone do not assign roles.
Every collected current Type instruction has its source Type-origin guards.
Native construction and physical field attachment remain separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentTypeOperands
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisProgramRoles (ProgramSyntax)
open SourceSynthesisCurrentSourceGuards (encodedLibrary)
open SourceSynthesisCurrentTypeFieldCalls (allTypes_allowed current_generalized_allowed)
open SourceSynthesisNativeTypeTrace (Origin origin_top)
open SourceSynthesisOriginalTypeAnnotations (OriginalType)
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "Allowed" => SourceEqualityAnnotationConstruction.Allowed

mutual
/-- Collect complete Type instructions at existing Program operand positions. -/
def typeOperands : Expression → List Expression
  | .empty | .var _ | .binder _ _ => []
  | .node rows => rows.flatMap rowTypeOperands
  | .union members => members.flatMap typeOperands
termination_by expression => sizeOf expression

/-- Retain Type fields in order and recurse only through Program operands. -/
def rowTypeOperands : Row → List Expression
  | .mk _ _ [annotation] => [annotation]
  | .mk _ _ [types, marker, function, argument] =>
      types :: marker :: (typeOperands function ++ typeOperands argument)
  | .mk _ _ [goal, candidates] => goal :: typeOperands candidates
  | .mk _ _ _ => []
termination_by row => sizeOf row
end

private def Good (lib : Library) (expression : Expression) : Prop :=
  ∀ field ∈ typeOperands expression, Allowed (Origin (encodedLibrary lib)) (ordinarySymbols field)

private def GoodRow (lib : Library) (row : Row) : Prop :=
  ∀ field ∈ rowTypeOperands row, Allowed (Origin (encodedLibrary lib)) (ordinarySymbols field)

private theorem node_good (lib : Library) (rows : List Row)
    (checked : ∀ row ∈ rows, GoodRow lib row) : Good lib (.node rows) := by
  intro field member
  rw [typeOperands] at member
  obtain ⟨row, included, inside⟩ := List.mem_flatMap.mp member
  exact checked row included field inside

private theorem union_good (lib : Library) (members : List Expression)
    (checked : ∀ member ∈ members, Good lib member) : Good lib (.union members) := by
  intro field member
  rw [typeOperands] at member
  obtain ⟨source, included, inside⟩ := List.mem_flatMap.mp member
  exact checked source included field inside

private theorem annotated_good (lib : Library) (name : String) (guard : Guard) (field : Expression)
    (allowed : Allowed (Origin (encodedLibrary lib)) (ordinarySymbols field)) :
    GoodRow lib (.mk name guard [field]) := by
  intro candidate member
  have same : candidate = field := by simpa only [rowTypeOperands, List.mem_singleton] using member
  exact same.symm ▸ allowed

private theorem generalized_good (lib : Library) (catalog : List (String × Nat))
    (name : String) (scheme : Ty) (original : OriginalType lib scheme) :
    GoodRow lib (component (allTypes top catalog) name
      (SourceSynthesisPr210TypeReflection.encodeTy scheme)) := by
  apply annotated_good
  simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    current_generalized_allowed literal lib catalog scheme original

private theorem rigid_good (lib : Library) (name : String) (typ : Ty) :
    GoodRow lib (.mk name top [SourceSynthesisCurrentContext.typeNode typ]) := by
  apply annotated_good
  simpa only [SourceSynthesisCurrentContext.typeNode,
    SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
    SourceSynthesisOriginalTypeAnnotations.rigid_allowed literal (encodedLibrary lib)
      (SourceSynthesisPr210TypeReflection.encodeTy typ)

private theorem application_good (lib : Library) (types function argument : Expression)
    (typesAllowed : Allowed (Origin (encodedLibrary lib)) (ordinarySymbols types))
    (functionGood : Good lib function) (argumentGood : Good lib argument) :
    Good lib (application types function argument) := by
  intro field member
  simp only [typeOperands, application, rowTypeOperands, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | first | second
  · exact typesAllowed
  · simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      SourceSynthesisOriginalTypeAnnotations.marker_allowed literal (encodedLibrary lib)
  · exact functionGood field first
  · exact argumentGood field second

private theorem filter_good (lib : Library) (candidates goal : Expression)
    (goalAllowed : Allowed (Origin (encodedLibrary lib)) (ordinarySymbols goal))
    (candidatesGood : Good lib candidates) : Good lib (ofType candidates goal) := by
  intro field member
  simp only [typeOperands, ofType, rowTypeOperands, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons] at member
  rcases member with rfl | inside
  · exact goalAllowed
  · exact candidatesGood field inside

private structure ContextGood (lib : Library) (ctx : Context) : Prop where
  types : Allowed (Origin (encodedLibrary lib)) (ordinarySymbols ctx.types)
  components : ∀ entry ∈ ctx.components, GoodRow lib entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, GoodRow lib entry.2
  argumentOnly : Good lib ctx.argumentOnly

private theorem context_good (lib : Library) (query : Query) :
    ContextGood lib (SourceSynthesisCurrentContext.context lib query) := by
  constructor
  · rw [SourceSynthesisCurrentContext.context_types]
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
      allTypes_allowed literal (Origin (encodedLibrary lib)) (origin_top (encodedLibrary lib))
        (SourceSynthesisCurrentContext.constructorCatalog lib query)
  · intro entry member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    apply generalized_good
    exact List.mem_append_left _ (List.mem_map.mpr ⟨source, included, rfl⟩)
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact rigid_good lib _ _
  · apply node_good
    intro row member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    apply generalized_good
    exact List.mem_append_right _ (List.mem_map.mpr ⟨source, included, rfl⟩)

private theorem node_entries (lib : Library) (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, GoodRow lib entry.2) :
    Good lib (.node (entries.map Prod.snd)) := by
  apply node_good
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_components (lib : Library) (ctx : Context) (checked : ContextGood lib ctx)
    (select : String × Row → Bool) :
    Good lib (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem without_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx)
    (names : List String) : Good lib (without ctx names) := selected_components lib ctx checked _

private theorem terms_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → Good lib row := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro asArgument row member
      cases size with
      | zero => simp only [termsRows, List.not_mem_nil] at member
      | succ size =>
          cases size with
          | zero =>
              rw [termsRows] at member
              rcases List.mem_append.mp member with base | optional
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at base
                rcases base with rfl | rfl
                · exact node_entries lib _ checked.arguments
                · exact node_entries lib _ checked.components
              · cases asArgument with
                | false => cases optional
                | true =>
                    have same := List.mem_singleton.mp optional
                    subst row
                    exact checked.argumentOnly
          | succ size =>
              cases size with
              | zero =>
                  rw [termsRows] at member
                  rcases List.mem_append.mp member with restricted | ordinary
                  · obtain ⟨⟨functions, arguments⟩, _included, selected⟩ := List.mem_filterMap.mp restricted
                    cases arguments with
                    | none => cases selected
                    | some excluded =>
                        have same := Option.some.inj selected
                        subst row
                        apply application_good lib _ _ _ checked.types
                        · exact selected_components lib ctx checked _
                        · apply union_good
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_good lib ctx checked excluded
                          · exact node_entries lib _ checked.arguments
                          · exact checked.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_good lib _ _ _ checked.types
                    · apply union_good
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_good lib ctx checked _
                      · exact node_entries lib _ checked.arguments
                    · exact union_good lib _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  apply application_good lib _ _ _ checked.types
                  · exact union_good lib _ (ih split.val split.property.2 false)
                  · exact union_good lib _ (ih _ (by have positive := split.property.1; omega) true)

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output) (returned : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases returned
  | ok input => exact ⟨input, rfl, returned⟩

private theorem mapM_preserves {Error Input Output : Type} (P : Output → Prop)
    (action : Input → Except Error Output) (inputs : List Input) (outputs : List Output)
    (checked : ∀ input output, action input = .ok output → P output)
    (returned : inputs.mapM action = .ok outputs) : ∀ output ∈ outputs, P output := by
  have related := SymbolicDriver.mapM_success_all₂ action inputs outputs returned
  have certificates := related.imp (fun input output success =>
    iff_of_true True.intro (checked input output success))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

private theorem relevant_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, Good lib row := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro asArgument names rows returned
      rw [relevantRows] at returned
      cases resolved : resolveArguments ctx names with
      | none => simp only [resolved] at returned; cases returned
      | some arguments =>
          simp only [resolved] at returned
          obtain ⟨actual, actualResult, computed⟩ := bind_ok _ _ _ returned
          have same := Except.ok.inj actualResult
          subst actual
          have argumentsChecked : ∀ entry ∈ arguments, GoodRow lib entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => GoodRow lib entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact terms_good lib ctx checked size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply node_good
            intro edge included
            have same := List.mem_singleton.mp included
            subst edge
            exact argumentsChecked _ List.mem_cons_self
          · split at computed
            · have same := Except.ok.inj computed
              subst rows
              intro row member
              cases member
            · obtain ⟨chunks, chunksResult, flattened⟩ := bind_ok _ _ _ computed
              have same := Except.ok.inj flattened
              subst rows
              have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good lib row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, Good lib row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves (Good lib) _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                apply application_good lib _ _ _ checked.types
                · exact union_good lib _ (ih split.val split.property.2 false _ function functionResult)
                · exact union_good lib _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument argumentResult)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksChecked chunk included row inside

/-- Actual current source success derives roles and Allowed for every collected Type operand. -/
theorem current_root_type_operands (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole) :
    ProgramSyntax whole ∧ ∀ field ∈ typeOperands whole,
      Allowed (Origin (encodedLibrary lib)) (ordinarySymbols field) := by
  refine ⟨(SourceSynthesisCurrentProgramStructure.current_root_structure lib query signed whole returned).1, ?_⟩
  change Good lib whole
  unfold SourceSynthesisCurrentConstruction.firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst whole
    apply filter_good
    · simpa only [SourceSynthesisCurrentContext.typeNode,
        SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using
        SourceSynthesisOriginalTypeAnnotations.rigid_allowed literal (encodedLibrary lib)
          (SourceSynthesisPr210TypeReflection.encodeTy query.queryGoal)
    · apply union_good
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good lib row := by
        apply mapM_preserves (fun chunk => ∀ row ∈ chunk, Good lib row) _ _ _ _ chunksResult
        intro arguments rows result
        exact relevant_good lib (SourceSynthesisCurrentContext.context lib query)
          (context_good lib query) signed.toNat true _ rows result
      exact chunksChecked chunk included row inside

end MicroCFTA.SourceSynthesisCurrentTypeOperands
