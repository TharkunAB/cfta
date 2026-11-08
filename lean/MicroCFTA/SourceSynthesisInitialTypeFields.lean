import MicroCFTA.SourceSynthesisProgramRoles

/-!
# Original synthesis Type fields

Each row certificate retains its source instruction and original input entry.
Program children recurse. Type children retain their exact constructor syntax.
Names can coincide. The certificates do not describe later native operations.
-/
namespace MicroCFTA.SourceSynthesisInitialTypeFields
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top generalize)
open SourceSynthesisFirstOrderConstruction

mutual
/-- Program syntax retains the exact source of each Type field. -/
inductive Program (lib : Library) (query : Query) : Expression → Prop where
  | empty : Program lib query .empty
  | node (rows : List Row) (fields : ∀ row ∈ rows, ProgramRow lib query row) :
      Program lib query (.node rows)
  | union (members : List Expression) (fields : ∀ member ∈ members, Program lib query member) :
      Program lib query (.union members)

/-- Original row variants assign Type fields by position, not by name. -/
inductive ProgramRow (lib : Library) (query : Query) : Row → Prop where
  | component (entry : String × Ty × List String) (member : entry ∈ lib.libraryGroups) :
      ProgramRow lib query (component (typesOf lib query) entry.1 entry.2.1)
  | argumentOnly (entry : String × Ty) (member : entry ∈ lib.libraryArgumentOnly) :
      ProgramRow lib query (component (typesOf lib query) entry.1 entry.2)
  | argument (entry : String × Ty) (member : entry ∈ query.queryArguments) :
      ProgramRow lib query (.mk entry.1 top [typeNode top entry.2])
  | application {function argument : Expression} {row : Row}
      (actual : application (typesOf lib query) function argument = .node [row])
      (functionFields : Program lib query function) (argumentFields : Program lib query argument) :
      ProgramRow lib query row
  | filter {candidates : Expression} {row : Row}
      (actual : ofType candidates (typeNode top query.queryGoal) = .node [row])
      (candidateFields : Program lib query candidates) : ProgramRow lib query row
end

/-- The local source tables retain exact input membership and the shared universe syntax. -/
structure ContextFields (lib : Library) (query : Query) (ctx : Context) : Prop where
  types : ctx.types = typesOf lib query
  components : ∀ entry ∈ ctx.components, ProgramRow lib query entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, ProgramRow lib query entry.2
  argumentOnly : Program lib query ctx.argumentOnly

/-- Actual context construction derives every component and argument Type field. -/
theorem context_fields (lib : Library) (query : Query) :
    ContextFields lib query (context lib query) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact ProgramRow.component source included
  · intro entry member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact ProgramRow.argument source included
  · apply Program.node
    intro row member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact ProgramRow.argumentOnly source included

private theorem node_entries (lib : Library) (query : Query) (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, ProgramRow lib query entry.2) :
    Program lib query (.node (entries.map Prod.snd)) := by
  apply Program.node
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_components (ctx : Context) (checked : ContextFields lib query ctx)
    (select : String × Row → Bool) :
    Program lib query (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem without_fields (ctx : Context) (checked : ContextFields lib query ctx)
    (names : List String) : Program lib query (without ctx names) :=
  selected_components ctx checked _

private theorem application_fields (ctx : Context) (checked : ContextFields lib query ctx)
    (function argument : Expression) (first : Program lib query function)
    (second : Program lib query argument) : Program lib query (application ctx.types function argument) := by
  rw [checked.types]
  apply Program.node
  intro row member
  obtain rfl := List.mem_singleton.mp member
  exact ProgramRow.application rfl first second

private theorem filter_fields (candidates : Expression) (fields : Program lib query candidates) :
    Program lib query (ofType candidates (typeNode top query.queryGoal)) := by
  apply Program.node
  intro row member
  obtain rfl := List.mem_singleton.mp member
  exact ProgramRow.filter rfl fields

private theorem terms_checked (ctx : Context) (checked : ContextFields lib query ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → Program lib query row := by
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
                · exact node_entries lib query _ checked.arguments
                · exact node_entries lib query _ checked.components
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
                        apply application_fields ctx checked
                        · exact selected_components ctx checked _
                        · apply Program.union
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_fields ctx checked excluded
                          · exact node_entries lib query _ checked.arguments
                          · exact checked.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_fields ctx checked
                    · apply Program.union
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_fields ctx checked _
                      · exact node_entries lib query _ checked.arguments
                    · exact Program.union _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  apply application_fields ctx checked
                  · exact Program.union _ (ih split.val split.property.2 false)
                  · apply Program.union
                    exact ih _ (by have positive := split.property.1; omega) true

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
  have certificates := related.imp (fun input output success => iff_of_true True.intro (checked input output success))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

private theorem relevant_checked (ctx : Context) (checked : ContextFields lib query ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, Program lib query row := by
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
          have argumentsChecked : ∀ entry ∈ arguments, ProgramRow lib query entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => ProgramRow lib query entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact terms_checked ctx checked size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply Program.node
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
              have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Program lib query row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, Program lib query row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves (Program lib query) _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                apply application_fields ctx checked
                · exact Program.union _ (ih split.val split.property.2 false _ function functionResult)
                · exact Program.union _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument argumentResult)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksChecked chunk included row inside

/-- Every actual terms cell retains its original Type-field sources. -/
theorem termsRows_fields (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (row : Expression) (member : row ∈ termsRows (context lib query) asArgument size) :
    Program lib query row :=
  terms_checked (context lib query) (context_fields lib query) size asArgument row member

/-- Name selection retains source entries even when names coincide. -/
theorem relevantRows_fields (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    ∀ row ∈ rows, Program lib query row :=
  relevant_checked (context lib query) (context_fields lib query) size asArgument names rows returned

/-- Actual signed synthesis derives the joint source certificate from its input data. -/
theorem firstOrderRaw_fields (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) : Program lib query expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply filter_fields
    apply Program.union
    intro row member
    obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
    have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Program lib query row := by
      apply mapM_preserves (fun chunk => ∀ row ∈ chunk, Program lib query row) _ _ _ _ chunksResult
      intro arguments rows result
      exact relevantRows_fields lib query size.toNat true _ rows result
    exact chunksChecked chunk included row inside

/-- Source errors remain explicit and accepted results carry the initial field certificate. -/
theorem firstOrderRaw_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression => Program lib query expression := by
  cases returned : firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_fields lib query size expression returned

end MicroCFTA.SourceSynthesisInitialTypeFields
