import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisProgramSourceSize

/-!
# Program roles and counts for the current source

The proof follows the existing row tables and their actual lookup results.
It uses the current context for every leaf. Avoid rules remain unrestricted.
Type annotations do not contribute to the Program component count.
-/
namespace MicroCFTA.SourceSynthesisCurrentProgramStructure
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisProgramRoles (ProgramSyntax ProgramRowSyntax)
open SourceSynthesisProgramSourceSize (ProgramSize RowSize)

private structure ContextFacts (ctx : Context) : Prop where
  components : ∀ entry ∈ ctx.components, ProgramRowSyntax entry.2 ∧ RowSize 1 entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, ProgramRowSyntax entry.2 ∧ RowSize 1 entry.2
  argumentOnly : ProgramSyntax ctx.argumentOnly ∧ ProgramSize 1 ctx.argumentOnly

private theorem node_structure {count : Nat} (rows : List Row)
    (checked : ∀ row ∈ rows, ProgramRowSyntax row ∧ RowSize count row) :
    ProgramSyntax (.node rows) ∧ ProgramSize count (.node rows) :=
  ⟨ProgramSyntax.node rows (fun row member => (checked row member).1),
    ProgramSize.node rows (fun row member => (checked row member).2)⟩

private theorem union_structure {count : Nat} (members : List Expression)
    (checked : ∀ member ∈ members, ProgramSyntax member ∧ ProgramSize count member) :
    ProgramSyntax (.union members) ∧ ProgramSize count (.union members) :=
  ⟨ProgramSyntax.union members (fun member included => (checked member included).1),
    ProgramSize.union members (fun member included => (checked member included).2)⟩

private theorem application_structure {functionCount argumentCount : Nat}
    (types function argument : Expression)
    (functionFacts : ProgramSyntax function ∧ ProgramSize functionCount function)
    (argumentFacts : ProgramSyntax argument ∧ ProgramSize argumentCount argument) :
    ProgramSyntax (application types function argument) ∧
      ProgramSize (functionCount + argumentCount) (application types function argument) := by
  apply node_structure
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact ⟨ProgramRowSyntax.application (types := types) (function := function)
    (argument := argument) rfl functionFacts.1 argumentFacts.1,
    RowSize.application (types := types) (function := function)
      (argument := argument) rfl functionFacts.2 argumentFacts.2⟩

private theorem filter_structure {count : Nat} (candidates goal : Expression)
    (candidateFacts : ProgramSyntax candidates ∧ ProgramSize count candidates) :
    ProgramSyntax (ofType candidates goal) ∧ ProgramSize count (ofType candidates goal) := by
  apply node_structure
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact ⟨ProgramRowSyntax.filter (candidates := candidates) (goal := goal) rfl candidateFacts.1,
    RowSize.filter (candidates := candidates) (goal := goal) rfl candidateFacts.2⟩

private theorem context_facts (lib : Library) (query : Query) :
    ContextFacts (SourceSynthesisCurrentContext.context lib query) := by
  constructor
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨SourceSynthesisProgramRoles.component_roles _ _ _, RowSize.annotated _ _⟩
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨ProgramRowSyntax.annotated _ _, RowSize.annotated _ _⟩
  · apply node_structure
    intro row member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨SourceSynthesisProgramRoles.component_roles _ _ _, RowSize.annotated _ _⟩

private theorem node_entries (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, ProgramRowSyntax entry.2 ∧ RowSize 1 entry.2) :
    ProgramSyntax (.node (entries.map Prod.snd)) ∧
      ProgramSize 1 (.node (entries.map Prod.snd)) := by
  apply node_structure
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_components (ctx : Context) (checked : ContextFacts ctx)
    (select : String × Row → Bool) :
    ProgramSyntax (.node ((ctx.components.filter select).map Prod.snd)) ∧
      ProgramSize 1 (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem without_structure (ctx : Context) (checked : ContextFacts ctx) (names : List String) :
    ProgramSyntax (without ctx names) ∧ ProgramSize 1 (without ctx names) :=
  selected_components ctx checked _

private theorem termsRows_structure (ctx : Context) (checked : ContextFacts ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size →
      ProgramSyntax row ∧ ProgramSize size row := by
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
                · exact node_entries _ checked.arguments
                · exact node_entries _ checked.components
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
                        apply application_structure
                        · exact selected_components ctx checked _
                        · apply union_structure
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_structure ctx checked excluded
                          · exact node_entries _ checked.arguments
                          · exact checked.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_structure
                    · apply union_structure
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_structure ctx checked _
                      · exact node_entries _ checked.arguments
                    · exact union_structure _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  have built := application_structure ctx.types _ _
                    (union_structure _ (ih split.val split.property.2 false))
                    (union_structure _ (ih (rest + 3 - split.val)
                      (by have positive := split.property.1; omega) true))
                  simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2)] using built

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

private theorem relevantRows_structure (ctx : Context) (checked : ContextFacts ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, ProgramSyntax row ∧ ProgramSize size row := by
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
          have argumentsChecked : ∀ entry ∈ arguments,
              ProgramRowSyntax entry.2 ∧ RowSize 1 entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => ProgramRowSyntax entry.2 ∧ RowSize 1 entry.2)
              ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact termsRows_structure ctx checked size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply node_structure
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
              have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk,
                  ProgramSyntax row ∧ ProgramSize size row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk,
                  ProgramSyntax row ∧ ProgramSize size row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves (fun row => ProgramSyntax row ∧ ProgramSize size row)
                  _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                have built := application_structure ctx.types _ _
                  (union_structure _ (ih split.val split.property.2 false _ function functionResult))
                  (union_structure _ (ih (size - split.val)
                    (by have positive := split.property.1; omega) true _ argument argumentResult))
                simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2)] using built
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksChecked chunk included row inside

/-- Every successful current root has its source Program roles and requested component count. -/
theorem current_root_structure (lib : Library) (query : Query) (signed : Int)
    (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression) :
    ProgramSyntax expression ∧ ProgramSize signed.toNat expression := by
  unfold SourceSynthesisCurrentConstruction.firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply filter_structure
    apply union_structure
    intro row member
    obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
    have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk,
        ProgramSyntax row ∧ ProgramSize signed.toNat row := by
      apply mapM_preserves (fun chunk => ∀ row ∈ chunk,
        ProgramSyntax row ∧ ProgramSize signed.toNat row) _ _ _ _ chunksResult
      intro arguments rows result
      exact relevantRows_structure (SourceSynthesisCurrentContext.context lib query)
        (context_facts lib query) signed.toNat true _ rows result
    exact chunksChecked chunk included row inside

end MicroCFTA.SourceSynthesisCurrentProgramStructure
