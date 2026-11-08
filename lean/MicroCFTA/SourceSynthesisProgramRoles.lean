import MicroCFTA.SourceSynthesisGuardRegions
import MicroCFTA.SourceSynthesisSelectionOrigins
import MicroCFTA.SymbolicNormalization

/-!
# Program occurrences in the actual FirstOrder source instructions

Program rows assign Type fields by their source positions. A Type field may
contain arbitrary syntax. Component names do not determine their roles.
The certificate has no Program rule for a capture or a Mu binder.
These results concern original instructions. Current execution, narrowed
rows, and physical constructor results need a separate role transport law.
-/
namespace MicroCFTA.SourceSynthesisProgramRoles
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
open InternedNestedConstruction (Syntax EdgeSyntax)

mutual
/-- Program syntax retains source node rows and ordered union alternatives. -/
inductive ProgramSyntax : Expression → Prop where
  | empty : ProgramSyntax .empty
  | node (rows : List Row) (checked : ∀ row ∈ rows, ProgramRowSyntax row) : ProgramSyntax (.node rows)
  | union (members : List Expression) (checked : ∀ member ∈ members, ProgramSyntax member) :
      ProgramSyntax (.union members)

/-- Each Program row retains its actual source layout and full guard. -/
inductive ProgramRowSyntax : Row → Prop where
  | annotated (name : String) (annotation : Expression) :
      ProgramRowSyntax (.mk name top [annotation])
  | application {types function argument : Expression} {row : Row}
      (actual : SourceSynthesisFirstOrderConstruction.application types function argument = .node [row])
      (functionRole : ProgramSyntax function) (argumentRole : ProgramSyntax argument) : ProgramRowSyntax row
  | filter {candidates goal : Expression} {row : Row}
      (actual : SourceSynthesisFirstOrderConstruction.ofType candidates goal = .node [row])
      (candidateRole : ProgramSyntax candidates) : ProgramRowSyntax row
end

/-- A lexical capture is absent from the Program phase. -/
theorem ProgramSyntax.not_var (index : Nat) : ¬ ProgramSyntax (.var index) := by
  intro role
  cases role

/-- A Mu instruction is absent from the Program phase. -/
theorem ProgramSyntax.not_binder (smart : Bool) (body : Expression) : ¬ ProgramSyntax (.binder smart body) := by
  intro role
  cases role

/-- A component retains its source Top guard and its generalized Type annotation. -/
theorem component_roles (types : Expression) (name : String) (typ : Ty) :
    ProgramRowSyntax (component types name typ) := .annotated name _

/-- A rigid query argument has the same Top owner guard and one Type annotation. -/
theorem rigidArgument_roles (name : String) (typ : Ty) :
    ProgramRowSyntax (.mk name top [typeNode top typ]) := .annotated name _

/-- Source application assigns Program roles only to function and argument. -/
theorem application_roles (types function argument : Expression)
    (functionRole : ProgramSyntax function) (argumentRole : ProgramSyntax argument) :
    ProgramSyntax (application types function argument) := by
  apply ProgramSyntax.node
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact ProgramRowSyntax.application (types := types) (function := function) (argument := argument)
    rfl functionRole argumentRole

/-- Source filter assigns a Program role only to its candidate child. -/
theorem filter_roles (candidates goal : Expression) (candidateRole : ProgramSyntax candidates) :
    ProgramSyntax (ofType candidates goal) := by
  apply ProgramSyntax.node
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact ProgramRowSyntax.filter (candidates := candidates) (goal := goal) rfl candidateRole

/-- Every Program row has one of the three concrete source endpoint regions. -/
theorem ProgramRowSyntax.guard_regions {symbol : String} {guard : Guard} {children : List Expression}
    (role : ProgramRowSyntax (.mk symbol guard children)) :
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
      SourceSynthesisGuardRegions.componentRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
      SourceSynthesisGuardRegions.applicationRegion path) ∨
    (∀ path ∈ EqualityNormalize.members ((SourceCompactGuards.sourceEqualities guard).getD []),
      SourceSynthesisGuardRegions.filterRegion path) := by
  cases role with
  | annotated name annotation =>
      left
      intro path member
      have empty : SourceCompactGuards.sourceEqualities (top : Guard) = some [] := rfl
      rw [empty] at member
      simp [EqualityNormalize.members] at member
  | application actual functionRole argumentRole =>
      exact Or.inr (Or.inl (SourceSynthesisGuardRegions.application_guard_endpoints
        _ _ _ symbol guard children actual).2)
  | filter actual candidateRole =>
      exact Or.inr (Or.inr (SourceSynthesisGuardRegions.filter_guard_endpoints
        _ _ symbol guard children actual).2)

private structure ContextRoles (ctx : Context) : Prop where
  components : ∀ entry ∈ ctx.components, ProgramRowSyntax entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, ProgramRowSyntax entry.2
  argumentOnly : ProgramSyntax ctx.argumentOnly

private theorem context_roles (lib : Library) (query : Query) : ContextRoles (context lib query) := by
  constructor
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact component_roles _ _ _
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact rigidArgument_roles _ _
  · apply ProgramSyntax.node
    intro row member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact component_roles _ _ _

private theorem node_entries (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, ProgramRowSyntax entry.2) :
    ProgramSyntax (.node (entries.map Prod.snd)) := by
  apply ProgramSyntax.node
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_components (ctx : Context) (checked : ContextRoles ctx)
    (select : String × Row → Bool) : ProgramSyntax (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem without_roles (ctx : Context) (checked : ContextRoles ctx) (names : List String) :
    ProgramSyntax (without ctx names) := selected_components ctx checked _

private theorem termsRows_checked (ctx : Context) (checked : ContextRoles ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → ProgramSyntax row := by
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
                        apply application_roles
                        · exact selected_components ctx checked _
                        · apply ProgramSyntax.union
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_roles ctx checked excluded
                          · exact node_entries _ checked.arguments
                          · exact checked.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_roles
                    · apply ProgramSyntax.union
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_roles ctx checked _
                      · exact node_entries _ checked.arguments
                    · exact ProgramSyntax.union _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  apply application_roles
                  · exact ProgramSyntax.union _ (ih split.val split.property.2 false)
                  · apply ProgramSyntax.union
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

private theorem relevantRows_checked (ctx : Context) (checked : ContextRoles ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, ProgramSyntax row := by
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
          have argumentsChecked : ∀ entry ∈ arguments, ProgramRowSyntax entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => ProgramRowSyntax entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact termsRows_checked ctx checked size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply ProgramSyntax.node
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
              have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, ProgramSyntax row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, ProgramSyntax row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves ProgramSyntax _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                apply application_roles
                · exact ProgramSyntax.union _ (ih split.val split.property.2 false _ function functionResult)
                · exact ProgramSyntax.union _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument argumentResult)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksChecked chunk included row inside

/-- Every actual terms-table alternative has its source Program certificate. -/
theorem termsRows_roles (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (row : Expression) (member : row ∈ termsRows (context lib query) asArgument size) : ProgramSyntax row :=
  termsRows_checked (context lib query) (context_roles lib query) size asArgument row member

/-- Successful names-only relevant lookup preserves the actual selected Program rows. -/
theorem relevantRows_roles (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    ∀ row ∈ rows, ProgramSyntax row :=
  relevantRows_checked (context lib query) (context_roles lib query) size asArgument names rows returned

/-- Actual original signed synthesis derives its Program roles without a supplied role certificate. -/
theorem firstOrderRaw_roles (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) : ProgramSyntax expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply filter_roles
    apply ProgramSyntax.union
    intro row member
    obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
    have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, ProgramSyntax row := by
      apply mapM_preserves (fun chunk => ∀ row ∈ chunk, ProgramSyntax row) _ _ _ _ chunksResult
      intro arguments rows result
      exact relevantRows_roles lib query size.toNat true _ rows result
    exact chunksChecked chunk included row inside

/-- Errors remain explicit; every actual successful original request has Program roles. -/
theorem firstOrderRaw_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression => ProgramSyntax expression := by
  cases returned : firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_roles lib query size expression returned

end MicroCFTA.SourceSynthesisProgramRoles
