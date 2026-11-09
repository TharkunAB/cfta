import MicroCFTA.SourceSynthesisProgramRoles

/-!
# Component counts of the actual synthesis source layouts

Each component or argument contributes one. Application adds the counts
of its function and argument. A filter retains its candidate count.
Type children remain unrestricted and do not contribute to this measure.
Every alternative of a node or union has the requested count. An empty
set of alternatives has this property at every count.

The proofs follow the actual source tables and their names-only lookup.
They retain the special size-two rows and last-winner argument selection.
This certificate does not identify literal Haskell toProgram, expanded
term node counts, driver depth, work fuel, or ranks with the source count.
-/
namespace MicroCFTA.SourceSynthesisProgramSourceSize
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction
open InternedNestedConstruction (Syntax EdgeSyntax)

mutual
/-- Source Program alternatives share one component count. -/
inductive ProgramSize : Nat → Expression → Prop where
  | empty (count : Nat) : ProgramSize count .empty
  | node {count : Nat} (rows : List Row)
      (checked : ∀ row ∈ rows, RowSize count row) : ProgramSize count (.node rows)
  | union {count : Nat} (members : List Expression)
      (checked : ∀ member ∈ members, ProgramSize count member) : ProgramSize count (.union members)

/-- Source row roles select only the counted Program operands. -/
inductive RowSize : Nat → Row → Prop where
  | annotated (name : String) (annotation : Expression) :
      RowSize 1 (.mk name top [annotation])
  | application {functionCount argumentCount : Nat} {types function argument : Expression} {row : Row}
      (actual : SourceSynthesisFirstOrderConstruction.application types function argument = .node [row])
      (functionSized : ProgramSize functionCount function)
      (argumentSized : ProgramSize argumentCount argument) :
      RowSize (functionCount + argumentCount) row
  | filter {count : Nat} {candidates goal : Expression} {row : Row}
      (actual : ofType candidates goal = .node [row])
      (candidateSized : ProgramSize count candidates) : RowSize count row
end

private theorem application_size {functionCount argumentCount : Nat}
    (types function argument : Expression)
    (functionSized : ProgramSize functionCount function)
    (argumentSized : ProgramSize argumentCount argument) :
    ProgramSize (functionCount + argumentCount) (application types function argument) := by
  apply ProgramSize.node
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact RowSize.application (types := types) (function := function) (argument := argument)
    rfl functionSized argumentSized

private theorem filter_size {count : Nat} (candidates goal : Expression)
    (candidateSized : ProgramSize count candidates) : ProgramSize count (ofType candidates goal) := by
  apply ProgramSize.node
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact RowSize.filter (candidates := candidates) (goal := goal) rfl candidateSized

private structure ContextSizes (ctx : Context) : Prop where
  components : ∀ entry ∈ ctx.components, RowSize 1 entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, RowSize 1 entry.2
  argumentOnly : ProgramSize 1 ctx.argumentOnly

private theorem context_sizes (lib : Library) (query : Query) : ContextSizes (context lib query) := by
  constructor
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact RowSize.annotated _ _
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact RowSize.annotated _ _
  · apply ProgramSize.node
    intro row member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact RowSize.annotated _ _

private theorem node_entries (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, RowSize 1 entry.2) :
    ProgramSize 1 (.node (entries.map Prod.snd)) := by
  apply ProgramSize.node
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_components (ctx : Context) (checked : ContextSizes ctx)
    (select : String × Row → Bool) : ProgramSize 1 (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem without_sizes (ctx : Context) (checked : ContextSizes ctx) (names : List String) :
    ProgramSize 1 (without ctx names) := selected_components ctx checked _

private theorem termsRows_checked (ctx : Context) (checked : ContextSizes ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → ProgramSize size row := by
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
                        apply application_size
                        · exact selected_components ctx checked _
                        · apply ProgramSize.union
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_sizes ctx checked excluded
                          · exact node_entries _ checked.arguments
                          · exact checked.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_size
                    · apply ProgramSize.union
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_sizes ctx checked _
                      · exact node_entries _ checked.arguments
                    · exact ProgramSize.union _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
                  have built := application_size ctx.types _ _
                    (ProgramSize.union _ (ih split.val split.property.2 false))
                    (ProgramSize.union _ (ih (rest + 3 - split.val) (by have positive := split.property.1; omega) true))
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
  have certificates := related.imp (fun input output success => iff_of_true True.intro (checked input output success))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

private theorem relevantRows_checked (ctx : Context) (checked : ContextSizes ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, ProgramSize size row := by
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
          have argumentsChecked : ∀ entry ∈ arguments, RowSize 1 entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => RowSize 1 entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact termsRows_checked ctx checked size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply ProgramSize.node
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
              have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, ProgramSize size row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, ProgramSize size row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves (ProgramSize size) _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                have built := application_size ctx.types _ _
                  (ProgramSize.union _ (ih split.val split.property.2 false _ function functionResult))
                  (ProgramSize.union _ (ih (size - split.val) (by have positive := split.property.1; omega)
                    true _ argument argumentResult))
                simpa only [Nat.add_sub_of_le (Nat.le_of_lt split.property.2)] using built
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksChecked chunk included row inside

/-- Every actual terms-table alternative has the requested component count. -/
theorem termsRows_size (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (expression : Expression) (member : expression ∈ termsRows (context lib query) asArgument size) :
    ProgramSize size expression :=
  termsRows_checked (context lib query) (context_sizes lib query) size asArgument expression member

/-- Successful relevant lookup retains the requested count at every selected alternative. -/
theorem relevantRows_size (lib : Library) (query : Query) (size : Nat) (asArgument : Bool)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    ∀ expression ∈ rows, ProgramSize size expression :=
  relevantRows_checked (context lib query) (context_sizes lib query) size asArgument names rows returned

/-- Successful signed construction derives its count from the actual source recursion. -/
theorem firstOrderRaw_size (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) : ProgramSize size.toNat expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply filter_size
    apply ProgramSize.union
    intro row member
    obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
    have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, ProgramSize size.toNat row := by
      apply mapM_preserves (fun chunk => ∀ row ∈ chunk, ProgramSize size.toNat row) _ _ _ _ chunksResult
      intro arguments rows result
      exact relevantRows_size lib query size.toNat true _ rows result
    exact chunksChecked chunk included row inside

/-- A successful signed request cannot come from the negative missing-table branch. -/
theorem firstOrderRaw_nonnegative (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) : 0 ≤ size := by
  by_cases nonnegative : 0 ≤ size
  · exact nonnegative
  · have belowZero : size < 0 := by omega
    rw [firstOrderRaw_negative lib query size belowZero] at returned
    cases returned

/-- Errors remain explicit. Every successful result retains its requested source count. -/
theorem firstOrderRaw_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression => ProgramSize size.toNat expression := by
  cases returned : firstOrderRaw lib query size with
  | error => trivial
  | ok expression => exact firstOrderRaw_size lib query size expression returned

end MicroCFTA.SourceSynthesisProgramSourceSize
