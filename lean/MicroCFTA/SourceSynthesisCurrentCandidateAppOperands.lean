import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisSelectionOrigins
import MicroCFTA.SymbolicDriver

namespace MicroCFTA.SourceSynthesisCurrentCandidateAppOperands
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisFirstOrderConstruction
open SourceSynthesisGeneralizeSyntax (eqGuard top)

private def FunctionShape (function : Expression) : Prop :=
  (∃ rows : List Row, function = .node rows) ∨
    ∃ pools : List (List Row), function = .union (pools.map fun rows => .node rows)

private def Leaf (row : Row) : Prop :=
  ∃ (name : String) (annotation : Expression), row = .mk name top [annotation]

private def NodeFacts (ctx : Context) (expression : Expression) : Prop :=
  ∃ rows : List Row, expression = .node rows ∧
    ∀ (types function argument : Expression),
      EdgeSyntax.mk "app"
        (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
        [types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument] ∈ rows →
      types = ctx.types ∧ FunctionShape function

private theorem leaf_node (ctx : Context) (rows : List Row)
    (leaves : ∀ row ∈ rows, Leaf row) : NodeFacts ctx (.node rows) := by
  refine ⟨rows, rfl, ?_⟩
  intro types function argument member
  obtain ⟨name, annotation, same⟩ := leaves _ member
  have lengths := congrArg (fun row : Row => match row with | .mk _ _ children => children.length) same
  change (4 : Nat) = 1 at lengths
  omega

private theorem application_facts (ctx : Context) (function argument : Expression)
    (shape : FunctionShape function) : NodeFacts ctx (application ctx.types function argument) := by
  refine ⟨[.mk "app"
    (eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    [ctx.types, SourceSynthesisTypeSyntax.arrowMarker top, function, argument]], rfl, ?_⟩
  intro types selectedFunction selectedArgument member
  have same := List.mem_singleton.mp member
  cases same
  exact ⟨rfl, shape⟩

private theorem union_shape (members : List Expression)
    (nodes : ∀ member ∈ members, ∃ rows : List Row, member = .node rows) :
    FunctionShape (.union members) := by
  have gathered : ∃ pools : List (List Row), members = pools.map (fun rows => .node rows) := by
    induction members with
    | nil => exact ⟨[], rfl⟩
    | cons first rest ih =>
      obtain ⟨rows, rfl⟩ := nodes first List.mem_cons_self
      obtain ⟨pools, same⟩ := ih
        (fun member included => nodes member (List.mem_cons_of_mem _ included))
      exact ⟨rows :: pools, by simp only [List.map_cons, same]⟩
  obtain ⟨pools, same⟩ := gathered
  exact .inr ⟨pools, congrArg Syntax.union same⟩

private structure ContextFacts (ctx : Context) : Prop where
  components : ∀ entry ∈ ctx.components, Leaf entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, Leaf entry.2
  argumentOnly : NodeFacts ctx ctx.argumentOnly

private theorem context_facts (lib : SourceSynthesisTypeSyntax.Library)
    (query : SourceSynthesisTypeSyntax.Query) :
    ContextFacts (SourceSynthesisCurrentContext.context lib query) := by
  constructor
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, rfl⟩
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, rfl⟩
  · apply leaf_node
    intro row member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    exact ⟨_, _, rfl⟩

private theorem node_entries (ctx : Context) (entries : List (String × Row))
    (leaves : ∀ entry ∈ entries, Leaf entry.2) : NodeFacts ctx (.node (entries.map Prod.snd)) := by
  apply leaf_node
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact leaves entry included

private theorem terms_facts (ctx : Context) (checked : ContextFacts ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → NodeFacts ctx row := by
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
          · exact node_entries ctx _ checked.arguments
          · exact node_entries ctx _ checked.components
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
              apply application_facts
              exact .inl ⟨_, rfl⟩
          · have same := List.mem_singleton.mp ordinary
            subst row
            apply application_facts
            apply union_shape
            intro child included
            simp only [List.mem_cons, List.not_mem_nil, or_false] at included
            rcases included with rfl | rfl
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩
        | succ rest =>
          rw [termsRows] at member
          obtain ⟨split, _included, rfl⟩ := List.mem_map.mp member
          apply application_facts
          apply union_shape
          intro function included
          obtain ⟨rows, same, _facts⟩ := ih split.val split.property.2 false function included
          exact ⟨rows, same⟩

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

private theorem relevant_facts (ctx : Context) (checked : ContextFacts ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, NodeFacts ctx row := by
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
      have argumentsChecked : ∀ entry ∈ arguments, Leaf entry.2 :=
        SourceSynthesisSelectionOrigins.resolveSelection_preserves (fun entry => Leaf entry.2)
          ctx.argumentEdges names arguments checked.arguments resolved
      split at computed
      · have same := Except.ok.inj computed
        subst rows
        exact terms_facts ctx checked size asArgument
      · have same := Except.ok.inj computed
        subst rows
        intro row member
        have same := List.mem_singleton.mp member
        subst row
        apply leaf_node
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
          have chunksChecked : ∀ chunk ∈ chunks, ∀ row ∈ chunk, NodeFacts ctx row := by
            apply mapM_preserves (fun chunk => ∀ row ∈ chunk, NodeFacts ctx row) _ _ _ _ chunksResult
            intro split choices choicesResult
            apply mapM_preserves (NodeFacts ctx) _ _ _ _ choicesResult
            intro offset expression expressionResult
            obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
            obtain ⟨argument, _argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
            have same := Except.ok.inj completed
            subst expression
            apply application_facts
            apply union_shape
            intro member included
            obtain ⟨sourceRows, same, _facts⟩ :=
              ih split.val split.property.2 false _ function functionResult member included
            exact ⟨sourceRows, same⟩
          intro row member
          obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
          exact chunksChecked chunk included row inside

/-- The actual current factory fixes each source app Type operand and function pool shape. -/
theorem current_candidate_app_operands
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole) :
    let ctx := SourceSynthesisCurrentContext.context lib query
    ∃ chunks : List (List SourceSynthesisFirstOrderConstruction.Expression),
      (SourceSynthesisSelections.permutations ctx.argumentEdges).mapM
        (fun selected => SourceSynthesisFirstOrderConstruction.relevantRows
          ctx true signed.toNat (selected.map Prod.fst)) = .ok chunks ∧
      whole = SourceSynthesisFirstOrderConstruction.ofType (.union chunks.flatten)
        (SourceSynthesisCurrentContext.typeNode query.queryGoal) ∧
      ∀ candidate ∈ chunks.flatten,
        ∃ rows : List SourceSynthesisFirstOrderConstruction.Row,
          candidate = .node rows ∧
          ∀ (types function argument : SourceSynthesisFirstOrderConstruction.Expression),
            InternedNestedConstruction.EdgeSyntax.mk "app"
              (SourceSynthesisGeneralizeSyntax.eqGuard
                [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
              [types, SourceSynthesisTypeSyntax.arrowMarker SourceSynthesisGeneralizeSyntax.top,
                function, argument] ∈ rows →
            types = SourceSynthesisTypeSyntax.allTypes SourceSynthesisGeneralizeSyntax.top
              (SourceSynthesisCurrentContext.constructorCatalog lib query) ∧
            ((∃ functionRows : List SourceSynthesisFirstOrderConstruction.Row,
                function = .node functionRows) ∨
              ∃ pools : List (List SourceSynthesisFirstOrderConstruction.Row),
                function = .union (pools.map fun functionRows => .node functionRows)) := by
  dsimp only
  unfold SourceSynthesisCurrentConstruction.firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst whole
    refine ⟨chunks, chunksResult, rfl, ?_⟩
    have chunksChecked : ∀ chunk ∈ chunks, ∀ candidate ∈ chunk,
        NodeFacts (SourceSynthesisCurrentContext.context lib query) candidate := by
      apply mapM_preserves (fun chunk => ∀ candidate ∈ chunk,
        NodeFacts (SourceSynthesisCurrentContext.context lib query) candidate) _ _ _ _ chunksResult
      intro selected rows result
      exact relevant_facts (SourceSynthesisCurrentContext.context lib query)
        (context_facts lib query) signed.toNat true _ rows result
    intro candidate member
    obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
    obtain ⟨rows, same, facts⟩ := chunksChecked chunk included candidate inside
    exact ⟨rows, same, facts⟩

end MicroCFTA.SourceSynthesisCurrentCandidateAppOperands
