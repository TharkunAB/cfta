import MicroCFTA.SourceSynthesisRecursiveOrigins

/-!
# One recursive type universe in original FirstOrder instructions

Each instruction is a finite ordinary-node and union prefix over the exact
computed allTypes expression. The prefix treats that expression as one atom.
It has no other binder and no bare lexical variable. Source errors remain
errors. This result does not assert preservation by native operations.
-/
namespace MicroCFTA.SourceSynthesisUniverseOrigins
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top replace finish generalize)
open SourceSynthesisFirstOrderConstruction

/-- Each ordinary row retains the property of all its child instructions. -/
def Children (P : Expression → Prop) (row : Row) : Prop :=
  ∀ child ∈ (match row with | .mk _ _ children => children), P child

/-- A finite source prefix uses one exact recursive universe as its only atom. -/
inductive OverUniverse (types : Expression) : Expression → Prop where
  | atom : OverUniverse types types
  | node (rows : List Row)
      (children : ∀ row ∈ rows, Children (OverUniverse types) row) :
      OverUniverse types (.node rows)
  | union (members : List Expression)
      (children : ∀ child ∈ members, OverUniverse types child) :
      OverUniverse types (.union members)

/-- A binder in the prefix is exactly the selected universe. -/
theorem binder_eq (types : Expression) (smart : Bool) (body : Expression)
    (origin : OverUniverse types (.binder smart body)) : .binder smart body = types := by
  cases origin
  rfl

/-- The computed recursive universe excludes a bare lexical variable from its prefix. -/
theorem not_var (constructors : List (String × Nat)) (index : Nat) :
    ¬ OverUniverse (allTypes top constructors) (.var index) := by
  intro origin
  change OverUniverse (.binder true (allTypesBody top constructors)) (.var index) at origin
  cases origin

/-- These two constructor rules suffice for the source program-table induction. -/
structure Closed (P : Expression → Prop) : Prop where
  node : ∀ rows, (∀ row ∈ rows, Children P row) → P (.node rows)
  union : ∀ members, (∀ child ∈ members, P child) → P (.union members)

private theorem over_closed (types : Expression) : Closed (OverUniverse types) :=
  ⟨OverUniverse.node, OverUniverse.union⟩

section Closure
variable {P : Expression → Prop}

private theorem node_one (closed : Closed P) (name : String) (guard : Guard) (children : List Expression)
    (checked : ∀ child ∈ children, P child) : P (.node [.mk name guard children]) := by
  apply closed.node
  intro row member
  have same := List.mem_singleton.mp member
  subst row
  exact checked

private theorem node_entries (closed : Closed P) (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, Children P entry.2) : P (.node (entries.map Prod.snd)) := by
  apply closed.node
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem arrow_closed (closed : Closed P) (argument result : Expression) (first : P argument) (second : P result) :
    P (arrowType top argument result) := by
  apply node_one closed
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact node_one closed "(->)" top [] (by simp)
  · exact first
  · exact second

private theorem typeExpressions_closed (closed : Closed P) (types : Expression) (typesP : P types) (typ : Ty) :
    P (typeNode top typ) ∧ P (replace types typ) := by
  induction typ using Ty.rec
    (motive_2 := fun entries => ∀ typ ∈ entries, P (typeNode top typ) ∧ P (replace types typ)) with
  | tVar name =>
      exact ⟨by simpa only [typeNode] using node_one closed (variableSymbol name) top [] (by simp),
        by simpa only [replace] using typesP⟩
  | tFun argument result first second =>
      exact ⟨by simpa only [typeNode] using arrow_closed closed _ _ first.1 second.1,
        by simpa only [replace] using arrow_closed closed _ _ first.2 second.2⟩
  | tCons name arguments children =>
      have ordinary (build : Ty → Expression) (inputs : ∀ typ ∈ arguments, P (build typ)) :
          P (.node [.mk name top (arguments.map build)]) := by
        apply node_one closed
        intro child member
        obtain ⟨typ, included, rfl⟩ := List.mem_map.mp member
        exact inputs typ included
      have rigid := ordinary (typeNode top) (fun typ member => (children typ member).1)
      have substituted := ordinary (replace types) (fun typ member => (children typ member).2)
      cases arguments with
      | nil =>
          refine ⟨by simpa only [typeNode] using rigid, ?_⟩
          by_cases recognized : SourceSynthesisGeneralizeSyntax.isVariableSymbol name = true
          · simpa only [replace, recognized, ↓reduceIte] using typesP
          · simpa only [replace, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil] using substituted
      | cons first rest =>
          cases rest with
          | nil => exact ⟨by simpa only [typeNode] using rigid, by simpa only [replace] using substituted⟩
          | cons second rest =>
              cases rest with
              | cons third tail =>
                  exact ⟨by simpa only [typeNode] using rigid, by simpa only [replace] using substituted⟩
              | nil =>
                  by_cases alias : name = "Fun"
                  · subst name
                    constructor
                    · simpa only [typeNode, ↓reduceIte] using
                        (arrow_closed closed _ _ (children first (by simp)).1 (children second (by simp)).1)
                    · simpa only [replace, ↓reduceIte] using
                        (arrow_closed closed _ _ (children first (by simp)).2 (children second (by simp)).2)
                  · exact ⟨by simpa only [typeNode, alias, ↓reduceIte, List.map_cons, List.map_nil] using rigid,
                      by simpa only [replace, alias, ↓reduceIte, List.map_cons, List.map_nil] using substituted⟩
  | nil => rename_i typ member; cases member
  | cons typ entries own rest =>
      rename_i other member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact rest other member

private theorem application_closed (closed : Closed P) (types function argument : Expression)
    (typesP : P types) (first : P function) (second : P argument) :
    P (application types function argument) := by
  apply node_one closed
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact typesP
  · exact node_one closed "(->)" top [] (by simp)
  · exact first
  · exact second

private theorem ofType_closed (closed : Closed P) (candidates goal : Expression) (programs : P candidates) (annotation : P goal) :
    P (ofType candidates goal) := by
  apply node_one closed
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact annotation
  · exact programs

/-- The table induction reads these properties from the actual local bindings. -/
structure ContextClosed (P : Expression → Prop) (ctx : Context) : Prop where
  types : P ctx.types
  components : ∀ entry ∈ ctx.components, Children P entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, Children P entry.2
  argumentOnly : P ctx.argumentOnly

private theorem without_closed (closed : Closed P) (ctx : Context) (clean : ContextClosed P ctx) (names : List String) :
    P (without ctx names) := by
  apply node_entries closed
  intro entry member
  exact clean.components entry (List.mem_filter.mp member).1

private theorem selected_components (closed : Closed P) (ctx : Context) (clean : ContextClosed P ctx)
    (select : String × Row → Bool) :
    P (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries closed
  intro entry member
  exact clean.components entry (List.mem_filter.mp member).1

private theorem termsRows_closed (closed : Closed P) (ctx : Context) (clean : ContextClosed P ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → P row := by
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
                · exact node_entries closed _ clean.arguments
                · exact node_entries closed _ clean.components
              · cases asArgument with
                | false => cases optional
                | true =>
                    have same := List.mem_singleton.mp optional
                    subst row
                    exact clean.argumentOnly
          | succ size =>
              cases size with
              | zero =>
                  rw [termsRows] at member
                  rcases List.mem_append.mp member with restricted | ordinary
                  · obtain ⟨⟨functions, arguments⟩, _, selected⟩ := List.mem_filterMap.mp restricted
                    cases arguments with
                    | none => cases selected
                    | some excluded =>
                        have same := Option.some.inj selected
                        subst row
                        apply application_closed closed _ _ _ clean.types
                        · exact selected_components closed ctx clean _
                        · apply closed.union
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_closed closed ctx clean excluded
                          · exact node_entries closed _ clean.arguments
                          · exact clean.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_closed closed _ _ _ clean.types
                    · apply closed.union
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_closed closed ctx clean _
                      · exact node_entries closed _ clean.arguments
                    · exact closed.union _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _, rfl⟩ := List.mem_map.mp member
                  apply application_closed closed _ _ _ clean.types
                  · exact closed.union _ (ih split.val split.property.2 false)
                  · apply closed.union
                    exact ih _ (by have positive := split.property.1; omega) true

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output)
    (returned : (action >>= next) = .ok value) :
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

private theorem relevantRows_closed (closed : Closed P) (ctx : Context) (clean : ContextClosed P ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, P row := by
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
          have argumentsClean : ∀ entry ∈ arguments, Children P entry.2 :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => Children P entry.2) ctx.argumentEdges names arguments
              clean.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact termsRows_closed closed ctx clean size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            apply closed.node
            intro edge included
            have same := List.mem_singleton.mp included
            subst edge
            exact argumentsClean _ List.mem_cons_self
          · split at computed
            · have same := Except.ok.inj computed
              subst rows
              intro row member
              cases member
            · obtain ⟨chunks, chunksResult, flattened⟩ := bind_ok _ _ _ computed
              have same := Except.ok.inj flattened
              subst rows
              have chunksClean : ∀ chunk ∈ chunks, ∀ row ∈ chunk, P row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, P row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves P _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                apply application_closed closed _ _ _ clean.types
                · exact closed.union _ (ih split.val split.property.2 false _ function functionResult)
                · exact closed.union _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument argumentResult)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksClean chunk included row inside

end Closure

/-- The existing row evaluator preserves each closed context property. -/
theorem relevantRows_induction (P : Expression → Prop) (closed : Closed P)
    (ctx : Context) (contextP : ContextClosed P ctx) (size : Nat)
    (asArgument : Bool) (names : List String) (rows : List Expression)
    (returned : relevantRows ctx asArgument size names = .ok rows) :
    ∀ row ∈ rows, P row :=
  relevantRows_closed closed ctx contextP size asArgument names rows returned

/-- Induct over the actual constructor and error control for any closed source property. -/
theorem firstOrderRaw_induction (P : Expression → Prop) (closed : Closed P)
    (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (contextP : ContextClosed P (context lib query)) (goalP : P (typeNode top query.queryGoal))
    (returned : firstOrderRaw lib query size = .ok expression) : P expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply ofType_closed closed
    · apply closed.union
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have chunksP : ∀ chunk ∈ chunks, ∀ row ∈ chunk, P row := by
        apply mapM_preserves (fun chunk => ∀ row ∈ chunk, P row) _ _ _ _ chunksResult
        intro arguments rows result
        exact relevantRows_closed closed _ contextP size.toNat true _ rows result
      exact chunksP chunk included row inside
    · exact goalP

/-- Every rigid original type is an ordinary prefix over any selected universe. -/
theorem typeNode_overUniverse (types : Expression) (typ : Ty) :
    OverUniverse types (typeNode top typ) :=
  (typeExpressions_closed (over_closed types) types .atom typ).1

/-- Actual replacement inserts only the supplied universe atom into a finite type pattern. -/
theorem replace_overUniverse (types : Expression) (typ : Ty) :
    OverUniverse types (replace types typ) :=
  (typeExpressions_closed (over_closed types) types .atom typ).2

/-- Root relabeling leaves the one computed binder unchanged. -/
theorem finish_overUniverse (constructors : List (String × Nat)) (symbol : String)
    (classes : List (List (List Nat))) (expression : Expression)
    (origin : OverUniverse (allTypes top constructors) expression) :
    OverUniverse (allTypes top constructors) (finish symbol classes expression) := by
  cases origin with
  | atom => exact .atom
  | node rows checked =>
      cases rows with
      | nil => exact .node [] checked
      | cons first rest =>
          cases first with
          | mk name guard children =>
              cases rest with
              | nil =>
                  apply OverUniverse.node
                  intro row member
                  have same := List.mem_singleton.mp member
                  subst row
                  exact checked (.mk name guard children) List.mem_cons_self
              | cons second tail => exact .node _ checked
  | union members checked => exact .union members checked

/-- Actual generalization retains the same recursive universe throughout its finite prefix. -/
theorem generalize_overUniverse (constructors : List (String × Nat)) (typ : Ty) :
    OverUniverse (allTypes top constructors) (generalize (allTypes top constructors) typ) :=
  finish_overUniverse constructors _ _ _ (replace_overUniverse _ typ)

private theorem actual_context_closed (lib : Library) (query : Query) :
    ContextClosed (OverUniverse (typesOf lib query)) (context lib query) := by
  refine ⟨.atom, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact generalize_overUniverse _ _
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact typeNode_overUniverse _ _
  · apply OverUniverse.node
    intro row member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact generalize_overUniverse _ _

/-- The actual terms-table rows use the single universe computed from original input data. -/
theorem termsRows_overUniverse (lib : Library) (query : Query) (asArgument : Bool) (size : Nat)
    (row : Expression) (member : row ∈ termsRows (context lib query) asArgument size) :
    OverUniverse (typesOf lib query) row :=
  termsRows_closed (over_closed _) _ (actual_context_closed lib query) size asArgument row member

/-- A successful actual relevant-table lookup retains that same universe in every row. -/
theorem relevantRows_overUniverse (lib : Library) (query : Query) (asArgument : Bool) (size : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    ∀ row ∈ rows, OverUniverse (typesOf lib query) row :=
  relevantRows_closed (over_closed _) _ (actual_context_closed lib query) size asArgument names rows returned

/-- A successful original FirstOrder constructor uses only its computed allTypes binder. -/
theorem firstOrderRaw_overUniverse (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) :
    OverUniverse (typesOf lib query) expression :=
  firstOrderRaw_induction _ (over_closed _) lib query size expression
    (actual_context_closed lib query) (typeNode_overUniverse _ query.queryGoal) returned

/-- Source errors remain errors; every successful prefix has exactly the computed universe. -/
theorem firstOrderRaw_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression => OverUniverse (typesOf lib query) expression := by
  cases returned : firstOrderRaw lib query size with
  | error error => trivial
  | ok expression => exact firstOrderRaw_overUniverse lib query size expression returned

end MicroCFTA.SourceSynthesisUniverseOrigins
