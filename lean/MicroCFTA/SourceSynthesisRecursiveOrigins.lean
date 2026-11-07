import MicroCFTA.SourceSynthesisFirstOrderConstruction
import MicroCFTA.SourceSynthesisSelectionOrigins
import MicroCFTA.SymbolicNormalization

/-!
# Equality-free Mu bodies in original synthesis instructions

Each binder body has only the supplied top guard. Finite ordinary roots can
have equality guards. The actual FirstOrder local bindings and terms-table
rows derive this restriction from Library and Query data.
The result concerns constructor instructions. It does not assert preservation
by native normalization, projection, intersection, or enumeration.
-/
namespace MicroCFTA.SourceSynthesisRecursiveOrigins
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)

section Generic
variable {Symbol G : Type}

mutual
/-- Every binder has a top-only body; ordinary root guards remain unrestricted. -/
def PlainMu (top : G) : Syntax Symbol G → Prop
  | .empty | .var _ => True
  | .node rows => EdgesPlainMu top rows
  | .union children => ManyPlainMu top children
  | .binder _ body => (∀ guard ∈ guards body, guard = top) ∧ PlainMu top body

/-- Ordered child instructions retain the same binder restriction. -/
def ManyPlainMu (top : G) : List (Syntax Symbol G) → Prop
  | [] => True
  | first :: rest => PlainMu top first ∧ ManyPlainMu top rest

/-- Ordinary edge guards do not change the binder bodies of their children. -/
def EdgesPlainMu (top : G) : List (EdgeSyntax Symbol G) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyPlainMu top children ∧ EdgesPlainMu top rest
end

mutual
/-- A completely top-guarded instruction satisfies the binder restriction. -/
theorem of_guards (top : G) (expression : Syntax Symbol G)
    (checked : ∀ guard ∈ guards expression, guard = top) : PlainMu top expression := by
  cases expression with
  | empty | var => trivial
  | node rows => exact edges_of_guards top rows checked
  | union children => exact children_of_guards top children checked
  | binder smart body => exact ⟨checked, of_guards top body checked⟩
termination_by sizeOf expression

private theorem children_of_guards (top : G) (children : List (Syntax Symbol G))
    (checked : ∀ guard ∈ childGuards children, guard = top) : ManyPlainMu top children := by
  cases children with
  | nil => trivial
  | cons first rest =>
      exact ⟨of_guards top first (fun guard member => checked guard (List.mem_append_left _ member)),
        children_of_guards top rest (fun guard member => checked guard (List.mem_append_right _ member))⟩
termination_by sizeOf children

private theorem edges_of_guards (top : G) (rows : List (EdgeSyntax Symbol G))
    (checked : ∀ guard ∈ edgeGuards rows, guard = top) : EdgesPlainMu top rows := by
  cases rows with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk name guard children =>
          exact ⟨children_of_guards top children (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_left _ member))),
            edges_of_guards top rest (fun other member => checked other
              (List.mem_cons_of_mem _ (List.mem_append_right _ member)))⟩
termination_by sizeOf rows
end

private theorem many_of_mem (top : G) (children : List (Syntax Symbol G))
    (checked : ∀ child ∈ children, PlainMu top child) : ManyPlainMu top children := by
  induction children with
  | nil => trivial
  | cons first rest ih =>
      exact ⟨checked first List.mem_cons_self,
        ih (fun child member => checked child (List.mem_cons_of_mem _ member))⟩

/-- Any ordinary edge can retain children with clean binder bodies. -/
theorem node (top : G) (name : Symbol) (guard : G) (children : List (Syntax Symbol G))
    (checked : ∀ child ∈ children, PlainMu top child) :
    PlainMu top (.node [.mk name guard children]) :=
  ⟨many_of_mem top children checked, True.intro⟩

/-- A source union retains the binder restriction of each operand. -/
theorem union (top : G) (children : List (Syntax Symbol G))
    (checked : ∀ child ∈ children, PlainMu top child) : PlainMu top (.union children) :=
  many_of_mem top children checked

private theorem node_rows (top : G) (rows : List (EdgeSyntax Symbol G))
    (checked : ∀ row ∈ rows, PlainMu top (.node [row])) : PlainMu top (.node rows) := by
  induction rows with
  | nil => trivial
  | cons first rest ih =>
      cases first with
      | mk name guard children =>
          exact ⟨(checked _ List.mem_cons_self).1,
            ih (fun row member => checked row (List.mem_cons_of_mem _ member))⟩

private theorem node_entries (top : G) (entries : List (String × EdgeSyntax Symbol G))
    (checked : ∀ entry ∈ entries, PlainMu top (.node [entry.2])) :
    PlainMu top (.node (entries.map Prod.snd)) := by
  apply node_rows
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

end Generic

open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top replace finish generalize)
open SourceSynthesisFirstOrderConstruction

/-- The actual recursive source universe has top-only binder bodies. -/
theorem allTypes_plainMu (constructors : List (String × Nat)) : PlainMu top (allTypes top constructors) :=
  of_guards top _ (allTypes_guards top constructors)

/-- Rigid query types retain the original binder restriction. -/
theorem typeNode_plainMu (typ : Ty) : PlainMu top (typeNode top typ) :=
  of_guards top _ (typeNode_guards top typ)

private theorem arrow_plainMu (argument result : Expr Guard)
    (first : PlainMu top argument) (second : PlainMu top result) :
    PlainMu top (arrowType top argument result) := by
  apply node
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact node top "(->)" top [] (by simp)
  · exact first
  · exact second

/-- Simultaneous finite-pattern replacement does not enter the supplied universe. -/
theorem replace_plainMu (types : Expr Guard) (clean : PlainMu top types) (typ : Ty) :
    PlainMu top (replace types typ) := by
  induction typ using Ty.rec
    (motive_2 := fun typesList => ∀ typ ∈ typesList, PlainMu top (replace types typ)) with
  | tVar _ => simpa only [replace] using clean
  | tFun argument result first second => simpa only [replace] using arrow_plainMu _ _ first second
  | tCons name arguments children =>
      have ordinary : PlainMu top (.node [.mk name top (arguments.map (replace types))]) := by
        apply node
        intro child member
        obtain ⟨typ, included, rfl⟩ := List.mem_map.mp member
        exact children typ included
      cases arguments with
      | nil =>
          by_cases recognized : SourceSynthesisGeneralizeSyntax.isVariableSymbol name = true
          · simpa only [replace, recognized, ↓reduceIte] using clean
          · simpa only [replace, recognized, Bool.false_eq_true, ↓reduceIte, List.map_nil] using ordinary
      | cons first rest =>
          cases rest with
          | nil => simpa only [replace] using ordinary
          | cons second rest =>
              cases rest with
              | cons third tail => simpa only [replace] using ordinary
              | nil =>
                  by_cases alias : name = "Fun"
                  · subst name
                    simpa only [replace, ↓reduceIte] using
                      arrow_plainMu _ _ (children first (by simp)) (children second (by simp))
                  · simpa only [replace, alias, ↓reduceIte, List.map_cons, List.map_nil] using ordinary
  | nil => rename_i typ member; cases member
  | cons typ typesList own rest =>
      rename_i other member
      rcases List.mem_cons.mp member with rfl | member
      · exact own
      · exact rest other member

/-- The native outer match installs equality only at an ordinary root. -/
theorem finish_plainMu (symbol : String) (classes : List (List (List Nat))) (expression : Expr Guard)
    (clean : PlainMu top expression) : PlainMu top (finish symbol classes expression) := by
  cases expression with
  | empty | var | union | binder => exact clean
  | node rows =>
      cases rows with
      | nil => exact clean
      | cons first rest =>
          cases first with
          | mk name guard children =>
              cases rest with
              | nil => exact clean
              | cons second tail => exact clean

/-- Actual finite-type generalization leaves every inserted binder body unchanged. -/
theorem generalize_plainMu (types : Expr Guard) (clean : PlainMu top types) (typ : Ty) :
    PlainMu top (generalize types typ) :=
  finish_plainMu _ _ _ (replace_plainMu types clean typ)

/-- A component stores its generalized annotation below an ordinary row. -/
theorem component_plainMu (types : Expression) (clean : PlainMu top types) (name : String) (typ : Ty) :
    PlainMu top (.node [component types name typ]) := by
  apply node
  intro child member
  have same : child = generalize types typ := List.mem_singleton.mp member
  subst child
  exact generalize_plainMu types clean typ

/-- Application equalities remain outside the binder bodies of all four children. -/
theorem application_plainMu (types function argument : Expression)
    (typesClean : PlainMu top types) (first : PlainMu top function) (second : PlainMu top argument) :
    PlainMu top (application types function argument) := by
  apply node
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact typesClean
  · exact node top "(->)" top [] (by simp)
  · exact first
  · exact second

/-- The root filter adds its equality at an ordinary node. -/
theorem ofType_plainMu (candidates goal : Expression)
    (programs : PlainMu top candidates) (annotation : PlainMu top goal) :
    PlainMu top (ofType candidates goal) := by
  apply node
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact annotation
  · exact programs

private structure CleanContext (ctx : Context) : Prop where
  types : PlainMu top ctx.types
  components : ∀ entry ∈ ctx.components, PlainMu top (.node [entry.2])
  arguments : ∀ entry ∈ ctx.argumentEdges, PlainMu top (.node [entry.2])
  argumentOnly : PlainMu top ctx.argumentOnly

private theorem context_clean (lib : Library) (query : Query) : CleanContext (context lib query) := by
  have typesClean : PlainMu top (typesOf lib query) := allTypes_plainMu _
  refine ⟨typesClean, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact component_plainMu _ typesClean _ _
  · intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    apply node
    intro child inside
    have same := List.mem_singleton.mp inside
    subst child
    exact typeNode_plainMu original.2
  · apply node_rows
    intro row member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact component_plainMu _ typesClean _ _

private theorem without_clean (ctx : Context) (clean : CleanContext ctx) (names : List String) :
    PlainMu top (without ctx names) := by
  apply node_entries
  intro entry member
  exact clean.components entry (List.mem_filter.mp member).1

/-- Each actual query argument row retains a rigid type annotation. -/
theorem context_argument_plainMu (lib : Library) (query : Query) (entry : String × Row)
    (member : entry ∈ (context lib query).argumentEdges) : PlainMu top (.node [entry.2]) :=
  (context_clean lib query).arguments entry member

private theorem selected_components (ctx : Context) (clean : CleanContext ctx)
    (select : String × Row → Bool) :
    PlainMu top (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply node_entries
  intro entry member
  exact clean.components entry (List.mem_filter.mp member).1

private theorem termsRows_clean (ctx : Context) (clean : CleanContext ctx) (size : Nat) :
    ∀ asArgument row, row ∈ termsRows ctx asArgument size → PlainMu top row := by
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
                · exact node_entries top _ clean.arguments
                · exact node_entries top _ clean.components
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
                        apply application_plainMu _ _ _ clean.types
                        · exact selected_components ctx clean _
                        · apply union
                          intro child inside
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                          rcases inside with rfl | rfl | rfl
                          · exact without_clean ctx clean excluded
                          · exact node_entries top _ clean.arguments
                          · exact clean.argumentOnly
                  · have same := List.mem_singleton.mp ordinary
                    subst row
                    apply application_plainMu _ _ _ clean.types
                    · apply union
                      intro child inside
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                      rcases inside with rfl | rfl
                      · exact without_clean ctx clean _
                      · exact node_entries top _ clean.arguments
                    · exact union top _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _, rfl⟩ := List.mem_map.mp member
                  apply application_plainMu _ _ _ clean.types
                  · exact union top _ (ih split.val split.property.2 false)
                  · apply union
                    exact ih _ (by have positive := split.property.1; omega) true

/-- Every actual terms-table row derives clean Mu bodies from original library/query data. -/
theorem termsRows_plainMu (lib : Library) (query : Query) (asArgument : Bool) (size : Nat)
    (row : Expression) (member : row ∈ termsRows (context lib query) asArgument size) : PlainMu top row :=
  termsRows_clean _ (context_clean lib query) size asArgument row member

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

private theorem relevantRows_clean (ctx : Context) (clean : CleanContext ctx) (size : Nat) :
    ∀ asArgument names rows, relevantRows ctx asArgument size names = .ok rows →
      ∀ row ∈ rows, PlainMu top row := by
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
          have argumentsClean : ∀ entry ∈ arguments, PlainMu top (.node [entry.2]) :=
            SourceSynthesisSelectionOrigins.resolveSelection_preserves
              (fun entry => PlainMu top (.node [entry.2])) ctx.argumentEdges names arguments
              clean.arguments resolved
          split at computed
          · have same := Except.ok.inj computed
            subst rows
            exact termsRows_clean ctx clean size asArgument
          · have same := Except.ok.inj computed
            subst rows
            intro row member
            have same := List.mem_singleton.mp member
            subst row
            exact argumentsClean _ List.mem_cons_self
          · split at computed
            · have same := Except.ok.inj computed
              subst rows
              intro row member
              cases member
            · obtain ⟨chunks, chunksResult, flattened⟩ := bind_ok _ _ _ computed
              have same := Except.ok.inj flattened
              subst rows
              have chunksClean : ∀ chunk ∈ chunks, ∀ row ∈ chunk, PlainMu top row := by
                apply mapM_preserves (fun chunk => ∀ row ∈ chunk, PlainMu top row) _ _ _ _ chunksResult
                intro split choices choicesResult
                apply mapM_preserves (PlainMu top) _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, functionResult, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, argumentResult, completed⟩ := bind_ok _ _ _ argumentStep
                have same := Except.ok.inj completed
                subst expression
                apply application_plainMu _ _ _ clean.types
                · exact union top _ (ih split.val split.property.2 false _ function functionResult)
                · exact union top _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument argumentResult)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact chunksClean chunk included row inside

/-- A successful actual relevant-table lookup retains clean Mu bodies in every row. -/
theorem relevantRows_plainMu (lib : Library) (query : Query) (asArgument : Bool) (size : Nat)
    (names : List String) (rows : List Expression)
    (returned : relevantRows (context lib query) asArgument size names = .ok rows) :
    ∀ row ∈ rows, PlainMu top row :=
  relevantRows_clean _ (context_clean lib query) size asArgument names rows returned

/-- A successful original FirstOrder constructor has only top guards in every Mu body. -/
theorem firstOrderRaw_plainMu (lib : Library) (query : Query) (size : Int) (expression : Expression)
    (returned : firstOrderRaw lib query size = .ok expression) : PlainMu top expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    have same := Except.ok.inj completed
    subst expression
    apply ofType_plainMu
    · apply union
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have chunksClean : ∀ chunk ∈ chunks, ∀ row ∈ chunk, PlainMu top row := by
        apply mapM_preserves (fun chunk => ∀ row ∈ chunk, PlainMu top row) _ _ _ _ chunksResult
        intro arguments rows result
        exact relevantRows_clean _ (context_clean lib query) size.toNat true _ rows result
      exact chunksClean chunk included row inside
    · exact typeNode_plainMu query.queryGoal

/-- The constructor keeps its actual error; each successful instruction has clean Mu bodies. -/
theorem firstOrderRaw_result (lib : Library) (query : Query) (size : Int) :
    match firstOrderRaw lib query size with
    | .error _ => True
    | .ok expression => PlainMu top expression := by
  cases returned : firstOrderRaw lib query size with
  | error error => trivial
  | ok expression => exact firstOrderRaw_plainMu lib query size expression returned

end MicroCFTA.SourceSynthesisRecursiveOrigins
