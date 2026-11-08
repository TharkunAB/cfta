import MicroCFTA.SourceSynthesisUniverseCallerBoundary
import MicroCFTA.SourceSynthesisProgramRoles
import MicroCFTA.SourceEqualityOriginalAllocationPreparation
import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory

/-!
# Cached original guards from actual FirstOrder source construction

The source proof checks all literal guards, including guards in Type positions.
The Label adapter changes names and retains this exact inventory.
Preparation uses the actual serial allocator and its returned history.
Native allocation order and lazy demand remain separate.
-/
namespace MicroCFTA.SourceSynthesisOriginalGuardsCached
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisFirstOrderConstruction
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)
local notation "Cached" => SourceEqualityGuardReadback.Cached
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula

private def Good (expression : Expression) : Prop :=
  ∀ guard ∈ guards expression, Cached guard.equalities

private def GoodRow : Row → Prop
  | .mk _ guard children => Cached guard.equalities ∧ ∀ child ∈ children, Good child

private theorem eqGuard_cached (classes : List (List (List Nat))) :
    Cached (eqGuard classes).equalities := by
  rw [SourceSynthesisGeneralizeSyntax.eqGuard_eq_source]
  exact SourceEqualityGuardReadback.normalize_cached classes

private theorem children_good (expressions : List Expression)
    (checked : ∀ expression ∈ expressions, Good expression) :
    ∀ guard ∈ childGuards expressions, Cached guard.equalities := by
  induction expressions with
  | nil => intro guard member; cases member
  | cons first rest ih =>
      intro guard member
      rcases List.mem_append.mp member with head | tail
      · exact checked first List.mem_cons_self guard head
      · exact ih (fun expression included => checked expression (List.mem_cons_of_mem _ included)) guard tail

private theorem node_good (rows : List Row) (checked : ∀ row ∈ rows, GoodRow row) :
    Good (.node rows) := by
  induction rows with
  | nil => intro guard member; cases member
  | cons row rest ih =>
      cases row with
      | mk name guard children =>
          have own := checked _ List.mem_cons_self
          intro other member
          rcases List.mem_cons.mp member with rfl | tail
          · exact own.1
          · rcases List.mem_append.mp tail with child | later
            · exact children_good children own.2 other child
            · exact ih (fun row included => checked row (List.mem_cons_of_mem _ included)) other later

private theorem union_good (members : List Expression) (checked : ∀ member ∈ members, Good member) :
    Good (.union members) := children_good members checked

private theorem typeNode_good (typ : Ty) : Good (typeNode top typ) := by
  intro guard member
  rw [typeNode_guards top typ guard member]
  exact SourceEqualityConstraintConstructors.top_cached

private theorem types_good (lib : Library) (query : Query) : Good (typesOf lib query) := by
  intro guard member
  rw [allTypes_guards top (constructorCatalog lib query) guard member]
  exact SourceEqualityConstraintConstructors.top_cached

private theorem generalize_good (types : Expression) (checked : Good types) (typ : Ty) :
    Good (SourceSynthesisGeneralizeSyntax.generalize types typ) := by
  intro guard member
  rcases SourceSynthesisGeneralizeSyntax.generalize_guards types typ guard member with own | trivial | inherited
  · subst guard; exact eqGuard_cached _
  · subst guard; exact SourceEqualityConstraintConstructors.top_cached
  · exact checked guard inherited

private theorem component_good (types : Expression) (checked : Good types) (name : String) (typ : Ty) :
    GoodRow (component types name typ) := by
  refine ⟨SourceEqualityConstraintConstructors.top_cached, ?_⟩
  intro child member
  cases List.mem_singleton.mp member
  exact generalize_good types checked typ

private theorem marker_good : Good (arrowMarker (Guard := Guard) top) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  exact ⟨SourceEqualityConstraintConstructors.top_cached, by intro child included; cases included⟩

private theorem application_good (types function argument : Expression)
    (typesGood : Good types) (functionGood : Good function) (argumentGood : Good argument) :
    Good (application types function argument) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  refine ⟨eqGuard_cached _, ?_⟩
  intro child included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl | rfl | rfl
  · exact typesGood
  · exact marker_good
  · exact functionGood
  · exact argumentGood

private theorem filter_good (candidates goal : Expression) (candidatesGood : Good candidates) (goalGood : Good goal) :
    Good (ofType candidates goal) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  refine ⟨eqGuard_cached _, ?_⟩
  intro child included
  rcases List.mem_cons.mp included with rfl | rest
  · exact goalGood
  · cases List.mem_singleton.mp rest
    exact candidatesGood

private structure ContextGood (ctx : Context) : Prop where
  types : Good ctx.types
  components : ∀ entry ∈ ctx.components, GoodRow entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, GoodRow entry.2
  argumentOnly : Good ctx.argumentOnly

private theorem context_good (lib : Library) (query : Query) : ContextGood (context lib query) := by
  refine ⟨types_good lib query, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    exact component_good _ (types_good lib query) _ _
  · intro entry member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    refine ⟨SourceEqualityConstraintConstructors.top_cached, ?_⟩
    intro child included
    cases List.mem_singleton.mp included
    exact typeNode_good _
  · apply node_good
    intro row member
    obtain ⟨source, _, rfl⟩ := List.mem_map.mp member
    exact component_good _ (types_good lib query) _ _

private theorem entries_good (entries : List (String × Row)) (checked : ∀ entry ∈ entries, GoodRow entry.2) :
    Good (.node (entries.map Prod.snd)) := by
  apply node_good
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_good (ctx : Context) (checked : ContextGood ctx) (select : String × Row → Bool) :
    Good (.node ((ctx.components.filter select).map Prod.snd)) :=
  entries_good _ (fun entry member => checked.components entry (List.mem_filter.mp member).1)

private theorem terms_good (ctx : Context) (checked : ContextGood ctx) (size : Nat) :
    ∀ flag row, row ∈ termsRows ctx flag size → Good row := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro flag row member
      cases size with
      | zero => simp only [termsRows, List.not_mem_nil] at member
      | succ size =>
          cases size with
          | zero =>
              rw [termsRows] at member
              rcases List.mem_append.mp member with base | optional
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at base
                rcases base with rfl | rfl
                · exact entries_good _ checked.arguments
                · exact entries_good _ checked.components
              · cases flag with
                | false => cases optional
                | true => cases List.mem_singleton.mp optional; exact checked.argumentOnly
          | succ size =>
              cases size with
              | zero =>
                  rw [termsRows] at member
                  rcases List.mem_append.mp member with restricted | ordinary
                  · obtain ⟨⟨functions, arguments⟩, _, selected⟩ := List.mem_filterMap.mp restricted
                    cases arguments with
                    | none => cases selected
                    | some excluded =>
                        cases Option.some.inj selected
                        apply application_good _ _ _ checked.types
                        · exact selected_good ctx checked _
                        · apply union_good
                          intro child included
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at included
                          rcases included with rfl | rfl | rfl
                          · exact selected_good ctx checked _
                          · exact entries_good _ checked.arguments
                          · exact checked.argumentOnly
                  · cases List.mem_singleton.mp ordinary
                    apply application_good _ _ _ checked.types
                    · apply union_good
                      intro child included
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
                      rcases included with rfl | rfl
                      · exact selected_good ctx checked _
                      · exact entries_good _ checked.arguments
                    · exact union_good _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _, rfl⟩ := List.mem_map.mp member
                  apply application_good _ _ _ checked.types
                  · exact union_good _ (ih split.val split.property.2 false)
                  · exact union_good _ (ih _ (by have positive := split.property.1; omega) true)

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output) (returned : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error => cases returned
  | ok input => exact ⟨input, rfl, returned⟩

private theorem mapM_good {Error Input Output : Type} (P : Output → Prop)
    (action : Input → Except Error Output) (inputs : List Input) (outputs : List Output)
    (checked : ∀ input output, action input = .ok output → P output)
    (returned : inputs.mapM action = .ok outputs) : ∀ output ∈ outputs, P output := by
  have related := SymbolicDriver.mapM_success_all₂ action inputs outputs returned
  have certificates := related.imp (fun input output done => iff_of_true True.intro (checked input output done))
  exact (SymbolicDriver.all₂_forall_iff (fun _ => True) P inputs outputs certificates).mp (by simp)

private theorem relevant_good (ctx : Context) (checked : ContextGood ctx) (size : Nat) :
    ∀ flag names rows, relevantRows ctx flag size names = .ok rows → ∀ row ∈ rows, Good row := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro flag names rows returned
      rw [relevantRows] at returned
      cases resolved : resolveArguments ctx names with
      | none => simp only [resolved] at returned; cases returned
      | some arguments =>
          simp only [resolved] at returned
          obtain ⟨actual, same, computed⟩ := bind_ok _ _ _ returned
          cases Except.ok.inj same
          have argumentsGood := SourceSynthesisSelectionOrigins.resolveSelection_preserves
            (fun entry => GoodRow entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · cases Except.ok.inj computed
            exact terms_good ctx checked size flag
          · cases Except.ok.inj computed
            intro row member
            cases List.mem_singleton.mp member
            apply node_good
            intro edge included
            cases List.mem_singleton.mp included
            exact argumentsGood _ List.mem_cons_self
          · split at computed
            · cases Except.ok.inj computed
              intro row member; cases member
            · obtain ⟨chunks, chunkResult, flattened⟩ := bind_ok _ _ _ computed
              cases Except.ok.inj flattened
              have goodChunks : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good row := by
                apply mapM_good (fun chunk => ∀ row ∈ chunk, Good row) _ _ _ _ chunkResult
                intro split choices choicesResult
                apply mapM_good Good _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, first, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, second, completed⟩ := bind_ok _ _ _ argumentStep
                cases Except.ok.inj completed
                apply application_good _ _ _ checked.types
                · exact union_good _ (ih split.val split.property.2 false _ function first)
                · exact union_good _ (ih _ (by have positive := split.property.1; omega) true _ argument second)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact goodChunks chunk included row inside

private theorem firstOrder_good (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression) : Good expression := by
  unfold firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    cases Except.ok.inj completed
    apply filter_good
    · apply union_good
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have goodChunks : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good row := by
        apply mapM_good (fun chunk => ∀ row ∈ chunk, Good row) _ _ _ _ chunksResult
        intro arguments rows result
        exact relevant_good _ (context_good lib query) signed.toNat true _ rows result
      exact goodChunks chunk included row inside
    · exact typeNode_good _

mutual
private theorem ordinary_guards (expression : Expression) :
    guards (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) = guards expression := by
  cases expression with
  | empty | var => rfl
  | node rows =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, guards, ordinary_edgeGuards rows]
  | union members =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, guards, ordinary_childGuards members]
  | binder smart body =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinarySymbols, guards, ordinary_guards body]
termination_by sizeOf expression

private theorem ordinary_childGuards (expressions : List Expression) :
    childGuards (SourceSynthesisUniverseCallerBoundary.ordinaryChildren expressions) = childGuards expressions := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      simp only [SourceSynthesisUniverseCallerBoundary.ordinaryChildren, childGuards,
        ordinary_guards first, ordinary_childGuards rest]
termination_by sizeOf expressions

private theorem ordinary_edgeGuards (rows : List Row) :
    edgeGuards (SourceSynthesisUniverseCallerBoundary.ordinaryEdges rows) = edgeGuards rows := by
  cases rows with
  | nil => rfl
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [SourceSynthesisUniverseCallerBoundary.ordinaryEdges, edgeGuards,
            ordinary_childGuards children, ordinary_edgeGuards rest]
termination_by sizeOf rows
end

/-- Actual signed source success derives normalized payloads in every original Label guard. -/
theorem firstOrderRaw_guards_cached (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression) :
    ∀ guard ∈ guards (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression), Cached guard.equalities := by
  rw [ordinary_guards]
  exact firstOrder_good lib query signed expression returned

/-- The actual serial allocator derives all fields of the supplied actual original build. -/
theorem prepared_fields_of_build [DecidableEq (EdgeKey Symbol Guard)]
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : firstOrderRaw lib query signed = .ok expression)
    (initial : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid initial)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) [] empty = .done value heap) :
    ∃ fields cache,
      SourceEqualityOriginalAllocationPreparation.Receipt
        (guards (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression)) initial fields cache ∧
      SourceCurrentConjunctionEquality.Fields (SourceEqualityConstraintMemoAllocation.initial cache) heap := by
  obtain ⟨fields, cache, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete _
    initial valid (firstOrderRaw_guards_cached lib query signed expression returned)
  exact ⟨fields, cache, prepared, prepared.history.fields valid
    (SourceSynthesisUniverseCallerBoundary.ordinarySymbols expression) (fun _ member => member) value heap built⟩

end MicroCFTA.SourceSynthesisOriginalGuardsCached
