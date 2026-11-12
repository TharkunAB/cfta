import MicroCFTA.SourceSynthesisCurrentConstruction
import MicroCFTA.SourceSynthesisOriginalGuardAlphabet
import MicroCFTA.SourceSynthesisRecursiveOrigins

/-!
# Complete guards and Mu bodies in current source construction

The library view encodes each scheme once. It preserves all other input fields.
The current factory supplies every table invariant. The proofs retain arbitrary
avoid rules and canonical query payloads. They do not identify the current
universe with a historical universe. Native construction and Room are separate.
-/
namespace MicroCFTA.SourceSynthesisCurrentSourceGuards
open InternedNestedConstruction (Syntax EdgeSyntax)
open SourceSynthesisTypeSyntax (Ty Library Query typeNode allTypes arrowMarker)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard equalityClasses generalize)
open SourceSynthesisFirstOrderConstruction (Expression Row Context component application ofType
  termsRows relevantRows resolveArguments)
open SourceSynthesisPr210TypeReflection (encodeTy)
open SourceSynthesisOriginalGuardAlphabet (alphabet applicationGuard filterGuard)
open SourceSynthesisRecursiveOrigins (PlainMu)
open SourceEqualityConstraintOrigins (guards childGuards edgeGuards)

/-- Encode each library scheme once and retain the remaining source fields. -/
def encodedLibrary (lib : Library) : Library :=
  { lib with
    libraryGroups := lib.libraryGroups.map fun entry =>
      (entry.1, encodeTy entry.2.1, entry.2.2)
    libraryArgumentOnly := lib.libraryArgumentOnly.map fun entry =>
      (entry.1, encodeTy entry.2) }

private def Good (lib : Library) (expression : Expression) : Prop :=
  (∀ guard ∈ guards expression, guard ∈ alphabet (encodedLibrary lib)) ∧
    PlainMu top expression

private def GoodRow (lib : Library) : Row → Prop
  | .mk _ guard children =>
      guard ∈ alphabet (encodedLibrary lib) ∧ ∀ child ∈ children, Good lib child

private theorem top_mem (lib : Library) : top ∈ alphabet (encodedLibrary lib) :=
  List.mem_cons_self

private theorem application_mem (lib : Library) :
    applicationGuard ∈ alphabet (encodedLibrary lib) :=
  List.mem_cons_of_mem _ List.mem_cons_self

private theorem filter_mem (lib : Library) : filterGuard ∈ alphabet (encodedLibrary lib) :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem union_good (lib : Library) (children : List Expression)
    (checked : ∀ child ∈ children, Good lib child) : Good lib (.union children) := by
  constructor
  · induction children with
    | nil => intro guard member; cases member
    | cons first rest ih =>
        intro guard member
        rcases List.mem_append.mp member with own | later
        · exact (checked first List.mem_cons_self).1 guard own
        · exact ih (fun child included => checked child (List.mem_cons_of_mem _ included)) guard later
  · exact SourceSynthesisRecursiveOrigins.union top children
      (fun child included => (checked child included).2)

private theorem node_good (lib : Library) (rows : List Row)
    (checked : ∀ row ∈ rows, GoodRow lib row) : Good lib (.node rows) := by
  induction rows with
  | nil =>
      constructor
      · intro guard member
        cases member
      · trivial
  | cons row rest ih =>
      cases row with
      | mk name own children =>
          have fields := checked _ List.mem_cons_self
          have tail := ih (fun row included => checked row (List.mem_cons_of_mem _ included))
          have childrenGood := union_good lib children fields.2
          refine ⟨?_, childrenGood.2, tail.2⟩
          intro guard member
          rcases List.mem_cons.mp member with same | inside
          · subst guard; exact fields.1
          · rcases List.mem_append.mp inside with child | later
            · exact childrenGood.1 guard child
            · exact tail.1 guard later

private theorem type_good (lib : Library) (typ : Ty) : Good lib (typeNode top typ) := by
  constructor
  · intro guard member
    rw [SourceSynthesisTypeSyntax.typeNode_guards top typ guard member]
    exact top_mem lib
  · exact SourceSynthesisRecursiveOrigins.typeNode_plainMu typ

private theorem types_good (lib : Library) (catalog : List (String × Nat)) :
    Good lib (allTypes top catalog) := by
  constructor
  · intro guard member
    rw [SourceSynthesisTypeSyntax.allTypes_guards top catalog guard member]
    exact top_mem lib
  · exact SourceSynthesisRecursiveOrigins.allTypes_plainMu catalog

private theorem component_good (lib : Library) (types : Expression) (checked : Good lib types)
    (name : String) (typ : Ty)
    (own : eqGuard (equalityClasses typ) ∈ alphabet (encodedLibrary lib)) :
    GoodRow lib (component types name typ) := by
  refine ⟨top_mem lib, ?_⟩
  intro child member
  cases List.mem_singleton.mp member
  constructor
  · intro guard included
    rcases SourceSynthesisGeneralizeSyntax.generalize_guards types typ guard included with
      same | trivial | inherited
    · subst guard; exact own
    · subst guard; exact top_mem lib
    · exact checked.1 guard inherited
  · exact SourceSynthesisRecursiveOrigins.generalize_plainMu types checked.2 typ

private theorem marker_good (lib : Library) : Good lib (arrowMarker top) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  exact ⟨top_mem lib, by intro child absent; cases absent⟩

private theorem application_good (lib : Library) (types function argument : Expression)
    (typesGood : Good lib types) (first : Good lib function) (second : Good lib argument) :
    Good lib (application types function argument) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  refine ⟨application_mem lib, ?_⟩
  intro child included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl | rfl | rfl
  · exact typesGood
  · exact marker_good lib
  · exact first
  · exact second

private theorem filter_good (lib : Library) (candidates goal : Expression)
    (programs : Good lib candidates) (annotation : Good lib goal) :
    Good lib (ofType candidates goal) := by
  apply node_good
  intro row member
  cases List.mem_singleton.mp member
  refine ⟨filter_mem lib, ?_⟩
  intro child included
  simp only [List.mem_cons, List.not_mem_nil, or_false] at included
  rcases included with rfl | rfl
  · exact annotation
  · exact programs

private theorem group_mem (lib : Library) (entry : String × Ty × List String)
    (member : entry ∈ lib.libraryGroups) :
    eqGuard (equalityClasses (encodeTy entry.2.1)) ∈ alphabet (encodedLibrary lib) := by
  simp only [alphabet, encodedLibrary, List.map_map, Function.comp_def]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))))

private theorem argumentOnly_mem (lib : Library) (entry : String × Ty)
    (member : entry ∈ lib.libraryArgumentOnly) :
    eqGuard (equalityClasses (encodeTy entry.2)) ∈ alphabet (encodedLibrary lib) := by
  simp only [alphabet, encodedLibrary, List.map_map, Function.comp_def]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_right _ (List.mem_map.mpr ⟨entry, member, rfl⟩))))

private structure ContextGood (lib : Library) (ctx : Context) : Prop where
  types : Good lib ctx.types
  components : ∀ entry ∈ ctx.components, GoodRow lib entry.2
  arguments : ∀ entry ∈ ctx.argumentEdges, GoodRow lib entry.2
  argumentOnly : Good lib ctx.argumentOnly

private theorem context_good (lib : Library) (query : Query) :
    ContextGood lib (SourceSynthesisCurrentContext.context lib query) := by
  have typesGood := types_good lib (SourceSynthesisCurrentContext.constructorCatalog lib query)
  refine ⟨typesGood, ?_, ?_, ?_⟩
  · intro entry member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact component_good lib _ typesGood _ _ (group_mem lib source included)
  · intro entry member
    obtain ⟨source, _included, rfl⟩ := List.mem_map.mp member
    refine ⟨top_mem lib, ?_⟩
    intro child inside
    cases List.mem_singleton.mp inside
    exact type_good lib (encodeTy source.2)
  · apply node_good
    intro row member
    obtain ⟨source, included, rfl⟩ := List.mem_map.mp member
    exact component_good lib _ typesGood _ _ (argumentOnly_mem lib source included)

private theorem entries_good (lib : Library) (entries : List (String × Row))
    (checked : ∀ entry ∈ entries, GoodRow lib entry.2) :
    Good lib (.node (entries.map Prod.snd)) := by
  apply node_good
  intro row member
  obtain ⟨entry, included, rfl⟩ := List.mem_map.mp member
  exact checked entry included

private theorem selected_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx)
    (select : String × Row → Bool) :
    Good lib (.node ((ctx.components.filter select).map Prod.snd)) := by
  apply entries_good
  intro entry member
  exact checked.components entry (List.mem_filter.mp member).1

private theorem terms_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx)
    (size : Nat) : ∀ flag row, row ∈ termsRows ctx flag size → Good lib row := by
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
                · exact entries_good lib _ checked.arguments
                · exact entries_good lib _ checked.components
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
                        apply application_good lib _ _ _ checked.types
                        · exact selected_good lib ctx checked _
                        · apply union_good
                          intro child included
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at included
                          rcases included with rfl | rfl | rfl
                          · exact selected_good lib ctx checked _
                          · exact entries_good lib _ checked.arguments
                          · exact checked.argumentOnly
                  · cases List.mem_singleton.mp ordinary
                    apply application_good lib _ _ _ checked.types
                    · apply union_good
                      intro child included
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
                      rcases included with rfl | rfl
                      · exact selected_good lib ctx checked _
                      · exact entries_good lib _ checked.arguments
                    · exact union_good lib _ (ih 1 (by decide) true)
              | succ rest =>
                  rw [termsRows] at member
                  obtain ⟨split, _, rfl⟩ := List.mem_map.mp member
                  apply application_good lib _ _ _ checked.types
                  · exact union_good lib _ (ih split.val split.property.2 false)
                  · exact union_good lib _ (ih _ (by have positive := split.property.1; omega) true)

private theorem bind_ok {Error Input Output : Type} (action : Except Error Input)
    (next : Input → Except Error Output) (value : Output)
    (returned : (action >>= next) = .ok value) :
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

private theorem relevant_good (lib : Library) (ctx : Context) (checked : ContextGood lib ctx)
    (size : Nat) : ∀ flag names rows, relevantRows ctx flag size names = .ok rows →
      ∀ row ∈ rows, Good lib row := by
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
            (fun entry => GoodRow lib entry.2) ctx.argumentEdges names arguments checked.arguments resolved
          split at computed
          · cases Except.ok.inj computed
            exact terms_good lib ctx checked size flag
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
              have goodChunks : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good lib row := by
                apply mapM_good (fun chunk => ∀ row ∈ chunk, Good lib row) _ _ _ _ chunkResult
                intro split choices choicesResult
                apply mapM_good (Good lib) _ _ _ _ choicesResult
                intro offset expression expressionResult
                obtain ⟨function, first, argumentStep⟩ := bind_ok _ _ _ expressionResult
                obtain ⟨argument, second, completed⟩ := bind_ok _ _ _ argumentStep
                cases Except.ok.inj completed
                apply application_good lib _ _ _ checked.types
                · exact union_good lib _ (ih split.val split.property.2 false _ function first)
                · exact union_good lib _ (ih _ (by have positive := split.property.1; omega)
                    true _ argument second)
              intro row member
              obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
              exact goodChunks chunk included row inside

/-- Actual current output derives its complete literal alphabet and clean Mu bodies. -/
theorem firstOrderRaw_guards_plainMu (lib : Library) (query : Query) (signed : Int)
    (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression) :
    (∀ guard ∈ guards expression, guard ∈ alphabet (encodedLibrary lib)) ∧ PlainMu top expression := by
  change Good lib expression
  unfold SourceSynthesisCurrentConstruction.firstOrderRaw at returned
  split at returned
  · cases returned
  · obtain ⟨chunks, chunksResult, completed⟩ := bind_ok _ _ _ returned
    cases Except.ok.inj completed
    apply filter_good
    · apply union_good
      intro row member
      obtain ⟨chunk, included, inside⟩ := List.mem_flatten.mp member
      have goodChunks : ∀ chunk ∈ chunks, ∀ row ∈ chunk, Good lib row := by
        apply mapM_good (fun chunk => ∀ row ∈ chunk, Good lib row) _ _ _ _ chunksResult
        intro arguments rows result
        exact relevant_good lib _ (context_good lib query) signed.toNat true _ rows result
      exact goodChunks chunk included row inside
    · exact type_good lib (encodeTy query.queryGoal)

mutual
private theorem mapped_inventory {Symbol : Type} (literal : String → Symbol) (expression : Expression) :
    guards (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression) = guards expression := by
  cases expression with
  | empty | var => rfl
  | node rows => simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_rows literal rows]
  | union members =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_children literal members]
  | binder smart body =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapSyntax, guards, mapped_inventory literal body]
termination_by sizeOf expression

private theorem mapped_children {Symbol : Type} (literal : String → Symbol) (expressions : List Expression) :
    childGuards (SourceSynthesisProgramBuildRolesGeneric.mapChildren literal expressions) = childGuards expressions := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
      simp only [SourceSynthesisProgramBuildRolesGeneric.mapChildren, childGuards,
        mapped_inventory literal first, mapped_children literal rest]
termination_by sizeOf expressions

private theorem mapped_rows {Symbol : Type} (literal : String → Symbol) (rows : List Row) :
    edgeGuards (SourceSynthesisProgramBuildRolesGeneric.mapEdges literal rows) = edgeGuards rows := by
  cases rows with
  | nil => rfl
  | cons row rest =>
      cases row with
      | mk name guard children =>
          simp only [SourceSynthesisProgramBuildRolesGeneric.mapEdges, edgeGuards,
            mapped_children literal children, mapped_rows literal rest]
termination_by sizeOf rows
end

/-- Any symbol adapter retains the complete alphabet of the same current output. -/
theorem mapped_guards {Symbol : Type} (literal : String → Symbol)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression) :
    ∀ guard ∈ guards (SourceSynthesisProgramBuildRolesGeneric.mapSyntax literal expression),
      guard ∈ alphabet (encodedLibrary lib) := by
  rw [mapped_inventory]
  exact (firstOrderRaw_guards_plainMu lib query signed expression returned).1

end MicroCFTA.SourceSynthesisCurrentSourceGuards
