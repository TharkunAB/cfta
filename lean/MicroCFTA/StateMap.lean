import MicroCFTA.Language

/-!
# State renaming and deliberate state merging

`Data.CFTA.mapStates` merges rows whose names become equal. It cannot remove
an original run. It preserves the exact language when the renaming is
injective. A non-injective renaming can add accepted terms.
-/
namespace MicroCFTA.StateMap
open Language

/-- Rename only child state identities, retaining symbols and guards. -/
def edge (rename : State → Other) (original : Edge State Symbol) : Edge Other Symbol :=
  ⟨original.label, original.children.map rename, original.guard⟩

/-- Gather all source rows whose names map to the requested output name. -/
def graph [DecidableEq Other] (states : List State) (automaton : Automaton State Symbol)
    (rename : State → Other) : Automaton Other Symbol := fun target =>
  states.flatMap fun state => if rename state = target then (automaton state).map (edge rename) else []

/-- Every renamed alternative comes from one complete source alternative. -/
theorem edge_exact [DecidableEq Other] (states : List State) (automaton : Automaton State Symbol)
    (rename : State → Other) (target : Other) (result : Edge Other Symbol) :
    result ∈ graph states automaton rename target ↔
      ∃ source ∈ states, rename source = target ∧ ∃ original ∈ automaton source, result = edge rename original := by
  simp only [graph, List.mem_flatMap]
  constructor
  · rintro ⟨source, member, present⟩
    split at present
    · next same =>
      obtain ⟨original, present, equal⟩ := List.mem_map.mp present
      exact ⟨source, member, same, original, present, equal.symm⟩
    · simp at present
  · rintro ⟨source, member, same, original, present, rfl⟩
    refine ⟨source, member, ?_⟩
    rw [ite_eq_left same]
    exact List.mem_map.mpr ⟨original, present, rfl⟩

/-- State merging retains every original complete accepting run. -/
theorem map_complete [DecidableEq Other] (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (rename : State → Other)
    {state : State} {term : Term Symbol} (accepted : Accepts automaton state term) :
    Accepts (graph states automaton rename) (rename state) term := by
  induction accepted using Accepts.rec
    (motive_2 := fun childStates terms _ =>
      All₂ (Accepts (graph states automaton rename)) (childStates.map rename) terms) with
  | @node state original terms present runs guard ih =>
    exact .node (edge rename original) terms
      ((edge_exact states automaton rename (rename state) _).mpr
        ⟨state, complete state, rfl, original, present, rfl⟩) ih guard
  | nil => exact .nil
  | cons head tail ih ihtail => exact .cons ih ihtail

/-- A relation on renamed child states can be read on the original child list. -/
theorem all₂_unmap (rename : State → Other) (relation : Other → Value → Prop)
    (states : List State) (values : List Value) (runs : All₂ relation (states.map rename) values) :
    All₂ (fun state value => relation (rename state) value) states values := by
  induction states generalizing values with
  | nil => cases runs; exact .nil
  | cons state rest ih => cases runs with
    | cons head tail => exact .cons head (ih _ tail)

/-- Injective renaming cannot construct a run from unrelated source states. -/
theorem map_sound [DecidableEq Other] (states : List State) (automaton : Automaton State Symbol)
    (rename : State → Other) (injective : ∀ a b, rename a = rename b → a = b)
    {target : Other} {term : Term Symbol} (accepted : Accepts (graph states automaton rename) target term) :
    ∀ source, rename source = target → Accepts automaton source term := by
  induction accepted using Accepts.rec
    (motive_2 := fun childStates terms _ =>
      All₂ (fun target term => ∀ source, rename source = target → Accepts automaton source term) childStates terms) with
  | @node target result terms member runs guard ih =>
    intro source same
    obtain ⟨owner, _, renamed, original, present, equal⟩ :=
      (edge_exact states automaton rename target result).mp member
    have ownerEq := injective owner source (renamed.trans same.symm)
    subst owner
    subst result
    have children := all₂_unmap rename _ original.children terms ih
    exact .node original terms present (children.imp (fun _ _ child => child _ rfl)) guard
  | nil => exact .nil
  | cons head tail ih ihtail => exact .cons ih ihtail

/-- An injective public state rename preserves all and only the original terms. -/
theorem map_exact [DecidableEq Other] (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (rename : State → Other)
    (injective : ∀ a b, rename a = rename b → a = b) (state : State) (term : Term Symbol) :
    Accepts (graph states automaton rename) (rename state) term ↔ Accepts automaton state term :=
  ⟨fun accepted => map_sound states automaton rename injective accepted state rfl,
    map_complete states complete automaton rename⟩

/-- Two states with different root constructors before merging. -/
def separate : Automaton Bool Nat
  | false => [⟨0, [true], fun _ => true⟩]
  | true => [⟨1, [], fun _ => true⟩]

/-- The documented state-merging behavior can enlarge the root language. -/
theorem merging_can_add_terms :
    Accepts (graph [false, true] separate (fun _ => ())) () (.node 1 []) ∧
      ¬Accepts separate false (.node 1 []) := by
  constructor
  · exact .node ⟨1, [], fun _ => true⟩ [] (by simp [graph, separate, edge]) .nil rfl
  · rw [accepts_node_iff]
    simp [separate]

end MicroCFTA.StateMap
