import MicroCFTA.SourceEqualityOpenOrdinaryHead
import MicroCFTA.SourceCurrentSecondaryTrace
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Current secondary gate effects and replay above completed caches

Actual gate traces preserve semantic readiness and both constructor histories.
Single stored unfolding supplies these effects without a cost-heap premise.
Each completed trace replays with the same Boolean and no constructor effect
in a cache that retains its final heap. The replay target need not retain
the initial gate schedule. Projection completion remains a separate result.
-/
namespace MicroCFTA.SourceCurrentSecondaryReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceCurrentSecondaryTrace EqualityNormalize
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache

/-- A completed node gate retains semantic heaps and replays exactly above its completed final heap. -/
theorem node_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : Path) (value : Value Symbol Guard) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (trace : NodeTrace unconstrained path value before answer after)
    (semantic : SemanticReady before) (available : Available before value) :
    SemanticReady after ∧ Keeps before after ∧
      ∀ target, Grows after target → NodeTrace unconstrained path value target answer target := by
  revert available semantic
  induction trace using NodeTrace.rec
      (motive_2 := fun values index path before answer after _ => SemanticReady before →
        (∀ value ∈ values, Available before value) → SemanticReady after ∧ Keeps before after ∧
          ∀ target, Grows after target → ChildTrace unconstrained values index path target answer target)
      (motive_3 := fun index path edges before answer after _ => SemanticReady before →
        (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
          SemanticReady after ∧ Keeps before after ∧
            ∀ target, Grows after target → EdgesTrace unconstrained index path edges target answer target) with
  | empty => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .empty⟩
  | reference => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .reference⟩
  | union members => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .union members⟩
  | finite fast => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .finite fast⟩
  | endpoint slow => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .endpoint slow⟩
  | branches slow trace ih =>
      intro semantic available
      obtain ⟨finalSemantic, kept, replay⟩ := ih semantic (fun value member => available.children value member)
      exact ⟨finalSemantic, kept, fun target grows => .branches slow (replay target grows)⟩
  | constrained blocked => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .constrained blocked⟩
  | closed plain closed => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .closed plain closed⟩
  | unfold plain opened actual trace ih =>
      intro semantic available
      obtain ⟨result, middle, done, first, middleSemantic, resultAvailable, _⟩ :=
        SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
      obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
      cases sameValue
      cases sameState
      obtain ⟨finalSemantic, kept, replay⟩ := ih middleSemantic resultAvailable
      refine ⟨finalSemantic, first.trans kept, ?_⟩
      intro target retained
      exact .unfold plain opened
        (InternedFreshOrdinaryStoredSubstitution.unfold_replay _ _ target _ _
          semantic.ready.semantic.1.normal.facts.coherent.valid actual (grows_trans kept.growth retained))
        (replay target retained)
  | missing absent semantic _ => exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .missing absent⟩
  | present found trace ih semantic available =>
      obtain ⟨finalSemantic, kept, replay⟩ := ih semantic (available _ (List.mem_of_getElem? found))
      exact ⟨finalSemantic, kept, fun target retained => .present found (replay target retained)⟩
  | nil semantic _ => exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .nil⟩
  | stop head ih semantic available =>
      obtain ⟨finalSemantic, kept, replay⟩ := ih semantic (fun value member => available value (by simp [member]))
      exact ⟨finalSemantic, kept, fun target grows => .stop (replay target grows)⟩
  | next head tail headIH tailIH semantic available =>
      obtain ⟨middleSemantic, first, firstReplay⟩ := headIH semantic
        (fun value member => available value (by simp [member]))
      obtain ⟨finalSemantic, kept, replay⟩ := tailIH middleSemantic
        (fun value member => first.available value (available value (by simp [member])))
      exact ⟨finalSemantic, first.trans kept,
        fun target retained => .next (firstReplay target (grows_trans kept.growth retained)) (replay target retained)⟩

/-- A completed child lookup retains semantic readiness and exact warm replay. -/
theorem child_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (index : Nat) (path : Path)
    (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (trace : ChildTrace unconstrained values index path before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value) :
    SemanticReady after ∧ Keeps before after ∧
      ∀ target, Grows after target → ChildTrace unconstrained values index path target answer target := by
  cases trace with
  | missing absent => exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .missing absent⟩
  | present found trace =>
      obtain ⟨finalSemantic, kept, replay⟩ := node_replay _ _ _ _ _ _ trace semantic
        (available _ (List.mem_of_getElem? found))
      exact ⟨finalSemantic, kept, fun target retained => .present found (replay target retained)⟩

/-- Ordered edge gates retain each actual returned heap and replay above their completed final heap. -/
theorem edges_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (index : Nat) (path : Path) (edges : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (trace : EdgesTrace unconstrained index path edges before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available before value) :
    SemanticReady after ∧ Keeps before after ∧
      ∀ target, Grows after target → EdgesTrace unconstrained index path edges target answer target := by
  induction edges generalizing before answer after with
  | nil => cases trace; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .nil⟩
  | cons edge edges ih =>
      cases trace with
      | stop head =>
          obtain ⟨finalSemantic, kept, replay⟩ := child_replay _ _ _ _ _ _ _ head semantic
            (fun value member => available value (by simp [member]))
          exact ⟨finalSemantic, kept, fun target retained => .stop (replay target retained)⟩
      | next head tail =>
          obtain ⟨middleSemantic, first, firstReplay⟩ := child_replay _ _ _ _ _ _ _ head semantic
            (fun value member => available value (by simp [member]))
          obtain ⟨finalSemantic, kept, replay⟩ := ih _ _ _ tail middleSemantic
            (fun value member => first.available value (available value (by simp [member])))
          exact ⟨finalSemantic, first.trans kept,
            fun target retained => .next (firstReplay target (grows_trans kept.growth retained)) (replay target retained)⟩

/-- A complete forest path retains semantic readiness and has an exact replay above its final heap. -/
theorem path_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (path : Path) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (trace : PathTrace unconstrained values path before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value) :
    SemanticReady after ∧ Keeps before after ∧
      ∀ target, Grows after target → PathTrace unconstrained values path target answer target := by
  cases trace with
  | empty => exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .empty⟩
  | child trace =>
      cases trace with
      | missing absent => exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .child (.missing absent)⟩
      | present found trace =>
          obtain ⟨finalSemantic, kept, replay⟩ := node_replay _ _ _ _ _ _ trace semantic
            (available _ (List.mem_of_getElem? found))
          exact ⟨finalSemantic, kept, fun target retained => .child (.present found (replay target retained))⟩

/-- A complete class preserves semantic heaps and replays its ordered answer without a cost heap. -/
theorem class_replay [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard)
    (trace : ClassTrace unconstrained values paths before answer after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value) :
    SemanticReady after ∧ Keeps before after ∧
      ∀ target, Grows after target → ClassTrace unconstrained values paths target answer target := by
  revert available semantic
  induction trace with
  | nil => intro semantic _; exact ⟨semantic, pure_keeps _ semantic.ready, fun _ _ => .nil⟩
  | stop head =>
      intro semantic available
      obtain ⟨finalSemantic, kept, replay⟩ := path_replay _ _ _ _ _ _ head semantic available
      exact ⟨finalSemantic, kept, fun target retained => .stop (replay target retained)⟩
  | next head tail ih =>
      intro semantic available
      obtain ⟨middleSemantic, first, firstReplay⟩ := path_replay _ _ _ _ _ _ head semantic available
      obtain ⟨finalSemantic, kept, replay⟩ := ih middleSemantic
        (fun value member => first.available value (available value member))
      exact ⟨finalSemantic, first.trans kept,
        fun target retained => .next (firstReplay target (grows_trans kept.growth retained)) (replay target retained)⟩

/-- Every original row of a false edge scan retains its false child certificate in later caches. -/
theorem false_edges_members [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (index : Nat) (path : Path) (edges : List (EdgeValue Symbol Guard)) (before after : State Symbol Guard)
    (trace : EdgesTrace unconstrained index path edges before false after)
    (semantic : SemanticReady before) (available : ∀ value ∈ edges.flatMap EdgeValue.children, Available before value)
    (target : State Symbol Guard) (retained : Grows after target) :
    ∀ edge ∈ edges, ChildTrace unconstrained edge.children index path target false target := by
  induction edges generalizing before with
  | nil => intro edge member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := child_replay _ _ _ _ _ _ _ head semantic
            (fun value member => available value (by simp [member]))
          have tailAvailable : ∀ value ∈ rest.flatMap EdgeValue.children, Available _ value :=
            fun value member => firstEffects.2.1.available value (available value (by simp [member]))
          have tailEffects := edges_replay _ _ _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro edge member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable edge member

/-- A selected original child retains the exact false node certificate of its completed lookup. -/
theorem false_selected [DecidableEq (EdgeKey Symbol Guard)]
    {unconstrained : Value Symbol Guard → Bool} {values : List (Value Symbol Guard)} {index : Nat} {path : Path}
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : ChildTrace unconstrained values index path before false after) (found : values[index]? = some value) :
    NodeTrace unconstrained path value before false after := by
  cases trace with
  | missing absent => rw [absent] at found; cases found
  | present selected node =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      exact node

/-- Every path of a false class retains its own false certificate in every later extending cache. -/
theorem false_class_paths [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (paths : Class) (before after : State Symbol Guard)
    (trace : ClassTrace unconstrained values paths before false after)
    (semantic : SemanticReady before) (available : ∀ value ∈ values, Available before value)
    (target : State Symbol Guard) (retained : Grows after target) :
    ∀ path ∈ paths, PathTrace unconstrained values path target false target := by
  induction paths generalizing before with
  | nil => intro path member; cases member
  | cons first rest ih =>
      cases trace with
      | next head tail =>
          have firstEffects := path_replay _ _ _ _ _ _ head semantic available
          have tailAvailable := fun value member => firstEffects.2.1.available value (available value member)
          have tailEffects := class_replay _ _ _ _ _ _ tail firstEffects.1 tailAvailable
          intro path member
          rcases List.mem_cons.mp member with rfl | member
          · exact firstEffects.2.2 target (grows_trans tailEffects.2.1.growth retained)
          · exact ih _ tail firstEffects.1 tailAvailable path member

end MicroCFTA.SourceCurrentSecondaryReplay
