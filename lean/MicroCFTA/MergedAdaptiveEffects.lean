import MicroCFTA.MergedPhysicalGroupRoot

/-!
# State-dependent effects for recursive alternative merging

Each action selects its next computation in the actual current cache.
Failure records exhausted recursive fuel. The source correspondence proof
will derive a sufficient fuel bound from ordinary constructor height.
-/
namespace MicroCFTA.MergedAdaptiveEffects
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnionTransport
open MergedPhysicalGroupCalls Language

/-- A completed action returns its value and actual cache; none marks exhausted recursion. -/
abbrev Action (Symbol Guard Result : Type) := State Symbol Guard → Option (Result × State Symbol Guard)

/-- Return an existing value without cache effects. -/
def pure (value : Result) : Action Symbol Guard Result := fun state => some (value, state)

/-- Execute the next action at the exact cache returned by its predecessor. -/
def bind (first : Action Symbol Guard A) (next : A → Action Symbol Guard B) : Action Symbol Guard B :=
  fun state => (first state).bind fun result => next result.1 result.2

/-- Run an actual finite edge or node constructor computation. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result) : Action Symbol Guard Result :=
  fun state => some (run computation state)

/-- Sequence state-dependent requests in source order. -/
def map (call : Request → Action Symbol Guard Result) : List Request → Action Symbol Guard (List Result)
  | [] => pure []
  | first :: rest => bind (call first) fun value => bind (map call rest) fun values => pure (value :: values)

/-- All earlier available inputs and prepared reads remain usable in the actual result cache. -/
structure Extension [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (outputs : List (Value Symbol Guard)) : Prop where
  context : Context after outputs
  growth : Grows before after
  available : ∀ value, Available before value → Available after value

/-- No-effect branches preserve the complete prepared context. -/
theorem Extension.refl [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) : Extension state state outputs :=
  ⟨context, grows_refl state, fun _ available => available⟩

/-- Actual source state histories compose across adjacent action results. -/
theorem Extension.trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {outputs : List (Value Symbol Guard)}
    (first : Extension before middle outputs) (second : Extension middle after outputs) : Extension before after outputs :=
  ⟨second.context, grows_trans first.growth second.growth, fun value available => second.available value (first.available value available)⟩

/-- A finite constructor computation derives its effect certificate from its actual result context. -/
theorem Extension.work [DecidableEq (EdgeKey Symbol Guard)]
    (computation : Work Symbol Guard Result) (state : State Symbol Guard) (outputs : List (Value Symbol Guard))
    (before : Context state outputs) (after : Context (run computation state).2 outputs) :
    Extension state (run computation state).2 outputs :=
  ⟨after, (InternedConstructorTemplates.run_correct computation state before.facts.coherent.valid).2,
    fun _ available => available_after_run computation state before.facts.coherent.valid available⟩

/-- One child or column result retains the original operand languages at its actual final state. -/
structure Result [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (outputs : List (Value Symbol Guard))
    (meaning : Guard → Term Symbol → Bool) (inputs : List (Value Symbol Guard)) (value : Value Symbol Guard) : Prop where
  extension : Extension before after outputs
  available : Available after value
  covers : Covers before after meaning inputs value

/-- Sequential child actions derive the exact final cache and positionwise coverage. -/
theorem map_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Action Symbol Guard (Value Symbol Guard))
    (operands : Request → List (Value Symbol Guard)) (requests : List Request)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (complete : ∀ request ∈ requests, ∀ state, Context state outputs → Values state (operands request) →
      ∃ value after, call request state = some (value, after) ∧ Result state after outputs meaning (operands request) value)
    (state : State Symbol Guard) (context : Context state outputs)
    (inputs : ∀ request ∈ requests, Values state (operands request)) :
    ∃ values after, map call requests state = some (values, after) ∧ Extension state after outputs ∧ Values after values ∧
      All₂ (fun request value => Covers state after meaning (operands request) value) requests values := by
  induction requests generalizing state with
  | nil => exact ⟨[], state, rfl, .refl state outputs context, by simp [Values], .nil⟩
  | cons first rest ih =>
      obtain ⟨head, middle, firstDone, firstResult⟩ := complete first List.mem_cons_self state context (inputs first List.mem_cons_self)
      obtain ⟨tail, after, restDone, restExtension, restAvailable, restCovers⟩ :=
        ih (fun request member => complete request (List.mem_cons_of_mem _ member)) middle firstResult.extension.context
          (fun request member value included => firstResult.extension.available value
            (inputs request (List.mem_cons_of_mem _ member) value included))
      refine ⟨head :: tail, after, ?_, firstResult.extension.trans restExtension, ?_, .cons ?_ ?_⟩
      · simp only [map, bind, firstDone, restDone, Option.bind_some, pure]
      · intro value member
        rcases List.mem_cons.mp member with same | member
        · rw [same]; exact restExtension.available head firstResult.available
        · exact restAvailable value member
      · intro value member term accepted
        exact (accepts_stable middle after outputs firstResult.extension.context restExtension.growth meaning head firstResult.available term).mpr
          (firstResult.covers value member term accepted)
      · apply all₂_left_imp _ _ rest tail restCovers
        intro request original result covers value member term accepted
        exact covers value member term ((accepts_stable state middle outputs context firstResult.extension.growth meaning value
          (inputs request (List.mem_cons_of_mem _ original) value member) term).mpr accepted)

end MicroCFTA.MergedAdaptiveEffects
