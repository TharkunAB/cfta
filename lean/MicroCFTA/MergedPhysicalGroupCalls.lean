import MicroCFTA.MergedPhysicalUnion
import MicroCFTA.MergedMergeTermination
import MicroCFTA.MergedAlternativesGroups

/-!
# Sequential child calls of physical group construction

Each recursive call has a certificate for that child request. The list
worker threads the actual cache through all calls. Earlier result records
and their languages remain valid in the final cache.
-/
namespace MicroCFTA.MergedPhysicalGroupCalls
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance
open MergedPhysicalLanguage MergedPhysicalMergeContext MergedPhysicalUnionTransport
open Language

/-- One physical result includes every operand language from the call's initial cache. -/
def Covers [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (inputs : List (Value Symbol Guard))
    (result : Value Symbol Guard) : Prop :=
  ∀ value ∈ inputs, ∀ term, EpsilonUnion.Accepts (graph before meaning) value term →
    EpsilonUnion.Accepts (graph after meaning) result term

/-- Execute the specified child calls in order, retaining all constructor effects. -/
def mapCalls (call : Request → Work Symbol Guard Result) :
    List Request → Work Symbol Guard (List Result)
  | [] => .pure []
  | first :: rest => (call first).bind fun value =>
      (mapCalls call rest).bind fun values => .pure (value :: values)

/-- Sequential calls preserve the exact number and order of result positions. -/
theorem mapCalls_length [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Work Symbol Guard Result) (requests : List Request)
    (state : InternedConstructorTemplates.State Symbol Guard) :
    (run (mapCalls call requests) state).1.length = requests.length := by
  induction requests generalizing state with
  | nil => rfl
  | cons first rest ih => simp only [mapCalls, run_bind, run, List.length_cons, ih]

/-- Change a list relation using the original request's list membership. -/
theorem all₂_left_imp (before after : A → B → Prop) (left : List A) (right : List B)
    (related : All₂ before left right)
    (step : ∀ a ∈ left, ∀ b, before a b → after a b) : All₂ after left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (step _ List.mem_cons_self _ head)
        (ih (fun a member b => step a (List.mem_cons_of_mem _ member) b))

/-- Positionwise child coverage sends one accepted source row to the returned child row. -/
theorem covers_runs [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (meaning : Guard → Term Symbol → Bool) (operands : Request → List (Value Symbol Guard))
    (requests : List Request) (values : List (Value Symbol Guard)) (terms : List (Term Symbol))
    (covered : All₂ (fun request value => Covers before after meaning (operands request) value) requests values)
    (runs : All₂ (fun request term => ∃ value ∈ operands request,
      EpsilonUnion.Accepts (graph before meaning) value term) requests terms) :
    All₂ (EpsilonUnion.Accepts (graph after meaning)) values terms := by
  induction covered generalizing terms with
  | nil => cases runs; exact .nil
  | cons cover covers ih =>
      cases runs with
      | cons accepted rest =>
          obtain ⟨value, member, accepted⟩ := accepted
          exact .cons (cover value member _ accepted) (ih _ rest)

/-- Prepared available children keep their accepted row through later cache growth. -/
theorem runs_grow [DecidableEq (EdgeKey Symbol Guard)]
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context before outputs) (growth : Grows before after)
    (meaning : Guard → Term Symbol → Bool) (values : List (Value Symbol Guard))
    (available : Values before values) (terms : List (Term Symbol))
    (runs : All₂ (EpsilonUnion.Accepts (graph before meaning)) values terms) :
    All₂ (EpsilonUnion.Accepts (graph after meaning)) values terms := by
  exact all₂_left_imp _ _ values terms runs (fun value member term accepted =>
    (accepts_stable before after outputs context growth meaning value (available value member) term).mpr accepted)

/-- Child certificates compose through the actual sequence and its final cache. -/
theorem mapCalls_correct [DecidableEq (EdgeKey Symbol Guard)]
    (call : Request → Work Symbol Guard (Value Symbol Guard))
    (operands : Request → List (Value Symbol Guard)) (requests : List Request)
    (outputs : List (Value Symbol Guard)) (meaning : Guard → Term Symbol → Bool)
    (certified : ∀ request ∈ requests, ∀ state, Context state outputs → Values state (operands request) →
      let result := run (call request) state
      Context result.2 outputs ∧ Available result.2 result.1 ∧ Covers state result.2 meaning (operands request) result.1)
    (state : InternedConstructorTemplates.State Symbol Guard) (context : Context state outputs)
    (inputs : ∀ request ∈ requests, Values state (operands request)) :
    let result := run (mapCalls call requests) state
    Context result.2 outputs ∧ Values result.2 result.1 ∧
      All₂ (fun request value => Covers state result.2 meaning (operands request) value) requests result.1 := by
  induction requests generalizing state with
  | nil => exact ⟨context, by simp [Values, mapCalls, run], .nil⟩
  | cons first rest ih =>
      let head := run (call first) state
      let tail := run (mapCalls call rest) head.2
      have firstChecked := certified first List.mem_cons_self state context (inputs first List.mem_cons_self)
      have headContext : Context head.2 outputs := firstChecked.1
      have headAvailable : Available head.2 head.1 := firstChecked.2.1
      have headGrowth := (InternedConstructorTemplates.run_correct (call first) state context.facts.coherent.valid).2
      have laterInputs : ∀ request ∈ rest, Values head.2 (operands request) := by
        intro request member value included
        exact available_after_run (call first) state context.facts.coherent.valid
          (inputs request (List.mem_cons_of_mem _ member) value included)
      have restChecked := ih (fun request member => certified request (List.mem_cons_of_mem _ member)) head.2 headContext laterInputs
      have tailGrowth := (InternedConstructorTemplates.run_correct (mapCalls call rest) head.2 headContext.facts.coherent.valid).2
      have finalHead := available_after_run (mapCalls call rest) head.2 headContext.facts.coherent.valid headAvailable
      simp only [mapCalls, run_bind, run]
      refine ⟨restChecked.1, ?_, .cons ?_ ?_⟩
      · intro value member
        rcases List.mem_cons.mp member with same | member
        · rw [same]; exact finalHead
        · exact restChecked.2.1 value member
      · intro value member term accepted
        exact (accepts_stable head.2 tail.2 outputs headContext tailGrowth meaning head.1 headAvailable term).mpr
          (firstChecked.2.2 value member term accepted)
      · apply all₂_left_imp _ _ rest _ restChecked.2.2
        intro request original result covers value member term accepted
        exact covers value member term ((accepts_stable state head.2 outputs context headGrowth meaning value
          (inputs request (List.mem_cons_of_mem _ original) value member) term).mpr accepted)

end MicroCFTA.MergedPhysicalGroupCalls
