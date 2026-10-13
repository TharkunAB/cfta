import MicroCFTA.MergedColdInterpretation

/-!
# Cache-independent languages of binder-free source construction

Every constructor uses its actual cache readback. The recursive leaves
have arbitrary languages that satisfy the ordinary constructor laws.
-/
namespace MicroCFTA.MergedColdBuildLanguage
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedNestedConstruction InternedStoredShallowCompletion InternedEdgeResidency
open MergedColdInterpretation Language

/-- A finite constructor plan reads its lexical inputs and retains each full guard. -/
inductive Plan (meaning : Guard → Term Symbol → Bool) (input : Nat → Term Symbol → Prop) :
    Syntax Symbol Guard → Term Symbol → Prop where
  | input : input index term → Plan meaning input (.var index) term
  | node {symbol : Symbol} {guard : Guard} {children : List (Syntax Symbol Guard)} :
      EdgeSyntax.mk symbol guard children ∈ edges →
      All₂ (Plan meaning input) children terms → meaning guard (.node symbol terms) = true →
      Plan meaning input (.node edges) (.node symbol terms)
  | union : member ∈ members → Plan meaning input member term → Plan meaning input (.union members) term

/-- One source edge plan keeps the ordered child plans. -/
def EdgePlan (meaning : Guard → Term Symbol → Bool) (input : Nat → Term Symbol → Prop)
    (edge : EdgeSyntax Symbol Guard) (term : Term Symbol) : Prop :=
  match edge with
  | .mk symbol guard children => ∃ terms, term = .node symbol terms ∧
      All₂ (Plan meaning input) children terms ∧ meaning guard term = true

/-- Positionwise equivalent languages have the same ordered child runs. -/
theorem related_runs (left : A → C → Prop) (right : B → C → Prop)
    (as : List A) (bs : List B) (related : All₂ (fun a b => ∀ c, left a c ↔ right b c) as bs)
    (cs : List C) : All₂ left as cs ↔ All₂ right bs cs := by
  induction related generalizing cs with
  | nil => constructor <;> intro runs <;> cases runs <;> exact .nil
  | cons head tail ih =>
      constructor
      · intro runs; cases runs with | cons first rest => exact .cons ((head _).mp first) ((ih _).mp rest)
      · intro runs; cases runs with | cons first rest => exact .cons ((head _).mpr first) ((ih _).mpr rest)

/-- Positionwise equivalent languages have the same alternative language. -/
theorem related_exists (left : A → C → Prop) (right : B → C → Prop)
    (as : List A) (bs : List B) (related : All₂ (fun a b => ∀ c, left a c ↔ right b c) as bs)
    (c : C) : (∃ a ∈ as, left a c) ↔ ∃ b ∈ bs, right b c := by
  induction related with
  | nil => simp
  | cons head tail ih => simpa only [List.mem_cons, exists_eq_or_imp] using or_congr (head c) ih

/-- The plan node rule exposes one original edge. -/
theorem plan_node (meaning : Guard → Term Symbol → Bool) (input : Nat → Term Symbol → Prop)
    (edges : List (EdgeSyntax Symbol Guard)) (term : Term Symbol) :
    Plan meaning input (.node edges) term ↔ ∃ edge ∈ edges, EdgePlan meaning input edge term := by
  constructor
  · intro accepted; cases accepted with | node member runs allowed => exact ⟨_, member, _, rfl, runs, allowed⟩
  · rintro ⟨⟨symbol, guard, children⟩, member, terms, rfl, runs, allowed⟩
    exact .node member runs allowed

mutual
/-- Actual binder-free construction has the plan language in any fixed interpretation. -/
theorem build_plan [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (free : BinderFree expression) (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : build expression environment state = .done value after) :
    ∀ term, lang value term ↔ Plan meaning (fun index => lang (environment[index]?.getD .empty)) expression term := by
  cases expression with
  | empty =>
      simp only [build, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      intro term
      constructor
      · exact fun accepted => False.elim (laws.empty term accepted)
      · intro accepted; cases accepted
  | var index =>
      simp only [build, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      intro term
      constructor
      · intro accepted; exact .input accepted
      · intro accepted; cases accepted with | input accepted => exact accepted
  | binder smart body => simp [BinderFree] at free
  | node edges =>
      simp only [BinderFree] at free
      obtain ⟨values, middle, built⟩ := buildEdges_complete edges environment state free
      have verified := buildEdges_verified edges environment state facts inputs
      have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
      have resident := verified.result values middle built
      have matched := buildEdges_plan edges environment state facts inputs free lang meaning laws values middle built
      simp only [build, built, Outcome.bind, work, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      intro term
      exact (makeNode_exact middle middleFacts lang values resident meaning laws term).trans
        ((related_exists (EdgePlan meaning (fun index => lang (environment[index]?.getD .empty)))
          (EdgeMeaning lang meaning) edges values matched term).symm.trans (plan_node _ _ _ _).symm)
  | union members =>
      simp only [BinderFree] at free
      obtain ⟨values, middle, built⟩ := buildMany_complete members environment state free
      have verified := buildMany_verified members environment state facts inputs
      have middleFacts : Facts middle := by simpa only [built, Outcome.state] using verified.facts
      have available := verified.result values middle built
      have matched := buildMany_plan members environment state facts inputs free lang meaning laws values middle built
      simp only [build, built, Outcome.bind, work, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      intro term
      rw [makeUnion_common middle middleFacts lang values available meaning laws term,
        ← related_exists _ _ members values matched term]
      constructor
      · rintro ⟨member, present, accepted⟩; exact .union present accepted
      · intro accepted; cases accepted with | union present accepted => exact ⟨_, present, accepted⟩
termination_by sizeOf expression

/-- Each actual child result has its own source plan language. -/
theorem buildMany_plan [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (free : ManyBinderFree expressions) (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning)
    (values : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : buildMany expressions environment state = .done values after) :
    All₂ (fun expression value => ∀ term,
      Plan meaning (fun index => lang (environment[index]?.getD .empty)) expression term ↔ lang value term) expressions values := by
  cases expressions with
  | nil => simp only [buildMany, Outcome.done.injEq] at done; obtain ⟨rfl, rfl⟩ := done; exact .nil
  | cons first rest =>
      simp only [ManyBinderFree] at free
      obtain ⟨value, middle, firstDone⟩ := build_complete first environment state free.1
      obtain ⟨later, final, restDone⟩ := buildMany_complete rest environment middle free.2
      have verified := build_verified first environment state facts inputs
      have middleFacts : Facts middle := by simpa only [firstDone, Outcome.state] using verified.facts
      have middleInputs : Values middle environment := by
        intro value member
        simpa only [firstDone, Outcome.state] using verified.available value (inputs value member)
      simp only [buildMany, firstDone, Outcome.bind, restDone, Outcome.done.injEq] at done
      obtain ⟨rfl, rfl⟩ := done
      exact .cons (fun term => (build_plan first environment state facts inputs free.1 lang meaning laws value middle firstDone term).symm)
        (buildMany_plan rest environment middle middleFacts middleInputs free.2 lang meaning laws later final restDone)
termination_by sizeOf expressions

/-- Actual edge interning preserves each source edge plan, including child order. -/
theorem buildEdges_plan [DecidableEq (EdgeKey Symbol Guard)]
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (inputs : Values state environment)
    (free : EdgesBinderFree expressions) (lang : Value Symbol Guard → Term Symbol → Prop)
    (meaning : Guard → Term Symbol → Bool) (laws : Laws lang meaning)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : buildEdges expressions environment state = .done edges after) :
    All₂ (fun expression edge => ∀ term,
      EdgePlan meaning (fun index => lang (environment[index]?.getD .empty)) expression term ↔ EdgeMeaning lang meaning edge term)
      expressions edges := by
  cases expressions with
  | nil => simp only [buildEdges, Outcome.done.injEq] at done; obtain ⟨rfl, rfl⟩ := done; exact .nil
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          simp only [EdgesBinderFree] at free
          obtain ⟨values, middle, childrenDone⟩ := buildMany_complete children environment state free.1
          have verified := buildMany_verified children environment state facts inputs
          have middleFacts : Facts middle := by simpa only [childrenDone, Outcome.state] using verified.facts
          have middleInputs : Values middle environment := by
            intro value member
            simpa only [childrenDone, Outcome.state] using verified.available value (inputs value member)
          have available := verified.result values middle childrenDone
          let edge := run (makeEdge symbol guard values) middle
          have edgeVerified := edge_verified symbol guard values middle middleFacts available
          have edgeFacts : Facts edge.2 := edgeVerified.facts
          have edgeInputs : Values edge.2 environment := fun value member => edgeVerified.available value (middleInputs value member)
          obtain ⟨later, final, restDone⟩ := buildEdges_complete rest environment edge.2 free.2
          have fields := MergedPhysicalGroupEdges.makeEdge_fields middle middleFacts symbol guard values available
          dsimp only [edge] at restDone
          have childrenMatched := buildMany_plan children environment state facts inputs free.1 lang meaning laws values middle childrenDone
          simp only [buildEdges, childrenDone, Outcome.bind, work, restDone, Outcome.done.injEq] at done
          obtain ⟨rfl, rfl⟩ := done
          apply All₂.cons
          · intro term
            simp only [EdgePlan, EdgeMeaning, fields.1, fields.2.1, fields.2.2]
            exact exists_congr fun terms => and_congr_right fun _ =>
              and_congr (related_runs _ _ children values childrenMatched terms) Iff.rfl
          · exact buildEdges_plan rest environment edge.2 edgeFacts edgeInputs free.2 lang meaning laws later final restDone
termination_by sizeOf expressions
end

/-- Equal lexical input languages give equal plan languages. -/
theorem plan_congr (meaning : Guard → Term Symbol → Bool) (first second : Nat → Term Symbol → Prop)
    (same : ∀ index term, first index term ↔ second index term)
    (expression : Syntax Symbol Guard) (term : Term Symbol) :
    Plan meaning first expression term ↔ Plan meaning second expression term := by
  have forward : ∀ (first second : Nat → Term Symbol → Prop),
      (∀ index term, first index term → second index term) →
      ∀ expression term, Plan meaning first expression term → Plan meaning second expression term := by
    intro first second same expression term accepted
    induction accepted using Plan.rec
      (motive_2 := fun expressions terms _ => All₂ (Plan meaning second) expressions terms) with
    | input accepted => exact .input (same _ _ accepted)
    | node member _ allowed ih => exact .node member ih allowed
    | union member _ ih => exact .union member ih
    | nil => exact .nil
    | cons _ _ first rest => exact .cons first rest
  exact ⟨forward first second (fun index term => (same index term).mp) expression term,
    forward second first (fun index term => (same index term).mpr) expression term⟩

end MicroCFTA.MergedColdBuildLanguage
