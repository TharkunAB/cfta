import MicroCFTA.MergedColdGraphApprox

/-!
# Exact finite languages through cold cache growth

Preparation excludes new dynamic Mu construction during stored unfolding.
Ordinary identities can differ between the discarded cold execution and
later execution. A finite Mu exposure induction compares their languages.
-/
namespace MicroCFTA.MergedColdGraphTransport
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedNestedConstruction InternedStoredSubstitution InternedStoredClosedMuCompletion
open MergedPhysicalWarmup MergedPhysicalLanguage MergedColdInterpretation MergedColdBuildLanguage
open MergedColdGraphApprox Language

/-- Equal child languages on one stored child list preserve all ordered runs. -/
theorem runs_congr (first second : A → B → Prop) (values : List A)
    (same : ∀ value ∈ values, ∀ term, first value term ↔ second value term) (terms : List B) :
    All₂ first values terms ↔ All₂ second values terms := by
  induction values generalizing terms with
  | nil => constructor <;> intro runs <;> cases runs <;> exact .nil
  | cons value rest ih =>
      constructor
      · intro runs
        cases runs with
        | cons head tail =>
            exact .cons ((same value List.mem_cons_self _).mp head)
              ((ih (fun value member => same value (List.mem_cons_of_mem _ member)) _).mp tail)
      · intro runs
        cases runs with
        | cons head tail =>
            exact .cons ((same value List.mem_cons_self _).mpr head)
              ((ih (fun value member => same value (List.mem_cons_of_mem _ member)) _).mpr tail)

/-- Every prepared lexical input remains an original available record. -/
theorem input_available (state : State Symbol Guard) (environment : List (Value Symbol Guard))
    (inputs : Values state environment) (index : Nat) : Available state (environment[index]?.getD .empty) := by
  cases found : environment[index]? with
  | none => simpa only [found, Option.getD_none] using empty_available state
  | some value => simpa only [found, Option.getD_some] using inputs value (List.mem_of_getElem? found)

/-- Every finite exposure bound is independent of later ordinary allocation identities. -/
theorem approx_stable [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (facts : Facts before) (laterFacts : Facts after)
    (prepared : Prepared before) (retained : ∀ value, Available before value → Available after value)
    (meaning : Guard → Term Symbol → Bool) (bound : Nat) (value : Value Symbol Guard)
    (available : Available before value) (term : Term Symbol) :
    Approx before meaning bound value term ↔ Approx after meaning bound value term := by
  cases value with
  | empty => exact iff_of_false ((laws before meaning bound).empty term) ((laws after meaning bound).empty term)
  | reference name => constructor <;> intro accepted <;> cases accepted
  | node entry edges depth free =>
      rw [(laws before meaning bound).node, (laws after meaning bound).node]
      apply exists_congr
      intro edge
      apply and_congr_right
      intro member
      simp only [EdgeMeaning]
      apply exists_congr
      intro terms
      apply and_congr_right
      intro shape
      apply and_congr _ Iff.rfl
      apply runs_congr
      intro child present subterm
      exact approx_stable before after facts laterFacts prepared retained meaning bound child
        (available.children child (List.mem_flatMap.mpr ⟨edge, member, present⟩)) subterm
  | union entry members depth free =>
      rw [(laws before meaning bound).union, (laws after meaning bound).union]
      apply exists_congr
      intro child
      apply and_congr_right
      intro member
      exact approx_stable before after facts laterFacts prepared retained meaning bound child (available.children child member) term
  | mu entry body depth ordinary =>
      cases bound with
      | zero => constructor <;> intro accepted <;> cases accepted
      | succ bound =>
          let replacement : Environment Symbol Guard := fun name =>
            if name = .interned entry.identity then some (.mu entry body depth ordinary) else none
          let environment := (leaves body).map (input replacement)
          have bodyInput : Available before body := available.children body (by simp [children])
          have replacements : Replacements before replacement := by
            intro name value found
            dsimp [replacement] at found
            split at found
            · cases found; exact available
            · contradiction
          have inputs : Values before environment := inputs_available body replacement before bodyInput replacements
          have laterInputs : Values after environment := fun value member => retained value (inputs value member)
          have bodyPrepared := prepared entry.key entry body depth ordinary (available.resident entry rfl)
          have free := encode_withoutMu (leaves body) [] body bodyPrepared
          obtain ⟨first, firstState, firstDone⟩ := InternedStoredClosedMuCompletion.execute_complete body replacement before bodyPrepared
          obtain ⟨second, secondState, secondDone⟩ := InternedStoredClosedMuCompletion.execute_complete body replacement after bodyPrepared
          rw [mu_exact before meaning bound entry body depth ordinary first firstState firstDone term,
            mu_exact after meaning bound entry body depth ordinary second secondState secondDone term]
          rw [build_plan (encode (leaves body) [] body) environment before facts inputs free
            (Approx before meaning bound) meaning (laws before meaning bound) first firstState firstDone term,
            build_plan (encode (leaves body) [] body) environment after laterFacts laterInputs free
            (Approx after meaning bound) meaning (laws after meaning bound) second secondState secondDone term]
          apply plan_congr
          intro index subterm
          exact approx_stable before after facts laterFacts prepared retained meaning bound _
            (input_available before environment inputs index) subterm
termination_by (bound, sizeOf value)
decreasing_by
  · obtain ⟨edgeEntry, edgeChildren⟩ := edge
    have outer := List.sizeOf_lt_of_mem member
    have inner := List.sizeOf_lt_of_mem present
    simp only [EdgeValue.children, EdgeValue.mk.sizeOf_spec] at *
    simp_all only [Value.node.sizeOf_spec]
    simp_wf
    omega
  · have smaller := List.sizeOf_lt_of_mem member
    simp_all only [Value.union.sizeOf_spec]
    simp_wf
    omega
  · simp_wf
    apply Prod.Lex.left
    omega

/-- Original available records retain exactly their finite raw graph languages after cache growth. -/
theorem accepts_stable [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (facts : Facts before) (laterFacts : Facts after)
    (prepared : Prepared before) (growth : Grows before after)
    (history : Cache.Extends before.nodes.issued after.nodes.issued)
    (meaning : Guard → Term Symbol → Bool) (value : Value Symbol Guard)
    (available : Available before value) (term : Term Symbol) :
    EpsilonUnion.Accepts (graph before meaning) value term ↔ EpsilonUnion.Accepts (graph after meaning) value term := by
  rw [MergedColdGraphApprox.exact, MergedColdGraphApprox.exact]
  exact exists_congr fun bound => approx_stable before after facts laterFacts prepared
    (fun value available => available.grows before after growth history) meaning bound value available term

end MicroCFTA.MergedColdGraphTransport
