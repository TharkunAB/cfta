import MicroCFTA.SourceCurrentUsedBinderOutputTags

/-!
# Actual source union calls and root self filters

Actual union construction determines the member calls and their contexts.
The induction hypothesis applies only to indexed strict source members.
The two source calls can start and return at different heaps. Their root
parts retain complete guards and ordered child relations. Initial live
alias tests determine the bare-self cases of the actual raw returns.
The result compares the two actual root filters. It does not prove a
stored reconstruction relation or the nested binder induction case.
-/
namespace MicroCFTA.SourceCurrentSourceUnionFilterInduction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryContext InternedFreshOrdinaryFacts
open InternedFreshOrdinaryLiveInputs (input inputProfile)
open SourceCurrentNativeNormalizationInputs (support inputNames)
open SourceCurrentUsedBinderAliasTransport (Scope Aliases)
open SourceCurrentUsedBinderRootAlternatives (RootMatch)
open InternedBinderProtocol (Reference)
open Language
variable {Atom : Type}

private theorem member_aliases (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (aliases : Aliases (.union expressions) inputs firstNames secondNames)
    (child : Syntax Symbol Guard) (member : child ∈ expressions) :
    Aliases child inputs firstNames secondNames := by
  have included (label : Sum Reference Atom) (present : label ∈ Scope child inputs) :
      label ∈ Scope (.union expressions) inputs := by
    rcases List.mem_cons.mp present with rfl | present
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      unfold support at present ⊢
      rw [InternedFreeNameSemantics.evaluate]
      exact (InternedFreeNameSemantics.evaluateMany_member expressions (inputs.map inputProfile)
        (inputs.map inputNames) label).mpr ⟨child,member,present⟩
  exact fun left leftMember right rightMember => aliases left (included left leftMember) right (included right rightMember)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem many_calls (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before inputs)
    (outputs : List (Value Symbol Guard)) (after : State Symbol Guard)
    (actual : buildMany expressions inputs before = .done outputs after) :
    All₂ (fun expression output => ∃ entry returned,
      Context entry inputs ∧ build expression inputs entry = .done output returned) expressions outputs := by
  induction expressions generalizing before outputs after with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs before with
      | pending key current => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done value middle =>
          cases tail : buildMany rest inputs middle with
          | pending key current => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done values final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,rfl⟩ := actual
              have next : Context middle inputs := by
                simpa only [called,Outcome.state] using context.build expression
              exact .cons ⟨before,middle,context,called⟩ (ih middle next values final tail)

private theorem paired_calls (expressions : List (Syntax Symbol Guard))
    (leftInputs rightInputs : List (Value Symbol Guard))
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (cases : ∀ child ∈ expressions,
      ∀ leftEntry rightEntry, Context leftEntry leftInputs → Context rightEntry rightInputs →
      ∀ first leftAfter second rightAfter,
        build child leftInputs leftEntry = .done first leftAfter →
        build child rightInputs rightEntry = .done second rightAfter → RootMatch references values first second)
    (first second : List (Value Symbol Guard))
    (firstCalls : All₂ (fun expression output => ∃ entry returned,
      Context entry leftInputs ∧ build expression leftInputs entry = .done output returned) expressions first)
    (secondCalls : All₂ (fun expression output => ∃ entry returned,
      Context entry rightInputs ∧ build expression rightInputs entry = .done output returned) expressions second) :
    All₂ (RootMatch references values) first second := by
  induction firstCalls generalizing second with
  | nil => cases secondCalls; exact .nil
  | @cons expression first expressions firsts head tail ih =>
      cases secondCalls with
      | cons other remaining =>
          obtain ⟨leftEntry,leftAfter,leftContext,firstDone⟩ := head
          obtain ⟨rightEntry,rightAfter,rightContext,secondDone⟩ := other
          exact .cons (cases expression List.mem_cons_self leftEntry rightEntry leftContext rightContext
            first leftAfter _ rightAfter firstDone secondDone)
            (ih (fun child member => cases child (List.mem_cons_of_mem _ member)) _ remaining)

private theorem union_parts (expressions : List (Syntax Symbol Guard)) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (context : Context before inputs) (result : Value Symbol Guard)
    (after : State Symbol Guard) (actual : build (.union expressions) inputs before = .done result after) :
    ∃ outputs middle,
      buildMany expressions inputs before = .done outputs middle ∧ Context middle inputs ∧
      Values middle outputs ∧ run (makeUnion outputs) middle = (result,after) := by
  cases called : buildMany expressions inputs before with
  | pending key current => simp only [build,called,Outcome.bind] at actual; cases actual
  | done outputs middle =>
      have made : run (makeUnion outputs) middle = (result,after) :=
        Prod.ext (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).1
          (Outcome.done.inj (by simpa only [build,called,Outcome.bind,work] using actual)).2
      exact ⟨outputs,middle,rfl,
        by simpa only [called,Outcome.state] using context.many expressions,
        (buildMany_verified expressions inputs before context.normal.facts context.inputs).result outputs middle called,made⟩

/-- Indexed strict-member induction derives both raw union parts and the two actual root-filter parts. -/
theorem union_filtered (expressions : List (Syntax Symbol Guard))
    (inputs : List (Sum (Value Symbol Guard) Atom)) (firstNames secondNames : Atom → Reference)
    (references : Reference → Reference → Prop) (values : Value Symbol Guard → Value Symbol Guard → Prop)
    (own other : Reference) (before after later final : State Symbol Guard)
    (firstContext : Context before (inputs.map (input firstNames)))
    (secondContext : Context later (inputs.map (input secondNames)))
    (aliases : Aliases (.union expressions) inputs firstNames secondNames)
    (selfTests : ∀ label ∈ Scope (.union expressions) inputs,
      Sum.elim id firstNames label = own ↔ Sum.elim id secondNames label = other)
    (referenceLocal : ∀ first second, references first second → (first = own ↔ second = other))
    (memberIH : ∀ (index : Nat) (child : Syntax Symbol Guard), expressions[index]? = some child →
      sizeOf child < sizeOf (.union expressions : Syntax Symbol Guard) →
      Aliases child inputs firstNames secondNames →
      ∀ leftEntry rightEntry,
        Context leftEntry (inputs.map (input firstNames)) → Context rightEntry (inputs.map (input secondNames)) →
      ∀ first leftAfter second rightAfter,
        build child (inputs.map (input firstNames)) leftEntry = .done first leftAfter →
        build child (inputs.map (input secondNames)) rightEntry = .done second rightAfter →
        RootMatch references values first second)
    (first second : Value Symbol Guard)
    (firstDone : build (.union expressions) (inputs.map (input firstNames)) before = .done first after)
    (secondDone : build (.union expressions) (inputs.map (input secondNames)) later = .done second final) :
    RootMatch references values first second ∧
      (first = .reference own ↔ second = .reference other) ∧
      RootMatch references values (run (withoutSelfReference own first) after).1
        (run (withoutSelfReference other second) final).1 := by
  obtain ⟨left,leftMiddle,leftMany,leftContext,leftAvailable,leftMade⟩ :=
    union_parts expressions _ before firstContext first after firstDone
  obtain ⟨right,rightMiddle,rightMany,rightContext,rightAvailable,rightMade⟩ :=
    union_parts expressions _ later secondContext second final secondDone
  have childCases : ∀ child ∈ expressions,
      ∀ leftEntry rightEntry, Context leftEntry (inputs.map (input firstNames)) →
        Context rightEntry (inputs.map (input secondNames)) →
      ∀ first leftAfter second rightAfter,
        build child (inputs.map (input firstNames)) leftEntry = .done first leftAfter →
        build child (inputs.map (input secondNames)) rightEntry = .done second rightAfter →
        RootMatch references values first second := by
    intro child member
    obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp member
    have smaller : sizeOf child < sizeOf (.union expressions : Syntax Symbol Guard) := by
      have strict := List.sizeOf_lt_of_mem member
      simp only [Syntax.union.sizeOf_spec]
      omega
    exact memberIH index child found smaller (member_aliases expressions inputs firstNames secondNames aliases child member)
  have matched := paired_calls expressions _ _ references values childCases left right
    (many_calls expressions _ before firstContext left leftMiddle leftMany)
    (many_calls expressions _ later secondContext right rightMiddle rightMany)
  have raw := SourceCurrentUsedBinderRootAlternatives.union_ordered references values left right leftMiddle rightMiddle
    leftContext.normal rightContext.normal leftAvailable rightAvailable matched
  rw [leftMade,rightMade] at raw
  have bare := SourceCurrentUsedBinderOutputTags.bare (.union expressions) inputs firstNames secondNames own other
    before after later final firstContext secondContext first second firstDone secondDone selfTests
  have firstReturned : Context after (inputs.map (input firstNames)) := by
    simpa only [firstDone,Outcome.state] using firstContext.build (.union expressions)
  have secondReturned : Context final (inputs.map (input secondNames)) := by
    simpa only [secondDone,Outcome.state] using secondContext.build (.union expressions)
  have firstAvailable := (build_verified (.union expressions) _ before firstContext.normal.facts firstContext.inputs).result
    first after firstDone
  have secondAvailable := (build_verified (.union expressions) _ later secondContext.normal.facts secondContext.inputs).result
    second final secondDone
  exact ⟨raw,bare,SourceCurrentUsedBinderRootAlternatives.filter references values own other first second after final
    firstReturned.normal secondReturned.normal firstAvailable secondAvailable raw referenceLocal bare⟩

end MicroCFTA.SourceCurrentSourceUnionFilterInduction
