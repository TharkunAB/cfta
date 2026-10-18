import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentLiteralUnionParts

/-!
# Semantic entries of actual stored member calls

Completed calls derive the semantic heap at each indexed source occurrence.
Literal union rows retain an actual original member and its exact call interval.
-/
namespace MicroCFTA.SourceCurrentStoredLiteralCalls
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open SourceCurrentStoredSubstitutionCalls (Calls)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentLiteralRootParts (Row)

/-- An actual completed stored substitution derives semantic output and both physical histories. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (source : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before source) (replacements : Replacements before environment)
    (output : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute source environment before = .done output after) :
    SemanticHeap after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      Available after output ∧ Replacements after environment := by
  have inputs := InternedStoredSubstitution.inputs_available source environment before available replacements
  have retained := SourceRecursiveIntersectionSemanticHeap.source (encode (leaves source) [] source)
    ((leaves source).map (input environment)) before semantic inputs
  have checked := InternedFreshOrdinaryFacts.build_verified (encode (leaves source) [] source)
    ((leaves source).map (input environment)) before semantic.1.normal.facts inputs
  change SemanticHeap (InternedFreshOrdinaryStoredSubstitution.execute source environment before).state at retained
  change InternedNestedFacts.Verified before
    (InternedFreshOrdinaryStoredSubstitution.execute source environment before) Available at checked
  have growth : Grows before after := by simpa only [actual, Outcome.state] using checked.growth
  have issued : Extends before.nodes.issued after.nodes.issued := by
    simpa only [actual, Outcome.state] using checked.history
  exact ⟨by simpa only [actual, Outcome.state] using retained, growth, issued,
    checked.result output after actual,
    fun name value found => (replacements name value found).grows before after growth issued⟩

private theorem calls [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : Calls environment originals before outputs after)
    (semantic : SemanticHeap before) (available : Values before originals)
    (replacements : Replacements before environment) :
    SemanticHeap after ∧ Grows before after ∧ Extends before.nodes.issued after.nodes.issued ∧
      Values after outputs ∧ Replacements after environment := by
  induction actual with
  | nil => exact ⟨semantic, grows_refl _, extends_refl _, available, replacements⟩
  | cons original originals before middle after output outputs called rest ih =>
      obtain ⟨middleSemantic, firstGrowth, firstIssued, outputAvailable, middleReplacements⟩ :=
        execute original environment before semantic (available original List.mem_cons_self) replacements output middle called
      have remaining : Values middle originals := fun value member =>
        (available value (List.mem_cons_of_mem _ member)).grows before middle firstGrowth firstIssued
      obtain ⟨afterSemantic, restGrowth, restIssued, outputsAvailable, afterReplacements⟩ :=
        ih middleSemantic remaining middleReplacements
      refine ⟨afterSemantic,grows_trans firstGrowth restGrowth,extends_trans firstIssued restIssued,?_,afterReplacements⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputAvailable.grows middle after restGrowth restIssued
      · exact outputsAvailable value member

/-- An indexed result retains its source, actual prefix and suffix, and derived semantic call entry. -/
theorem indexed [DecidableEq (EdgeKey Symbol Guard)] {environment : Environment Symbol Guard}
    {originals outputs : List (Value Symbol Guard)} {before after : State Symbol Guard}
    (actual : Calls environment originals before outputs after)
    (semantic : SemanticHeap before) (available : Values before originals)
    (replacements : Replacements before environment)
    (index : Nat) (output : Value Symbol Guard) (selected : outputs[index]? = some output) :
    ∃ original current next, originals[index]? = some original ∧
      Calls environment (originals.take index) before (outputs.take index) current ∧
      InternedFreshOrdinaryStoredSubstitution.execute original environment current = .done output next ∧
      Calls environment (originals.drop (index + 1)) next (outputs.drop (index + 1)) after ∧
      SemanticHeap current ∧ Available current original ∧ Replacements current environment ∧
      SemanticHeap next ∧ Available next output ∧ Replacements next environment ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Grows current next ∧ Extends current.nodes.issued next.nodes.issued ∧
      Grows next after ∧ Extends next.nodes.issued after.nodes.issued := by
  obtain ⟨original,current,next,found,earlier,called,later⟩ := actual.indexed index output selected
  have earlierAvailable : Values before (originals.take index) :=
    fun value member => available value (List.mem_of_mem_take member)
  obtain ⟨currentSemantic,earlierGrowth,earlierIssued,_currentOutputs,currentReplacements⟩ :=
    calls earlier semantic earlierAvailable replacements
  have originalAvailable := (available original (List.mem_of_getElem? found)).grows
    before current earlierGrowth earlierIssued
  obtain ⟨nextSemantic,calledGrowth,calledIssued,outputAvailable,nextReplacements⟩ :=
    execute original environment current currentSemantic originalAvailable currentReplacements output next called
  have laterAvailable : Values next (originals.drop (index + 1)) := fun value member =>
    (available value (List.mem_of_mem_drop member)).grows before next
      (grows_trans earlierGrowth calledGrowth) (extends_trans earlierIssued calledIssued)
  obtain ⟨_afterSemantic,laterGrowth,laterIssued,_afterOutputs,_afterReplacements⟩ :=
    calls later nextSemantic laterAvailable nextReplacements
  exact ⟨original,current,next,found,earlier,called,later,currentSemantic,originalAvailable,currentReplacements,
    nextSemantic,outputAvailable,nextReplacements,earlierGrowth,earlierIssued,calledGrowth,calledIssued,
    laterGrowth,laterIssued⟩

/-- An actual open union row comes from one indexed original member call at its derived semantic entry. -/
theorem union_row [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned InternedBinderProtocol.NodeKey)
    (originals : List (Value Symbol Guard)) (level : Nat) (free : List InternedBinderProtocol.Reference)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.union entry originals level free))
    (replacements : Replacements before environment) (opened : free.isEmpty = false)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute (.union entry originals level free) environment before =
      .done result after) (row : EdgeValue Symbol Guard) (selected : Row result row) :
    ∃ values middle index original output current next,
      Calls environment originals before values middle ∧ run (makeUnion values) middle = (result,after) ∧
      originals[index]? = some original ∧ values[index]? = some output ∧ Row output row ∧
      Calls environment (originals.take index) before (values.take index) current ∧
      InternedFreshOrdinaryStoredSubstitution.execute original environment current = .done output next ∧
      Calls environment (originals.drop (index + 1)) next (values.drop (index + 1)) middle ∧
      SemanticHeap current ∧ Available current original ∧ Replacements current environment ∧
      SemanticHeap next ∧ Available next output ∧ Replacements next environment ∧
      Grows before current ∧ Extends before.nodes.issued current.nodes.issued ∧
      Grows current next ∧ Extends current.nodes.issued next.nodes.issued ∧
      Grows next after ∧ Extends next.nodes.issued after.nodes.issued := by
  obtain ⟨values,middle,actualCalls,made,_origins⟩ := SourceCurrentStoredSubstitutionOrigins.union entry originals
    level free environment before semantic.1.normal available replacements opened result after actual
  have originalsAvailable : Values before originals := fun value member => available.children value member
  obtain ⟨middleSemantic,_growth,_issued,valuesAvailable,_middleReplacements⟩ :=
    calls actualCalls semantic originalsAvailable replacements
  have rows := SourceCurrentLiteralUnionParts.row middle middleSemantic.1.normal.facts middleSemantic.1.normal.live
    values valuesAvailable row
  rw [made] at rows
  obtain ⟨output,member,part⟩ := rows.mp selected
  obtain ⟨index,foundOutput⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨original,current,next,found,earlier,called,later,currentSemantic,originalAvailable,currentReplacements,
    nextSemantic,outputAvailable,nextReplacements,earlierGrowth,earlierIssued,calledGrowth,calledIssued,laterGrowth,laterIssued⟩ :=
    indexed actualCalls semantic originalsAvailable replacements index output foundOutput
  have unionChecked := InternedNestedFacts.union_verified values middle middleSemantic.1.normal.facts valuesAvailable
  have unionGrowth : Grows middle after := by simpa only [InternedNestedConstruction.work,made,Outcome.state] using unionChecked.growth
  have unionIssued : Extends middle.nodes.issued after.nodes.issued := by
    simpa only [InternedNestedConstruction.work,made,Outcome.state] using unionChecked.history
  exact ⟨values,middle,index,original,output,current,next,actualCalls,made,found,foundOutput,part,
    earlier,called,later,currentSemantic,originalAvailable,currentReplacements,nextSemantic,outputAvailable,nextReplacements,
    earlierGrowth,earlierIssued,calledGrowth,calledIssued,grows_trans laterGrowth unionGrowth,
    extends_trans laterIssued unionIssued⟩

end MicroCFTA.SourceCurrentStoredLiteralCalls
