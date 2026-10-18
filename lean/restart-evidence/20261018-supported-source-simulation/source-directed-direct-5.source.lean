import MicroCFTA.SourceCurrentOpenPreorderSimulation
import MicroCFTA.SourceCurrentLiteralUnionParts
import MicroCFTA.SourceCurrentPublicationNodeRowSurvival
import MicroCFTA.SourceCurrentStoredNodeExpansion
import MicroCFTA.SourceCurrentStoredLiteralExecutionParts
import MicroCFTA.SourceCurrentLiteralUnionFusion

/-!
# Local source cases for directional simulation

Literal inclusion supplies normalization fragments at one reader.
Actual node calls retain full rows and ordered child memberships.
Physical Empty agreement is required only where rows can be removed.
The general used-binder source simulation remains separate.
-/
namespace MicroCFTA.SourceCurrentSourceDirectedCases
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedEdgeResidency (nodeEdges)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedBinderProtocol (Reference)
open SourceCurrentOpenPreorderSimulation (Directed Mutual)
open SourceCurrentOpenObservations (ReferenceOrigin RowMatch)
open SourceCurrentLiteralRootParts (Literal Row)
open MergedFreshOrdinaryGraph (Origin successors)
open Productivity (Reachable)
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryContext (Context)
open SourceEqualityRequiredCache (Ready Ordinary)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentStoredMuRetainedAlignment (RowCall)

/-- Exact root atoms and full rows of the first value occur in the second value. -/
def Below (first second : Value Symbol Guard) : Prop :=
  (∀ atom, Literal first atom → Literal second atom) ∧
    ∀ row, Row first row → Row second row

/-- Literal inclusion retains each value. -/
theorem Below.refl (value : Value Symbol Guard) : Below value value := ⟨fun _ => id,fun _ => id⟩

/-- Literal inclusion composes without an observation premise. -/
theorem Below.trans {first middle last : Value Symbol Guard}
    (left : Below first middle) (right : Below middle last) : Below first last :=
  ⟨fun atom found => right.1 atom (left.1 atom found),fun row found => right.2 row (left.2 row found)⟩

private theorem all_refl {relation : Value Symbol Guard → Value Symbol Guard → Prop}
    (reflexive : ∀ value, relation value value) (values : List (Value Symbol Guard)) : All₂ relation values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (reflexive value) ih

private def Survives (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧ Mutual relation first second

private theorem no_literal (value atom : Value Symbol Guard) (plain : Ordinary value) : ¬ Literal value atom := by
  cases value <;> try cases plain <;> intro impossible <;> cases impossible

private theorem ordinary_row (value : Value Symbol Guard) (plain : Ordinary value) (row : EdgeValue Symbol Guard) :
    Row value row ↔ row ∈ nodeEdges value := by
  cases value with
  | empty => constructor <;> intro impossible <;> cases impossible
  | node entry rows depth free => exact SourceCurrentLiteralRootParts.row_node entry rows depth free row
  | reference | union | mu => cases plain

private theorem children_empty (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    {first second : List (Value Symbol Guard)} (paired : All₂ (Survives relation) first second) :
    first.any (fun value => value.referenceOf == .empty) = second.any (fun value => value.referenceOf == .empty) := by
  induction paired with
  | nil => rfl
  | @cons first second rest remaining pair tail ih =>
      have head : (first.referenceOf == .empty) = (second.referenceOf == .empty) := by
        by_cases empty : first.referenceOf = .empty
        · simp only [empty,pair.1.mp empty,beq_self_eq_true]
        · have other : second.referenceOf ≠ .empty := fun found => empty (pair.1.mpr found)
          simp only [beq_eq_false_iff_ne.mpr empty,beq_eq_false_iff_ne.mpr other]
      simp only [List.any_cons,head,ih]

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One pair supplies the literal reference, physical row, and epsilon clauses. -/
def Local (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Value Symbol Guard) : Prop :=
  (∀ name : Reference, first = .reference name → ReferenceOrigin reader [second] name) ∧
  (∀ row ∈ nodeEdges first, ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other) ∧
  ∀ next ∈ successors reader first, ∃ later,
    Reachable (successors reader) [second] later ∧ relation next later

private theorem literal_path (reader : State Symbol Guard) {root atom : Value Symbol Guard}
    (found : Literal root atom) : Reachable (successors reader) [root] atom := by
  induction found with
  | reference | mu => exact .seed List.mem_cons_self
  | @union entry members level free value atom member found ih =>
      exact EpsilonUnion.reach_trans _ _ value atom
        (.step (.seed List.mem_cons_self) member) ih

private theorem row_origin (reader : State Symbol Guard) {root : Value Symbol Guard}
    {row : EdgeValue Symbol Guard} (found : Row root row) : Origin reader [root] row := by
  induction found with
  | node member => exact ⟨_,.seed List.mem_cons_self,member⟩
  | @union entry members level free value row member found ih =>
      exact ih.from_seeds reader [value] [.union entry members level free]
        (fun current present => (List.mem_singleton.mp present) ▸
          Reachable.step (Reachable.seed List.mem_cons_self) member) row

/-- Exact literal inclusion is a directional simulation, including actual Mu unfolding. -/
theorem below_directed (reader : State Symbol Guard) : Directed reader (Below (Symbol := Symbol) (Guard := Guard)) := by
  intro first second included
  refine ⟨?_,?_,?_⟩
  · intro name same
    subst first
    exact literal_path reader (included.1 _ (.reference name))
  · intro row member
    have literal : Row first row := by
      cases first with
      | node entry rows depth free => exact .node member
      | empty | reference | union | mu => cases member
    exact ⟨row,row_origin reader (included.2 row literal),rfl,rfl,
      all_refl (fun value => ⟨Below.refl value,Below.refl value⟩) row.children⟩
  · intro next member
    cases first with
    | empty | reference | node => cases member
    | union entry members level free =>
        refine ⟨second,.seed List.mem_cons_self,?_,?_⟩
        · intro atom found
          exact included.1 atom (.union member found)
        · intro row found
          exact included.2 row (.union member found)
    | mu entry body depth ordinary =>
        have reached := literal_path reader (included.1 _ (.mu entry body depth ordinary))
        exact ⟨next,.step reached member,Below.refl next⟩

/-- Equality gives a local clause when the child relation contains equality. -/
theorem equal (reader : State Symbol Guard) (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (reflexive : ∀ value, relation value value) (value : Value Symbol Guard) : Local reader relation value value := by
  refine ⟨?_,?_,?_⟩
  · intro name same
    exact same ▸ Reachable.seed List.mem_cons_self
  · intro row member
    exact ⟨row,⟨value,.seed List.mem_cons_self,member⟩,rfl,rfl,
      all_refl (fun value => ⟨reflexive value,reflexive value⟩) row.children⟩
  · intro next member
    exact ⟨next,.step (.seed List.mem_cons_self) member,reflexive next⟩

/-- A larger relation retains every local clause and both ordered child directions. -/
theorem Local.mono (reader : State Symbol Guard)
    (firstRelation secondRelation : Value Symbol Guard → Value Symbol Guard → Prop)
    (included : ∀ first second, firstRelation first second → secondRelation first second)
    {first second : Value Symbol Guard} (clauses : Local reader firstRelation first second) :
    Local reader secondRelation first second := by
  refine ⟨clauses.1,?_,?_⟩
  · intro row member
    obtain ⟨other,origin,fields⟩ := clauses.2.1 row member
    exact ⟨other,origin,fields.1,fields.2.1,
      All₂.imp (fun _ _ pair => ⟨included _ _ pair.1,included _ _ pair.2⟩) fields.2.2⟩
  · intro next member
    obtain ⟨later,reached,pair⟩ := clauses.2.2 next member
    exact ⟨later,reached,included _ _ pair⟩

/-- Each initial member is a literal fragment of the actual normalized union result. -/
theorem union_member (values : List (Value Symbol Guard)) (before : State Symbol Guard)
    (normal : Normal before) (available : Values before values)
    (value : Value Symbol Guard) (member : value ∈ values) :
    Below value (run (makeUnion values) before).1 := by
  constructor
  · intro atom found
    exact (SourceCurrentLiteralUnionParts.literal before normal.facts values available atom).mpr ⟨value,member,found⟩
  · intro row found
    exact (SourceCurrentLiteralUnionParts.row before normal.facts normal.live values available row).mpr ⟨value,member,found⟩

/-- Actual member and parent reconstructions derive a literal normalization fragment. -/
theorem union_reconstruction (originals outputs : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (common : State Symbol Guard)
    (normalized result : Value Symbol Guard) (ready : Ready common)
    (available : Values common originals) (replacements : Replacements common environment)
    (calls : All₂ (fun original output => execute original environment common = .done output common) originals outputs)
    (made : run (makeUnion originals) common = (normalized,common))
    (actual : execute normalized environment common = .done result common)
    (output : Value Symbol Guard) (member : output ∈ outputs) : Below output result := by
  have parts := SourceCurrentLiteralUnionFusion.warm originals outputs environment common normalized result
    ready available replacements calls made actual
  exact ⟨fun atom found => (parts.1 atom).mpr ⟨output,member,found⟩,
    fun row found => (parts.2 row).mpr ⟨output,member,found⟩⟩

private def Executions (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (common : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : Value Symbol Guard) : Prop :=
  ∀ result other, execute left first common = .done result common →
    execute right second common = .done other common → Survives relation result other

private def Child (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (common : State Symbol Guard) (firstInputs secondInputs : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (expression : Syntax Symbol Guard) : Prop :=
  ∀ left right, build expression firstInputs common = .done left common →
    build expression secondInputs common = .done right common → Executions relation common first second left right

private theorem source_children (expressions : List (Syntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (valid : Valid common)
    (outputs : List (Value Symbol Guard))
    (actual : buildMany expressions inputs common = .done outputs common) :
    All₂ (fun expression output => build expression inputs common = .done output common) expressions outputs := by
  induction expressions generalizing outputs with
  | nil =>
      simp only [buildMany,Outcome.done.injEq] at actual
      obtain ⟨rfl,_⟩ := actual
      exact .nil
  | cons expression rest ih =>
      cases called : build expression inputs common with
      | pending key middle => simp only [buildMany,called,Outcome.bind] at actual; cases actual
      | done output middle =>
          cases tail : buildMany rest inputs middle with
          | pending key final => simp only [buildMany,called,tail,Outcome.bind] at actual; cases actual
          | done remaining final =>
              simp only [buildMany,called,tail,Outcome.bind,Outcome.done.injEq] at actual
              obtain ⟨rfl,same⟩ := actual
              rw [same] at tail
              have checked := InternedFreshOrdinaryGrowth.build_correct expression inputs common valid
              have middleValid : Valid middle := by simpa only [called,Outcome.state] using checked.1
              have growth : Grows middle common := by
                simpa only [tail,Outcome.state] using
                  (InternedFreshOrdinaryGrowth.buildMany_correct rest inputs middle middleValid).2
              exact .cons (InternedFreshOrdinaryReplay.build_replay expression inputs common common output middle
                valid called growth) (ih remaining (InternedFreshOrdinaryReplay.buildMany_replays rest inputs
                  middle common remaining common middleValid tail (grows_refl _)))

private theorem children_executions (expressions : List (Syntax Symbol Guard))
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (common : State Symbol Guard)
    (firstInputs secondInputs : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (cases : ∀ expression ∈ expressions, Child relation common firstInputs secondInputs first second expression)
    (valid : Valid common) (left right : List (Value Symbol Guard))
    (firstDone : buildMany expressions firstInputs common = .done left common)
    (secondDone : buildMany expressions secondInputs common = .done right common) :
    All₂ (Executions relation common first second) left right := by
  have leftCalls := source_children expressions firstInputs common valid left firstDone
  have rightCalls := source_children expressions secondInputs common valid right secondDone
  clear firstDone secondDone
  induction leftCalls generalizing right with
  | nil => cases rightCalls; exact .nil
  | @cons expression left expressions lefts called rest ih =>
      cases rightCalls with
      | cons other remaining =>
          exact .cons (cases expression List.mem_cons_self _ _ called other)
            (ih (fun child member => cases child (List.mem_cons_of_mem _ member)) _ remaining)

private theorem source_ordinary (expressions : List (EdgeSyntax Symbol Guard))
    (inputs : List (Value Symbol Guard)) (common : State Symbol Guard) (ready : Ready common)
    (available : Values common inputs) (value : Value Symbol Guard)
    (actual : build (.node expressions) inputs common = .done value common) : Ordinary value := by
  cases called : InternedFreshOrdinaryConstruction.buildEdges expressions inputs common with
  | pending key middle => simp only [build,called,Outcome.bind] at actual; cases actual
  | done rows middle =>
      have made := Outcome.done.inj (by simpa only [build,called,Outcome.bind,InternedNestedConstruction.work] using actual)
      have checked := InternedFreshOrdinaryFacts.buildEdges_verified expressions inputs common
        ready.semantic.1.normal.facts available
      have facts : InternedNestedFacts.Facts middle := by simpa only [called,Outcome.state] using checked.facts
      have plain := SourceEqualityRequiredCache.node_ordinary rows middle facts (checked.result rows middle called)
      rw [made.1] at plain
      exact plain

private theorem raw_row_match (expressions : List (EdgeSyntax Symbol Guard))
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (common : State Symbol Guard)
    (firstInputs secondInputs : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (valid : Valid common) (index : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard))
    (firstRows secondRows : List (EdgeValue Symbol Guard)) (firstAfter secondAfter : State Symbol Guard)
    (left : RowCall expressions firstInputs common firstRows firstAfter common index symbol guard originals)
    (right : RowCall expressions secondInputs common secondRows secondAfter common index symbol guard originals)
    (cases : ∀ child ∈ originals, Child relation common firstInputs secondInputs first second child) :
    RowMatch (Executions relation common first second) left.output right.output := by
  have firstWarm := InternedFreshOrdinaryReplay.buildMany_replays originals firstInputs left.current common
    left.values left.middle left.context.normal.facts.coherent.valid left.called left.middle_growth
  have secondWarm := InternedFreshOrdinaryReplay.buildMany_replays originals secondInputs right.current common
    right.values right.middle right.context.normal.facts.coherent.valid right.called right.middle_growth
  refine ⟨left.symbol_eq.trans right.symbol_eq.symm,left.guard_eq.trans right.guard_eq.symm,?_⟩
  rw [left.children_eq,right.children_eq]
  exact children_executions originals relation common firstInputs secondInputs first second cases valid
    left.values right.values firstWarm secondWarm

private theorem stored_ordinary (raw result : Value Symbol Guard) (environment : Environment Symbol Guard)
    (common : State Symbol Guard) (ready : Ready common) (available : Available common raw)
    (replacements : Replacements common environment) (plain : Ordinary raw)
    (actual : execute raw environment common = .done result common) : Ordinary result := by
  cases raw with
  | empty =>
      have same := (Outcome.done.inj ((SourceCurrentStoredUnionObservations.closed .empty environment common rfl).symm.trans actual)).1
      subst result
      trivial
  | node entry rows depth free =>
      obtain ⟨_,_,ordinary,_⟩ := SourceCurrentStoredNodeExpansion.node_warm entry rows depth free
        environment common ready.semantic.1.normal available replacements result actual
      exact ordinary
  | reference | union | mu => cases plain

private theorem outputs (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (common : State Symbol Guard) (first second : Environment Symbol Guard)
    {left right firstOutputs secondOutputs : List (Value Symbol Guard)}
    (paired : All₂ (Executions relation common first second) left right)
    (firstCalls : All₂ (fun source result => execute source first common = .done result common) left firstOutputs)
    (secondCalls : All₂ (fun source result => execute source second common = .done result common) right secondOutputs) :
    All₂ (Survives relation) firstOutputs secondOutputs := by
  induction paired generalizing firstOutputs secondOutputs with
  | nil => cases firstCalls; cases secondCalls; exact .nil
  | cons pair rest ih =>
      cases firstCalls with
      | cons firstDone firstRest =>
          cases secondCalls with
          | cons secondDone secondRest => exact .cons (pair _ _ firstDone secondDone) (ih firstRest secondRest)

private theorem stored_row_match (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (common : State Symbol Guard) (first second : Environment Symbol Guard) (valid : Valid common)
    (rawFirst rawSecond row other : EdgeValue Symbol Guard)
    (paired : RowMatch (Executions relation common first second) rawFirst rawSecond)
    (firstCalls : RowCalls first common rawFirst row) (secondCalls : RowCalls second common rawSecond other) :
    RowMatch (Survives relation) row other := by
  exact ⟨firstCalls.2.2.1.trans (paired.1.trans secondCalls.2.2.1.symm),
    firstCalls.2.2.2.1.trans (paired.2.1.trans secondCalls.2.2.2.1.symm),
    outputs relation common first second paired.2.2
      (SourceCurrentStoredCallsReplay.replay firstCalls.1 common valid (grows_refl _))
      (SourceCurrentStoredCallsReplay.replay secondCalls.1 common valid (grows_refl _))⟩

private theorem terminal_local (reader : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop) (first second : Value Symbol Guard)
    (plain : Ordinary first)
    (rows : ∀ row ∈ nodeEdges first, ∃ other, Origin reader [second] other ∧ RowMatch (Mutual relation) row other) :
    Local reader relation first second := by
  refine ⟨?_,rows,?_⟩
  · intro name same
    subst first
    cases plain
  · intro next member
    cases first <;> try cases plain <;> cases member

/-- Actual node source and stored calls derive both local clauses from strict child calls. -/
theorem node (expressions : List (EdgeSyntax Symbol Guard)) (captures : List (Value Symbol Guard))
    (firstName secondName : Reference) (reader common : State Symbol Guard)
    (relation : Value Symbol Guard → Value Symbol Guard → Prop)
    (first second : Environment Symbol Guard) (ready : Ready common)
    (firstInputs : Values common (.reference firstName :: captures))
    (secondInputs : Values common (.reference secondName :: captures))
    (firstReplacements : Replacements common first) (secondReplacements : Replacements common second)
    (children : ∀ (index : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard)),
      expressions[index]? = some (.mk symbol guard originals) →
      ∀ (childIndex : Nat) (child : Syntax Symbol Guard), originals[childIndex]? = some child →
        sizeOf child < sizeOf (.node expressions : Syntax Symbol Guard) →
        ∀ left right, build child (.reference firstName :: captures) common = .done left common →
          build child (.reference secondName :: captures) common = .done right common →
        ∀ output other, execute left first common = .done output common →
          execute right second common = .done other common →
          (output.referenceOf = .empty ↔ other.referenceOf = .empty) ∧ Mutual relation output other)
    (rawFirst rawSecond left right : Value Symbol Guard)
    (firstRaw : build (.node expressions) (.reference firstName :: captures) common = .done rawFirst common)
    (secondRaw : build (.node expressions) (.reference secondName :: captures) common = .done rawSecond common)
    (firstDone : execute rawFirst first common = .done left common)
    (secondDone : execute rawSecond second common = .done right common) :
    Local reader relation left right ∧ Local reader relation right left := by
  have valid := ready.semantic.1.normal.facts.coherent.valid
  have firstContext := SourceRecursiveIntersectionSemanticHeap.context common ready.semantic _ firstInputs
  have secondContext := SourceRecursiveIntersectionSemanticHeap.context common ready.semantic _ secondInputs
  have firstPlain := source_ordinary expressions _ common ready firstInputs rawFirst firstRaw
  have secondPlain := source_ordinary expressions _ common ready secondInputs rawSecond secondRaw
  have firstAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    ready.semantic.1.normal.facts firstInputs).result rawFirst common firstRaw
  have secondAvailable := (InternedFreshOrdinaryFacts.build_verified (.node expressions) _ common
    ready.semantic.1.normal.facts secondInputs).result rawSecond common secondRaw
  have leftPlain := stored_ordinary rawFirst left first common ready firstAvailable firstReplacements firstPlain firstDone
  have rightPlain := stored_ordinary rawSecond right second common ready secondAvailable secondReplacements secondPlain secondDone
  have childCases (index : Nat) (symbol : Symbol) (guard : Guard) (originals : List (Syntax Symbol Guard))
      (source : expressions[index]? = some (.mk symbol guard originals)) (child : Syntax Symbol Guard)
      (member : child ∈ originals) : Child relation common (.reference firstName :: captures)
        (.reference secondName :: captures) first second child := by
    obtain ⟨childIndex,found⟩ := List.mem_iff_getElem?.mp member
    apply children index symbol guard originals source childIndex child found
    have small := List.sizeOf_lt_of_mem member
    have rowSmall := List.sizeOf_lt_of_mem (List.mem_of_getElem? source)
    simp only [Syntax.node.sizeOf_spec,EdgeSyntax.mk.sizeOf_spec] at *
    omega
  have rawMatch (row : EdgeValue Symbol Guard) (selected : Row rawFirst row) :
      ∃ other, Row rawSecond other ∧ RowMatch (Executions relation common first second) row other := by
    obtain ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,originals,opposite,own,
      _,_,_,_,same,member,_,_,_,_,_⟩ := SourceCurrentPublicationNodeRowSurvival.node expressions captures
        secondName firstName common common common common common secondContext firstContext rawSecond rawFirst
        secondRaw firstRaw (grows_refl _) (grows_refl _) row ((ordinary_row rawFirst firstPlain row).mp selected)
    refine ⟨opposite.output,(ordinary_row rawSecond secondPlain _).mpr member,?_⟩
    rw [←same]
    exact raw_row_match expressions relation common _ _ first second valid index symbol guard originals
      secondRows firstRows secondAfter firstAfter own opposite (childCases index symbol guard originals own.source)
  have rawReverse (row : EdgeValue Symbol Guard) (selected : Row rawSecond row) :
      ∃ other, Row rawFirst other ∧ RowMatch (Executions relation common second first) row other := by
    obtain ⟨firstRows,firstAfter,secondRows,secondAfter,index,symbol,guard,originals,own,opposite,
      _,_,_,_,same,member,_,_,_,_,_⟩ := SourceCurrentPublicationNodeRowSurvival.node expressions captures
        firstName secondName common common common common common firstContext secondContext rawFirst rawSecond
        firstRaw secondRaw (grows_refl _) (grows_refl _) row ((ordinary_row rawSecond secondPlain row).mp selected)
    refine ⟨own.output,(ordinary_row rawFirst firstPlain _).mpr member,?_⟩
    rw [←same]
    have swapped (child : Syntax Symbol Guard) (member : child ∈ originals) :
        Child relation common (.reference secondName :: captures) (.reference firstName :: captures) second first child := by
      intro a b firstRaw secondRaw x y firstDone secondDone
      have facts := childCases index symbol guard originals own.source child member b a secondRaw firstRaw y x secondDone firstDone
      exact ⟨facts.1.symm,facts.2.2,facts.2.1⟩
    exact raw_row_match expressions relation common _ _ second first valid index symbol guard originals
      secondRows firstRows secondAfter firstAfter opposite own swapped
  have forward (a b result other : Value Symbol Guard) (env otherEnv : Environment Symbol Guard)
      (aPlain : Ordinary a) (resultPlain : Ordinary result)
      (aAvailable : Available common a) (bAvailable : Available common b)
      (envAvailable : Replacements common env) (otherAvailable : Replacements common otherEnv)
      (aDone : execute a env common = .done result common) (bDone : execute b otherEnv common = .done other common)
      (raw : ∀ row, Row a row → ∃ matched, Row b matched ∧ RowMatch (Executions relation common env otherEnv) row matched) :
      ∀ row ∈ nodeEdges result, ∃ matched, Origin reader [other] matched ∧ RowMatch (Mutual relation) row matched := by
    intro row member
    have parts := SourceCurrentStoredLiteralExecutionParts.parts a result env common ready aAvailable envAvailable aDone
    rcases (parts.2 row).mp ((ordinary_row result resultPlain row).mpr member) with
      ⟨source,literal,output,called,part⟩ | ⟨source,part,called,alive⟩
    · exact False.elim (no_literal a source aPlain literal)
    · obtain ⟨original,found,pair⟩ := raw source part
      obtain ⟨matched,otherCalls⟩ := SourceCurrentStoredLiteralExecutionParts.row b other otherEnv common ready
        bAvailable otherAvailable bDone original found
      have fields := stored_row_match relation common env otherEnv valid source original row matched pair called otherCalls
      have otherParts := SourceCurrentStoredLiteralExecutionParts.parts b other otherEnv common ready bAvailable otherAvailable bDone
      have otherRow : Row other matched := (otherParts.2 matched).mpr (Or.inr ⟨original,found,otherCalls,by
        change (!(matched.children.any (fun child => child.referenceOf == .empty))) = true
        rw [←children_empty relation fields.2.2]
        exact alive⟩)
      exact ⟨matched,row_origin reader otherRow,fields.1,fields.2.1,All₂.imp (fun _ _ facts => facts.2) fields.2.2⟩
  exact ⟨terminal_local reader relation left right leftPlain
      (forward rawFirst rawSecond left right first second firstPlain leftPlain firstAvailable secondAvailable
        firstReplacements secondReplacements firstDone secondDone rawMatch),
    terminal_local reader relation right left rightPlain
      (forward rawSecond rawFirst right left second first secondPlain rightPlain secondAvailable firstAvailable
        secondReplacements firstReplacements secondDone firstDone rawReverse)⟩

end MicroCFTA.SourceCurrentSourceDirectedCases
