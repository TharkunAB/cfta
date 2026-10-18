import MicroCFTA.SourceCurrentFixedReaderUnionFragments
import MicroCFTA.SourceCurrentLiteralNormalizationSimulation

/-!
# Union clauses from actual fragments at the original reader

Each fragment obligation receives the exact strict source member and both
historical source calls. Atom obligations compare actual atom outputs.
Row obligations compare full reconstructed rows. Neither obligation needs
a warm filter or stored call for a whole original subgroup.
The atom and row obligations remain explicit premises.
-/
namespace MicroCFTA.SourceCurrentFixedReaderUnionClauses
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build buildMany)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentLiteralRootParts (Literal Row)
open SourceCurrentStoredNodeExpansion (RowCalls)
open SourceCurrentLiteralLocalSimulation (Clauses)
open SourceCurrentLiteralNormalizationSimulation (Relation)
open SourceCurrentSourceDirectedCases (Below)
open SourceCurrentOpenPreorderSimulation (Mutual)
open SourceCurrentOpenObservations (RowMatch)
open MergedFreshOrdinaryGraph (Origin successors)
open Productivity (Reachable)
open SourceEqualityRequiredCache (Ready)

/-- A strict member retains its historical call and its actual source replay. -/
def SourceCall [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (reader : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ before after, Context before inputs ∧ build expression inputs before = .done value after ∧
    Grows after reader ∧ build expression inputs reader = .done value reader

private theorem at_left {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (index : Nat) (value : α) (found : first[index]? = some value) :
    ∃ other, second[index]? = some other ∧ relation value other := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | @cons head other first second pair rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst value
          exact ⟨other,rfl,pair⟩
      | succ index => exact ih index found

private theorem at_right {α β : Type} {relation : α → β → Prop} {first : List α} {second : List β}
    (paired : All₂ relation first second) (index : Nat) (value : β) (found : second[index]? = some value) :
    ∃ other, first[index]? = some other ∧ relation other value := by
  induction paired generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | @cons head other first second pair rest ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst value
          exact ⟨head,rfl,pair⟩
      | succ index => exact ih index found

private theorem row_origin [DecidableEq (EdgeKey Symbol Guard)]
    (reader : State Symbol Guard) {root : Value Symbol Guard}
    {row : EdgeValue Symbol Guard} (found : Row root row) : Origin reader [root] row := by
  induction found with
  | node member => exact ⟨_,.seed List.mem_cons_self,member⟩
  | @union entry members level free value row member found ih =>
      exact ih.from_seeds reader [value] [.union entry members level free]
        (fun current present => (List.mem_singleton.mp present) ▸
          Reachable.step (Reachable.seed List.mem_cons_self) member) row

private theorem compose_children {source : Value Symbol Guard → Value Symbol Guard → Prop}
    {first middle last : List (Value Symbol Guard)}
    (left : All₂ (Mutual (Relation source)) first middle)
    (right : All₂ (Mutual Below) middle last) :
    All₂ (Mutual (Relation source)) first last := by
  induction left generalizing last with
  | nil => cases right; exact .nil
  | cons pair tail ih =>
      cases right with
      | cons next rest => exact .cons ⟨pair.1.post next.1,Relation.pre next.2 pair.2⟩ (ih rest)

private theorem post_below [DecidableEq (EdgeKey Symbol Guard)] (reader : State Symbol Guard)
    (source : Value Symbol Guard → Value Symbol Guard → Prop) {first middle last : Value Symbol Guard}
    (clauses : Clauses reader (Relation source) first middle) (included : Below middle last) :
    Clauses reader (Relation source) first last := by
  have normalization := SourceCurrentSourceDirectedCases.below_directed reader
  refine ⟨?_,?_,?_⟩
  · intro name found
    exact normalization.reference reader Below included name (clauses.1 name found)
  · intro row found
    obtain ⟨other,origin,fields⟩ := clauses.2.1 row found
    obtain ⟨final,reached,later⟩ := normalization.row reader Below included other origin
    exact ⟨final,reached,fields.1.trans later.1,fields.2.1.trans later.2.1,
      compose_children fields.2.2 later.2.2⟩
  · intro entry body depth ordinary found next member
    obtain ⟨endpoint,reached,related⟩ := clauses.2.2 entry body depth ordinary found next member
    obtain ⟨initial,present,steps,path⟩ :=
      SourceCurrentOpenOriginSteps.path_of_reachable reader [middle] endpoint reached
    obtain rfl := List.mem_singleton.mp present
    obtain ⟨final,finished,fragment⟩ := normalization.path reader Below included path
    exact ⟨final,finished,related.post fragment⟩

/-- Strict source fragment clauses derive the parent clauses at the original reader. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (firstInputs secondInputs : List (Value Symbol Guard))
    (firstBefore firstAfter secondBefore secondAfter reader : State Symbol Guard)
    (firstContext : Context firstBefore firstInputs) (secondContext : Context secondBefore secondInputs)
    (rawFirst rawSecond : Value Symbol Guard)
    (firstBuild : build (.union expressions) firstInputs firstBefore = .done rawFirst firstAfter)
    (secondBuild : build (.union expressions) secondInputs secondBefore = .done rawSecond secondAfter)
    (ready : Ready reader) (firstGrowth : Grows firstAfter reader) (secondGrowth : Grows secondAfter reader)
    (firstAvailable : Available reader rawFirst) (secondAvailable : Available reader rawSecond)
    (firstOwn secondOwn : Reference) (firstMap secondMap : Environment Symbol Guard)
    (firstReplacements : Replacements reader firstMap) (secondReplacements : Replacements reader secondMap)
    (firstFiltered secondFiltered left right : Value Symbol Guard)
    (firstFilter : run (withoutSelfReference firstOwn rawFirst) reader = (firstFiltered,reader))
    (secondFilter : run (withoutSelfReference secondOwn rawSecond) reader = (secondFiltered,reader))
    (firstDone : execute firstFiltered firstMap reader = .done left reader)
    (secondDone : execute secondFiltered secondMap reader = .done right reader)
    (firstValues secondValues : List (Value Symbol Guard))
    (firstMany : buildMany expressions firstInputs reader = .done firstValues reader)
    (secondMany : buildMany expressions secondInputs reader = .done secondValues reader)
    (source : Value Symbol Guard → Value Symbol Guard → Prop)
    (atoms : ∀ (index : Nat) (expression : Syntax Symbol Guard) (firstMember secondMember : Value Symbol Guard),
      expressions[index]? = some expression →
      firstValues[index]? = some firstMember → secondValues[index]? = some secondMember →
      SourceCall expression firstInputs reader firstMember → SourceCall expression secondInputs reader secondMember →
      ∀ atom output, Literal firstMember atom → (rawFirst = .reference firstOwn ∨ atom ≠ .reference firstOwn) →
      execute atom firstMap reader = .done output reader →
      ∃ other endpoint, Literal secondMember other ∧
        (rawSecond = .reference secondOwn ∨ other ≠ .reference secondOwn) ∧
        execute other secondMap reader = .done endpoint reader ∧
        Clauses reader (Relation source) output endpoint)
    (rows : ∀ (index : Nat) (expression : Syntax Symbol Guard) (firstMember secondMember : Value Symbol Guard),
      expressions[index]? = some expression →
      firstValues[index]? = some firstMember → secondValues[index]? = some secondMember →
      SourceCall expression firstInputs reader firstMember → SourceCall expression secondInputs reader secondMember →
      ∀ original output, Row firstMember original → RowCalls firstMap reader original output →
      (!(output.children.any (fun child => child.referenceOf == .empty))) = true →
      ∃ other rebuilt, Row secondMember other ∧ RowCalls secondMap reader other rebuilt ∧
        (!(rebuilt.children.any (fun child => child.referenceOf == .empty))) = true ∧
        RowMatch (Mutual (Relation source)) output rebuilt) :
    Clauses reader (Relation source) left right := by
  obtain ⟨valuesA,middleA,_manyA,_contextA,_madeA,_growthA,_availableA,warmA,_madeWarmA,sourcesA,
    literalsA,rowsA,_atomsA,_callsA⟩ := SourceCurrentFixedReaderUnionFragments.source expressions firstInputs
      firstBefore firstAfter reader firstContext rawFirst firstBuild ready firstGrowth firstAvailable
      firstOwn firstMap firstReplacements firstFiltered left firstFilter firstDone
  obtain ⟨valuesB,middleB,_manyB,_contextB,_madeB,_growthB,_availableB,warmB,_madeWarmB,sourcesB,
    literalsB,rowsB,_atomsB,_callsB⟩ := SourceCurrentFixedReaderUnionFragments.source expressions secondInputs
      secondBefore secondAfter reader secondContext rawSecond secondBuild ready secondGrowth secondAvailable
      secondOwn secondMap secondReplacements secondFiltered right secondFilter secondDone
  have sameA := (Outcome.done.inj (warmA.symm.trans firstMany)).1
  have sameB := (Outcome.done.inj (warmB.symm.trans secondMany)).1
  subst valuesA
  subst valuesB
  have atomic (index : Nat) (member atom output : Value Symbol Guard)
      (selected : firstValues[index]? = some member) (part : Literal member atom)
      (retained : rawFirst = .reference firstOwn ∨ atom ≠ .reference firstOwn)
      (called : execute atom firstMap reader = .done output reader) :
      Clauses reader (Relation source) output right := by
    obtain ⟨expression,selectedExpression,firstSource⟩ := at_right sourcesA index member selected
    obtain ⟨secondMember,secondSelected,secondSource⟩ := at_left sourcesB index expression selectedExpression
    obtain ⟨other,endpoint,otherPart,otherRetained,otherCall,clauses⟩ :=
      atoms index expression member secondMember selectedExpression selected secondSelected
        firstSource secondSource atom output part retained called
    have included : Below endpoint right := ⟨
      fun found inside => (literalsB found).mpr
        ⟨index,secondMember,other,endpoint,secondSelected,otherPart,otherRetained,otherCall,inside⟩,
      fun found inside => (rowsB found).mpr (Or.inl
        ⟨index,secondMember,other,endpoint,secondSelected,otherPart,otherRetained,otherCall,inside⟩)⟩
    exact post_below reader source clauses included
  refine ⟨?_,?_,?_⟩
  · intro name found
    obtain ⟨index,member,atom,output,selected,part,retained,called,inside⟩ := (literalsA _).mp found
    exact (atomic index member atom output selected part retained called).1 name inside
  · intro row found
    rcases (rowsA row).mp found with atom | ordinary
    · obtain ⟨index,member,atom,output,selected,part,retained,called,inside⟩ := atom
      exact (atomic index member atom output selected part retained called).2.1 row inside
    · obtain ⟨index,member,original,selected,part,called,alive⟩ := ordinary
      obtain ⟨expression,selectedExpression,firstSource⟩ := at_right sourcesA index member selected
      obtain ⟨secondMember,secondSelected,secondSource⟩ := at_left sourcesB index expression selectedExpression
      obtain ⟨other,rebuilt,otherPart,otherCall,otherAlive,matched⟩ :=
        rows index expression member secondMember selectedExpression selected secondSelected
          firstSource secondSource original row part called alive
      exact ⟨rebuilt,row_origin reader ((rowsB rebuilt).mpr (Or.inr
        ⟨index,secondMember,other,secondSelected,otherPart,otherCall,otherAlive⟩)),matched⟩
  · intro entry body depth ordinary found next member
    obtain ⟨index,value,atom,output,selected,part,retained,called,inside⟩ := (literalsA _).mp found
    exact (atomic index value atom output selected part retained called).2.2 entry body depth ordinary inside next member

end MicroCFTA.SourceCurrentFixedReaderUnionClauses
