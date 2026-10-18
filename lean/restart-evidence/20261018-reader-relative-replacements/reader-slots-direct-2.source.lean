import MicroCFTA.SourceCurrentReaderObservations
import MicroCFTA.SourceCurrentStoredMuBinderChildLineage

/-!
# Distinct related replacements at one reader

Reference slots can resolve to distinct values with the same observations
at the reader. Other slots retain one capture and equal maps on its free
names. Actual publication freshness permits two related local replacements.
The result does not compare completed binders or earlier stored winners.
-/
namespace MicroCFTA.SourceCurrentReaderReplacementSlots
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentReaderObservations (Related)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Resolved references relate at the reader; opaque captures retain equal free-name bindings. -/
def Slot (reader : State Symbol Guard) (first second : Environment Symbol Guard) :
    Value Symbol Guard → Value Symbol Guard → Prop
  | .reference a, .reference b => Related reader ((first a).getD (.reference a)) ((second b).getD (.reference b))
  | .reference _, _ | _, .reference _ => False
  | a, b => a = b ∧ ∀ name ∈ a.free, first name = second name

/-- Ordered lexical slots can resolve to distinct related values at one reader. -/
def Paired (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) : Prop := All₂ (Slot reader first second) left right

private theorem fixed_slot (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (value : Value Symbol Guard) (agree : ∀ name ∈ value.free, first name = second name) :
    Slot reader first second value value := by
  cases value with
  | reference name =>
      change Related reader ((first name).getD _) ((second name).getD _)
      rw [agree name (by simp [Value.free])]
      exact Related.refl reader _
  | empty | node | union | mu => exact ⟨rfl,agree⟩

/-- Existing equal-resolution slots embed into the reader-relative relation. -/
theorem of_equal (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard))
    (paired : SourceCurrentStoredMuBinderChildLineage.Paired first second left right) :
    Paired reader first second left right := by
  induction paired with
  | nil => exact .nil
  | @cons left right lefts rights slot tail ih =>
      refine .cons ?_ ih
      cases left <;> cases right
      all_goals try {cases slot}
      case reference.reference a b =>
          change Related reader ((first a).getD _) ((second b).getD _)
          change (first a).getD _ = (second b).getD _ at slot
          rw [slot]
          exact Related.refl reader _
      all_goals exact slot

private theorem reference_execute (name : Reference) (environment : Environment Symbol Guard)
    (state : State Symbol Guard) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]

private theorem slot_result (reader : State Symbol Guard) (coherent : Coherent reader)
    (first second : Environment Symbol Guard) (left right : Value Symbol Guard)
    (available : Available reader left) (paired : Slot reader first second left right)
    (result other : Value Symbol Guard) (after later : State Symbol Guard)
    (called : execute left first reader = .done result after)
    (returned : execute right second reader = .done other later) :
    Related reader result other ∧ after = later := by
  cases left <;> cases right
  all_goals try {cases paired}
  case reference.reference a b =>
      rw [reference_execute] at called returned
      obtain ⟨rfl,rfl⟩ := Outcome.done.inj called
      obtain ⟨rfl,rfl⟩ := Outcome.done.inj returned
      exact ⟨paired,rfl⟩
  all_goals obtain ⟨same,agree⟩ := paired
  all_goals cases same
  all_goals
    have equal := InternedFreshOrdinaryStoredSubstitution.execute_congr _ first second reader coherent available agree
    rw [called,returned] at equal
    obtain ⟨rfl,rfl⟩ := Outcome.done.inj equal
    exact ⟨Related.refl reader _,rfl⟩

/-- Actual variable reconstructions retain reader observations and their exact common output heap. -/
theorem reference (reader : State Symbol Guard) (coherent : Coherent reader)
    (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (paired : Paired reader first second left right) (available : Values reader left) (index : Nat)
    (result other : Value Symbol Guard) (after later : State Symbol Guard)
    (called : (build (.var index) left reader).bind (fun value current => execute value first current) = .done result after)
    (returned : (build (.var index) right reader).bind (fun value current => execute value second current) = .done other later) :
    Related reader result other ∧ after = later := by
  simp only [build,Outcome.bind] at called returned
  induction paired generalizing index with
  | nil =>
      exact slot_result reader coherent first second .empty .empty (empty_available reader)
        (fixed_slot reader first second .empty (by simp [Value.free])) result other after later called returned
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.getD_some] at called returned
          exact slot_result reader coherent first second _ _ (available _ List.mem_cons_self) head
            result other after later called returned
      | succ index =>
          exact ih (fun value member => available value (List.mem_cons_of_mem _ member)) index called returned

private theorem slot_bind (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : Value Symbol Guard) (paired : Slot reader first second left right)
    (firstName secondName : Reference) (firstValue secondValue : Value Symbol Guard)
    (firstFresh : firstName ∉ left.free) (secondFresh : secondName ∉ right.free) :
    Slot reader (bind firstName firstValue first) (bind secondName secondValue second) left right := by
  cases left <;> cases right
  all_goals try {cases paired}
  case reference.reference a b =>
      have firstDifferent : a ≠ firstName := by intro same; exact firstFresh (by simp [Value.free,same])
      have secondDifferent : b ≠ secondName := by intro same; exact secondFresh (by simp [Value.free,same])
      simpa only [Slot,SourceCurrentStoredMuBinderChildLineage.bind,firstDifferent,secondDifferent,ite_false] using paired
  all_goals obtain ⟨same,agree⟩ := paired
  all_goals cases same
  all_goals
    refine ⟨rfl,?_⟩
    intro name member
    have left : name ≠ firstName := fun same => firstFresh (same ▸ member)
    have right : name ≠ secondName := fun same => secondFresh (same ▸ member)
    simp only [SourceCurrentStoredMuBinderChildLineage.bind,left,right,ite_false,agree name member]

/-- Fresh local names extend paired captures with two related replacement values. -/
theorem extend (reader : State Symbol Guard) (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) (paired : Paired reader first second left right)
    (firstName secondName : Reference) (firstValue secondValue : Value Symbol Guard)
    (related : Related reader firstValue secondValue)
    (firstFresh : ∀ value ∈ left, firstName ∉ value.free)
    (secondFresh : ∀ value ∈ right, secondName ∉ value.free) :
    Paired reader (bind firstName firstValue first) (bind secondName secondValue second)
      (.reference firstName :: left) (.reference secondName :: right) := by
  refine .cons ?_ ?_
  · simpa only [Slot,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,Option.getD_some] using related
  · induction paired with
    | nil => exact .nil
    | cons head tail ih =>
        exact .cons (slot_bind reader first second _ _ head firstName secondName firstValue secondValue
          (firstFresh _ List.mem_cons_self) (secondFresh _ List.mem_cons_self))
          (ih (fun value member => firstFresh value (List.mem_cons_of_mem _ member))
            (fun value member => secondFresh value (List.mem_cons_of_mem _ member)))

private theorem publication_fresh (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    ∀ value ∈ event.environment, .interned event.entry.identity ∉ value.free := by
  intro value member
  have context := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have identity : event.entry.identity = event.cut.nodes.next :=
    InternedFreshProbeKeys.intern_miss_identity event.cut.nodes event.key event.missing
  rw [identity]
  exact InternedFreshProbeKeys.next_absent event.cut.nodes context.base.normal.facts.coherent.valid.2 value
    (context.base.inputs value member).issued

/-- Actual publications derive fresh bindings for distinct related arguments and retain both raw callbacks. -/
theorem publication_extend (reader : State Symbol Guard)
    (firstEvent secondEvent : Publication (Symbol := Symbol) (Guard := Guard))
    (first second : Environment Symbol Guard)
    (paired : Paired reader first second firstEvent.environment secondEvent.environment)
    (firstValue secondValue : Value Symbol Guard) (related : Related reader firstValue secondValue) :
    (∀ value ∈ firstEvent.environment, .interned firstEvent.entry.identity ∉ value.free) ∧
    (∀ value ∈ secondEvent.environment, .interned secondEvent.entry.identity ∉ value.free) ∧
    Paired reader (bind (.interned firstEvent.entry.identity) firstValue first)
      (bind (.interned secondEvent.entry.identity) secondValue second)
      (.reference (.interned firstEvent.entry.identity) :: firstEvent.environment)
      (.reference (.interned secondEvent.entry.identity) :: secondEvent.environment) ∧
    ∃ rawFirst afterFirst rawSecond afterSecond,
      build firstEvent.expression (.reference (.interned firstEvent.entry.identity) :: firstEvent.environment)
        firstEvent.allocated = .done rawFirst afterFirst ∧
      run (withoutSelfReference (.interned firstEvent.entry.identity) rawFirst) afterFirst =
        (firstEvent.body,firstEvent.afterBody) ∧
      build secondEvent.expression (.reference (.interned secondEvent.entry.identity) :: secondEvent.environment)
        secondEvent.allocated = .done rawSecond afterSecond ∧
      run (withoutSelfReference (.interned secondEvent.entry.identity) rawSecond) afterSecond =
        (secondEvent.body,secondEvent.afterBody) ∧
      Grows afterFirst firstEvent.afterBody ∧ Grows afterSecond secondEvent.afterBody := by
  have firstFresh := publication_fresh firstEvent
  have secondFresh := publication_fresh secondEvent
  refine ⟨firstFresh,secondFresh,extend reader first second _ _ paired _ _ _ _ related firstFresh secondFresh,?_⟩
  obtain ⟨_,_,rawFirst,afterFirst,_,_,calledFirst,filteredFirst,_,growthFirst,_,_⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks firstEvent
  obtain ⟨_,_,rawSecond,afterSecond,_,_,calledSecond,filteredSecond,_,growthSecond,_,_⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks secondEvent
  exact ⟨rawFirst,afterFirst,rawSecond,afterSecond,calledFirst,filteredFirst,calledSecond,filteredSecond,
    growthFirst,growthSecond⟩

end MicroCFTA.SourceCurrentReaderReplacementSlots
