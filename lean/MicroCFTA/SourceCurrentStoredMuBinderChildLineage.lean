import MicroCFTA.SourceCurrentStoredMuActiveChildLineage
import MicroCFTA.SourceCurrentNativeMuPublicationCallbacks

/-!
# Paired lexical inputs at actual reserved Mu bodies

An outer varying reference becomes a captured slot under a nested binder.
The two captured lists need not be physically equal. Paired slots retain
equal resolved references or the same opaque capture with compatible maps.
Actual publication misses derive freshness for the reserved local names.
This module does not compare completed binder results or earlier winners.
-/
namespace MicroCFTA.SourceCurrentStoredMuBinderChildLineage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction (build)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (Publication)
open Language

/-- References resolve equally; other slots retain one exact capture and agreement on its free names. -/
def Slot (first second : Environment Symbol Guard) : Value Symbol Guard → Value Symbol Guard → Prop
  | .reference a, .reference b => (first a).getD (.reference a) = (second b).getD (.reference b)
  | .reference _, _ | _, .reference _ => False
  | a, b => a = b ∧ ∀ name ∈ a.free, first name = second name

/-- Finite lexical inputs retain their source order under slot compatibility. -/
def Paired (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard)) : Prop :=
  All₂ (Slot first second) left right

/-- A local binding shadows the outer map at its exact original reference. -/
def bind (name : Reference) (value : Value Symbol Guard) (environment : Environment Symbol Guard) :
    Environment Symbol Guard := fun queried => if queried = name then some value else environment queried

private theorem fixed_slot (first second : Environment Symbol Guard) (value : Value Symbol Guard)
    (agree : ∀ name ∈ value.free, first name = second name) : Slot first second value value := by
  cases value with
  | reference name =>
      change (first name).getD _ = (second name).getD _
      rw [agree name (by simp [Value.free])]
  | empty | node | union | mu => exact ⟨rfl,agree⟩

/-- The existing one-varying-slot compatibility gives paired inputs without changing fixed captures. -/
theorem of_compatible (captures : List (Value Symbol Guard)) (firstName secondName : Reference)
    (first second : Environment Symbol Guard)
    (compatible : SourceCurrentStoredMuActiveChildLineage.Compatible captures firstName secondName first second) :
    Paired first second (.reference firstName :: captures) (.reference secondName :: captures) := by
  refine .cons compatible.1 ?_
  have same : ∀ values, (∀ value ∈ values, value ∈ captures) → All₂ (Slot first second) values values := by
    intro values included
    induction values with
    | nil => exact .nil
    | cons value rest ih =>
        exact .cons (fixed_slot first second value (compatible.2 value (included value List.mem_cons_self)))
          (ih (fun value member => included value (List.mem_cons_of_mem _ member)))
  exact same captures (fun _ member => member)

private theorem reference_execute [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (environment : Environment Symbol Guard) (state : State Symbol Guard) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]

private theorem slot_execute [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Environment Symbol Guard) (left right : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state left)
    (paired : Slot first second left right) : execute left first state = execute right second state := by
  cases left <;> cases right
  all_goals try {cases paired}
  case reference.reference a b =>
    rw [reference_execute,reference_execute,paired]
  all_goals obtain ⟨same,agree⟩ := paired
  all_goals cases same
  all_goals exact InternedFreshOrdinaryStoredSubstitution.execute_congr _ first second state coherent available agree

/-- Every actual indexed variable has identical repaired execution under paired lexical maps. -/
theorem reference [DecidableEq (EdgeKey Symbol Guard)] (first second : Environment Symbol Guard)
    (left right : List (Value Symbol Guard)) (paired : Paired first second left right)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Values state left) (index : Nat) :
    (build (.var index) left state).bind (fun value current => execute value first current) =
      (build (.var index) right state).bind (fun value current => execute value second current) := by
  simp only [build,Outcome.bind]
  induction paired generalizing index with
  | nil =>
      exact slot_execute first second .empty .empty state coherent (InternedProbeProvenance.empty_available state)
        (fixed_slot first second .empty (by simp [Value.free]))
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.getD_some]
          exact slot_execute first second _ _ state coherent (available _ List.mem_cons_self) head
      | succ index =>
          exact ih (fun value member => available value (List.mem_cons_of_mem _ member)) index

private theorem slot_bind (first second : Environment Symbol Guard) (left right : Value Symbol Guard)
    (paired : Slot first second left right) (firstName secondName : Reference) (argument : Value Symbol Guard)
    (firstFresh : firstName ∉ left.free) (secondFresh : secondName ∉ right.free) :
    Slot (bind firstName argument first) (bind secondName argument second) left right := by
  cases left <;> cases right
  all_goals try {cases paired}
  case reference.reference a b =>
    have firstDifferent : a ≠ firstName := by intro same; exact firstFresh (by simp [Value.free,same])
    have secondDifferent : b ≠ secondName := by intro same; exact secondFresh (by simp [Value.free,same])
    simpa only [Slot,bind,firstDifferent,secondDifferent,ite_false] using paired
  all_goals obtain ⟨same,agree⟩ := paired
  all_goals cases same
  all_goals
    refine ⟨rfl,?_⟩
    intro name member
    have left : name ≠ firstName := fun same => firstFresh (same ▸ member)
    have right : name ≠ secondName := fun same => secondFresh (same ▸ member)
    simp only [bind,left,right,ite_false,agree name member]

private theorem paired_bind (first second : Environment Symbol Guard) (left right : List (Value Symbol Guard))
    (paired : Paired first second left right) (firstName secondName : Reference) (argument : Value Symbol Guard)
    (firstFresh : ∀ value ∈ left, firstName ∉ value.free)
    (secondFresh : ∀ value ∈ right, secondName ∉ value.free) :
    Paired (bind firstName argument first) (bind secondName argument second)
      (.reference firstName :: left) (.reference secondName :: right) := by
  refine .cons ?_ ?_
  · simp only [Slot,bind,ite_true,Option.getD_some]
  · induction paired with
    | nil => exact .nil
    | cons head tail ih =>
        exact .cons (slot_bind first second _ _ head firstName secondName argument
          (firstFresh _ List.mem_cons_self) (secondFresh _ List.mem_cons_self))
          (ih (fun value member => firstFresh value (List.mem_cons_of_mem _ member))
            (fun value member => secondFresh value (List.mem_cons_of_mem _ member)))

private theorem publication_fresh [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    ∀ value ∈ event.environment, .interned event.entry.identity ∉ value.free := by
  intro value member
  have context := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have identity : event.entry.identity = event.cut.nodes.next :=
    InternedFreshProbeKeys.intern_miss_identity event.cut.nodes event.key event.missing
  rw [identity]
  exact InternedFreshProbeKeys.next_absent event.cut.nodes context.base.normal.facts.coherent.valid.2 value
    (context.base.inputs value member).issued

/-- Actual publication misses extend paired inputs and retain both literal reserved-body calls and filters. -/
theorem publication_extend [DecidableEq (EdgeKey Symbol Guard)]
    (firstEvent secondEvent : Publication (Symbol := Symbol) (Guard := Guard))
    (first second : Environment Symbol Guard)
    (paired : Paired first second firstEvent.environment secondEvent.environment)
    (argument : Value Symbol Guard) :
    (∀ value ∈ firstEvent.environment, .interned firstEvent.entry.identity ∉ value.free) ∧
    (∀ value ∈ secondEvent.environment, .interned secondEvent.entry.identity ∉ value.free) ∧
    Paired (bind (.interned firstEvent.entry.identity) argument first)
      (bind (.interned secondEvent.entry.identity) argument second)
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
  refine ⟨firstFresh,secondFresh,paired_bind first second _ _ paired _ _ argument firstFresh secondFresh,?_⟩
  obtain ⟨_,_,rawFirst,afterFirst,_,_,calledFirst,filteredFirst,_,growthFirst,_,_⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks firstEvent
  obtain ⟨_,_,rawSecond,afterSecond,_,_,calledSecond,filteredSecond,_,growthSecond,_,_⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks secondEvent
  exact ⟨rawFirst,afterFirst,rawSecond,afterSecond,calledFirst,filteredFirst,calledSecond,filteredSecond,
    growthFirst,growthSecond⟩

end MicroCFTA.SourceCurrentStoredMuBinderChildLineage
