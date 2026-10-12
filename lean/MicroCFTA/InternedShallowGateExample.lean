import MicroCFTA.InternedShallowGateRank

/-!
# A source-constructed open Mu in the ranked shallow fragment

The raw source binder retains an unused wrapper around external reference
999. Its actual cached body depth is zero. Its complete source cache state
inhabits the certified fragment, and unfolding exposes the reference.
-/
namespace MicroCFTA.InternedShallowGateExample
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedRequestFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredBodyInvariant InternedShallowHeap
open InternedBinderProtocol (NodeKey)

/-- Completing one depth-zero body extends a shallow state with another shallow Mu. -/
theorem complete_shallow (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (shallow : Shallow state)
    (zero : body.depth = 0) : Shallow (complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary stored
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
      (.mu actual actualBody actualDepth actualOrdinary) stored with old | ⟨_, equal⟩
  · exact shallow key actual actualBody actualDepth actualOrdinary old
  · cases equal
    exact zero

/-- The actual caller supplies an unresolved external source reference. -/
def external : Value Nat Unit := .reference (.uninterned 999)

/-- Raw source construction retains its unused wrapper. -/
def program : Syntax Nat Unit := .binder false (.var 1)

/-- Both actual probes normalize to the same external reference. -/
def key : NodeKey := muKey external external

/-- The source reserves its canonical entry before completing the body. -/
def reserved := Cache.intern (empty (Symbol := Nat) (Guard := Unit)).nodes key

/-- The actual raw completed payload stores the unchanged external body. -/
def record : Value Nat Unit := .mu reserved.1 external external external

/-- The exact source final state is obtained by the existing completion protocol. -/
def final : State Nat Unit :=
  (complete false reserved.1 external external external {empty with nodes := reserved.2}).state

/-- The fixture runs both source probes, reservation, and actual raw completion. -/
theorem source_return : build program [external] empty = .done record final := by cbv

/-- The generated source payload table contains only the one shallow Mu. -/
theorem source_shallow : Shallow final :=
  complete_shallow false reserved.1 external external external {empty with nodes := reserved.2} empty_shallow rfl

/-- The external source reference requires no interned identity reservation. -/
theorem source_inputs : Values (empty (Symbol := Nat) (Guard := Unit)) [external] := by
  intro value member
  have same : value = external := by simpa using member
  subst value
  exact ordinary_available empty 999

/-- The source execution derives every record and body-normalization premise. -/
def certified : InternedShallowGateRank.Node Nat Unit := by
  have checked := build_verified program [external] empty empty_facts source_inputs
  have facts : Facts final := by simpa [source_return, Outcome.state] using checked.facts
  have flat : Flat final := by simpa [source_return, Outcome.state] using build_flat program [external] empty empty_facts source_inputs empty_flat
  have clean : Clean final := by simpa [source_return, Outcome.state] using build_clean program [external] empty empty_facts source_inputs empty_flat empty_clean
  exact ⟨final, record, facts, flat, clean, source_shallow, checked.result record final source_return⟩

/-- This certified source Mu is open, so the gate really takes its unfolding branch. -/
theorem source_open : certified.value.free.isEmpty = false := by cbv

/-- The actual source adapter exposes the unchanged external reference in one step. -/
theorem source_unfold : InternedStoredSubstitution.unfold certified.value certified.state = .done external final := by cbv

/-- Its source head rank strictly decreases from one to zero. -/
theorem source_rank : InternedGateRank.headRank certified.value = 1 ∧
    InternedGateRank.headRank (InternedShallowGateRank.step certified).result.value = 0 := by
  have same := (InternedShallowGateRank.step certified).actual
  rw [source_unfold] at same
  have values := (Outcome.done.inj same).1
  constructor
  · cbv
  · rw [← values]
    rfl

end MicroCFTA.InternedShallowGateExample
