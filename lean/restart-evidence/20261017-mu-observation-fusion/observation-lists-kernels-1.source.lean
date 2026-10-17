import MicroCFTA.SourceCurrentOpenObservationLists

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.ObservationListsKernels
open InternedConstructorTemplates SourceCurrentOpenObservations SourceCurrentOpenObservationLists
open InternedBinderProtocol (Reference NodeKey)

/-- Literal union expansion composes with a duplicated and reordered open root list. -/
theorem union_and_duplicate (depth : Nat) (view : State Nat Bool)
    (entry : Cache.Interned NodeKey) (members : List (Value Nat Bool)) (level : Nat)
    (free : List Reference) (first second : Value Nat Bool) :
    Same depth view ([.union entry members level free] ++ [first,second,first])
      (members ++ [second,first]) := by
  apply SourceCurrentOpenObservationLists.append depth view _ _ _ _
  · exact SourceCurrentOpenObservations.union depth view entry members level free
  · apply of_members
    intro value
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto

#check @union_and_duplicate
#print axioms union_and_duplicate
end MicroCFTA.ObservationListsKernels
