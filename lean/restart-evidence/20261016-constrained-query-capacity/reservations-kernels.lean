import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations

namespace MicroCFTA.ReservationIntegration
open Cache InternedConstructorTemplates
open SourceCurrentAllocatedFiniteOrdinaryReservations

def repeatedConstructors : Work Nat Unit (Value Nat Unit) :=
  (makeEdge 7 () []).bind fun edge =>
  (makeNode [edge]).bind fun value =>
  (makeEdge 7 () []).bind fun repeated =>
  (makeNode [repeated]).bind fun _ => .pure value

/-- Repeated literal constructors request twice but reserve once in each family. -/
theorem repeated_requests :
    let before : State Nat Unit := empty
    let requests := observe repeatedConstructors before
    (run repeatedConstructors before).2.nodes.next = 1 ∧
    (run repeatedConstructors before).2.edges.next = 1 ∧
    nodeRequests requests = 2 ∧ edgeRequests requests = 2 ∧
    nodeReservations requests = 1 ∧ edgeReservations requests = 1 := by
  simp [repeatedConstructors, observe, nodeRequests, edgeRequests, nodeReservations, edgeReservations,
    makeEdge, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds,
    run, Work.bind, edgeStep, nodeStep, Cache.intern, Cache.install, Cache.reserve, Cache.keepFirst,
    Cache.put, empty, Cache.emptyState, identifyNode, maximumDepth, childFree, canonicalFree,
    Value.referenceOf, EdgeValue.children, EdgeValue.entry, List.eraseDups_cons]

/-- Removing an edge with an empty child makes no node request or reservation. -/
theorem filtered_constructor :
    let work : Work Nat Unit (Value Nat Unit) :=
      (makeEdge 9 () [.empty]).bind fun edge => makeNode [edge]
    let before : State Nat Unit := empty
    (run work before).1 = .empty ∧
    (run work before).2.nodes.next = 0 ∧
    (run work before).2.edges.next = 1 ∧
    nodeRequests (observe work before) = 0 := by
  simp [observe, nodeRequests, makeEdge, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds,
    run, Work.bind, edgeStep, Cache.intern, Cache.install, Cache.reserve, Cache.keepFirst,
    Cache.put, empty, Cache.emptyState, Value.referenceOf, EdgeValue.children]

/-- Two issued candidates consume two identities although one canonical entry wins. -/
theorem losing_candidate :
    let initial : Cache.State Nat := Cache.emptyState
    let first := Cache.reserve initial 7
    let second := Cache.reserve first.2 7
    let winner := Cache.install second.2 first.1
    let after := Cache.install winner second.1
    AtomicTrace initial after 2 ∧
    after.next = initial.next + 2 ∧
    after.table 7 = some ⟨0, 7⟩ ∧
    after.issued 0 = some 7 ∧ after.issued 1 = some 7 := by
  dsimp only
  have firstIssued : (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).2.issued
      (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).1.identity =
      some (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).1.key := by decide
  have secondIssued :
      (Cache.install (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).2
        (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).1).issued
        (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).1.identity =
      some (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).1.key := by decide
  have actual : AtomicTrace (Cache.emptyState : Cache.State Nat)
      (Cache.install
        (Cache.install (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).2
          (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).1)
        (Cache.reserve (Cache.reserve (Cache.emptyState : Cache.State Nat) 7).2 7).1) 2 :=
    .install (.install (.reserve (.reserve (.refl _) 7) 7) _ firstIssued) _ secondIssued
  refine ⟨actual, actual.next_exact, ?_⟩
  decide

/-- A replay uses the same actual return and consumes no further reservation. -/
theorem warm_replay {Symbol Guard Output : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (work : Work Symbol Guard Output) (before : State Symbol Guard) (valid : Valid before) :
    let after := (run work before).2
    run work after = ((run work before).1, after) ∧
    nodeReservations (observe work after) = 0 ∧
    edgeReservations (observe work after) = 0 ∧
    Extends before.nodes.issued after.nodes.issued ∧
    Extends before.edges.issued after.edges.issued := by
  dsimp only
  have replayed := replay work before (run work before).2 valid (grows_refl _)
  have counted := run_next work (run work before).2
  rw [replayed] at counted
  dsimp only at counted
  have retained := run_issued work before valid
  refine ⟨replayed, ?_, ?_, retained⟩ <;> omega

end MicroCFTA.ReservationIntegration

#print axioms MicroCFTA.ReservationIntegration.repeated_requests
#check @MicroCFTA.ReservationIntegration.repeated_requests
#print axioms MicroCFTA.ReservationIntegration.filtered_constructor
#check @MicroCFTA.ReservationIntegration.filtered_constructor
#print axioms MicroCFTA.ReservationIntegration.losing_candidate
#check @MicroCFTA.ReservationIntegration.losing_candidate
#print axioms MicroCFTA.ReservationIntegration.warm_replay
#check @MicroCFTA.ReservationIntegration.warm_replay
