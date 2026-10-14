import MicroCFTA.SourceRecursiveIntersectionCodeBounds

/-!
# Strict request limits through source union and row walks

Ordered source walks retain each original request limit through every earlier
child effect. Final constructors receive actual returned values and machines.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Ordered source union code retains each original member's strict request limit. -/
theorem union_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value)
    (memberBounds : ∀ member ∈ members, if left then NodeBelow source holds bound ⟨domain, member, other⟩
      else NodeBelow source holds bound ⟨domain, other, member⟩) :
    Below source holds bound ((walk (fun member => if left then requestNode domain member other else requestNode domain other member) members).bind
      fun values => .work (makeUnion values) .pure) state := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value known
    exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
  have calls : ∀ member ∈ members, ∀ current, SourceRecursiveIntersectionKernel.Valid current → input current member →
      Safe (if left then requestNode domain member other else requestNode domain other member) current (fun after value => Available after.heap value) := by
    intro member _ current _ known
    cases left
    · exact safe_requestNode domain other member current ⟨known.1, known.2.1, known.2.2⟩
    · exact safe_requestNode domain member other current ⟨known.1, known.2.2, known.2.1⟩
  have inputs : ∀ member ∈ members, input state member := fun member present => ⟨known, available, membersAvailable member present⟩
  have built := safe_walk (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable calls state valid inputs
  have bounded := below_walk source holds bound
    (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable calls (by
      intro member present current _ _
      have retained := memberBounds member present
      cases left
      · exact below_requestNode source holds bound _ current retained
      · exact below_requestNode source holds bound _ current retained) state valid inputs
  exact below_bind source holds bound _ _ state valid _ built bounded
    (fun values after _ _ _ => below_work source holds bound _ after)

/-- Actual source hash-join code retains every original row request's strict limit. -/
theorem compileRows_below [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge) (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge)
    (rowBounds : ∀ rows ∈ pairs left right, EdgeBelow source holds bound ⟨domain, rows.1, rows.2⟩) :
    Below source holds bound (compileRows domain left right) state := by
  let input := fun (current : Machine Symbol Guard) (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap rows.1 ∧ EdgeResident current.heap rows.2
  have stable : Stable input := by
    intro before after growth rows known
    exact ⟨known.1.grows _ growth, edge_grows _ _ growth.heap _ known.2.1, edge_grows _ _ growth.heap _ known.2.2⟩
  have calls : ∀ rows ∈ pairs left right, ∀ current, SourceRecursiveIntersectionKernel.Valid current → input current rows →
      Safe (requestEdge domain rows.1 rows.2) current (fun after value => EdgeResident after.heap value) := by
    intro rows _ current _ known
    exact safe_requestEdge domain rows.1 rows.2 current known
  have inputs : ∀ rows ∈ pairs left right, input state rows := by
    intro rows member
    obtain ⟨first, second, _⟩ := (pairs_member left right rows).mp member
    exact ⟨known, leftResident rows.1 first, rightResident rows.2 second⟩
  have built := safe_walk (fun rows => requestEdge domain rows.1 rows.2) (pairs left right) input _ stable edge_stable calls state valid inputs
  have bounded := below_walk source holds bound (fun rows => requestEdge domain rows.1 rows.2) (pairs left right) input _ stable edge_stable calls
    (fun rows member current _ _ => below_requestEdge source holds bound _ current (rowBounds rows member)) state valid inputs
  exact below_bind source holds bound _ _ state valid _ built bounded
    (fun values after _ _ _ => below_work source holds bound _ after)

end MicroCFTA.SourceRecursiveIntersectionCode
