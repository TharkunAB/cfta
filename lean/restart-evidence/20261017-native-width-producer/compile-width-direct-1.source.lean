import MicroCFTA.SourceRecursiveIntersectionCodeMass
import MicroCFTA.SourceRecursiveIntersectionCompileMass
import MicroCFTA.SourceRecursiveIntersectionCompileSafety

/-!
# Quantitative input certificates for every compiled node branch

The original available operands determine every row and member width.
Ordered requests retain their exact list length. Each continuation accepts
an increasing causal store bound at its actual returned machine.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCompileWidth
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionCodeMass
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Guard : Type} {bound : Nat}

private theorem bound_square (bound : Nat) (positive : 1 ≤ bound) : bound ≤ bound * bound := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left bound positive

/-- An original available union bounds every emitted member position. -/
theorem union_width (state : InternedConstructorTemplates.State Symbol Guard)
    (stored : Stored bound state) (entry) (members : List (Value Symbol Guard)) (level free)
    (available : Available state (.union entry members level free)) : members.length ≤ bound * bound := by
  have mass := InternedValueMassHeap.available state stored (.union entry members level free) available
  have positions := SourceRecursiveIntersectionCompileMass.values_length members
  simp only [InternedValueMass.value] at mass
  exact Nat.le_trans (by omega) (bound_square bound stored.positive)

/-- The two original available nodes bound the complete matched row schedule. -/
theorem rows_width [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard)
    (stored : Stored bound state) (left right : Value Symbol Guard)
    (leftAvailable : Available state left) (rightAvailable : Available state right) :
    (pairs (nodeEdges left) (nodeEdges right)).length ≤ bound * bound :=
  Nat.le_trans (SourceRecursiveIntersectionCompileMass.node_pairs_mass left right)
    (Nat.mul_le_mul (InternedValueMassHeap.available state stored left leftAvailable)
      (InternedValueMassHeap.available state stored right rightAvailable))

section Compiler
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual row walk retains its original count through every physically valid recursive return. -/
theorem compileRows (domain : Interned DomainKey) (left right : List (EdgeValue Symbol Guard))
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) (known : Domain state domain)
    (leftResident : ∀ row ∈ left, EdgeResident state.heap row)
    (rightResident : ∀ row ∈ right, EdgeResident state.heap row)
    (width : (pairs left right).length ≤ bound * bound) :
    At (SourceRecursiveIntersectionCode.compileRows domain left right) state bound
      (fun after value => Available after.heap value) := by
  let input := fun (current : Machine Symbol Guard) (rows : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain current domain ∧ EdgeResident current.heap rows.1 ∧ EdgeResident current.heap rows.2
  have stable : Stable input := by
    intro before after growth rows ready
    exact ⟨ready.1.grows domain growth, edge_grows _ _ growth.heap _ ready.2.1,
      edge_grows _ _ growth.heap _ ready.2.2⟩
  have original : ∀ rows ∈ pairs left right, input state rows := by
    intro rows member
    have included := (pairs_member left right rows).mp member
    exact ⟨known, leftResident rows.1 included.1, rightResident rows.2 included.2.1⟩
  have walked := SourceRecursiveIntersectionCodeMass.walk (fun rows => requestEdge domain rows.1 rows.2)
    (pairs left right) input _ stable edge_stable
    (fun rows _ current currentBound _ _ ready => request_edge domain rows.1 rows.2 current currentBound ready)
    state bound valid stored original
  apply SourceRecursiveIntersectionCodeMass.bind _ _ state bound valid stored _ _ walked
  intro rows after larger afterValid _ enough current outputs
  apply SourceRecursiveIntersectionCodeMass.node rows after larger afterValid outputs.2
  rw [outputs.1]
  exact Nat.le_trans width (Nat.mul_le_mul enough enough)

/-- The actual union walk retains one output for each immutable original member. -/
theorem compileUnion (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : Stored bound state.heap)
    (known : Domain state domain) (available : Available state.heap other)
    (membersAvailable : ∀ value ∈ members, Available state.heap value) (width : members.length ≤ bound * bound) :
    At ((SourceRecursiveIntersectionCode.walk (fun member => if left then requestNode domain member other
      else requestNode domain other member) members).bind fun values => .work (makeUnion values) .pure)
      state bound (fun after value => Available after.heap value) := by
  let input := fun (current : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain current domain ∧ Available current.heap other ∧ Available current.heap value
  have stable : Stable input := by
    intro before after growth value ready
    exact ⟨ready.1.grows domain growth, growth.available _ ready.2.1, growth.available _ ready.2.2⟩
  have calls : ∀ member ∈ members, ∀ current currentBound, SourceRecursiveIntersectionKernel.Valid current →
      Stored currentBound current.heap → input current member →
      At (if left then requestNode domain member other else requestNode domain other member) current currentBound
        (fun after value => Available after.heap value) := by
    intro member _ current currentBound _ _ ready
    cases left
    · exact request_node domain other member current currentBound ⟨ready.1, ready.2.1, ready.2.2⟩
    · exact request_node domain member other current currentBound ⟨ready.1, ready.2.2, ready.2.1⟩
  have walked := SourceRecursiveIntersectionCodeMass.walk
    (fun member => if left then requestNode domain member other else requestNode domain other member)
    members input _ stable available_stable calls state bound valid stored
    (fun member present => ⟨known, available, membersAvailable member present⟩)
  apply SourceRecursiveIntersectionCodeMass.bind _ _ state bound valid stored _ _ walked
  intro values after larger afterValid _ enough current outputs
  apply SourceRecursiveIntersectionCodeMass.union values after larger afterValid outputs.2
  rw [outputs.1]
  exact Nat.le_trans width (Nat.mul_le_mul enough enough)

/-- Mu entry retains literal domains and bodies before the actual optional-binder continuation. -/
theorem compileMu (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) :
    At (SourceRecursiveIntersectionCode.compileMu domain left right) state bound
      (fun after value => Available after.heap value) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;>
    simp only [SourceRecursiveIntersectionCode.compileMu, first, second, unsupported, At]
  all_goals try trivial
  rename_i firstId secondId
  obtain ⟨_valid, _growth, enteredDomain⟩ :=
    entered state valid domain known left right leftAvailable rightAvailable firstId secondId
  intro larger _ growth _ _
  refine ⟨⟨enteredDomain, growth.available _ (body_available state.heap left leftAvailable),
    growth.available _ (body_available state.heap right rightAvailable)⟩, ?_⟩
  intro value after last _ _ _ _ available
  exact SourceRecursiveIntersectionCodeMass.optional _ value after last available

/-- Actual binding readback supplies the original complete Mu before its quantitative request. -/
theorem compileReference (domain : Interned DomainKey) (name : Nat) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) :
    At (SourceRecursiveIntersectionCode.compileReference domain name other left) state bound
      (fun after value => Available after.heap value) := by
  by_cases member : name ∈ SourceRecursiveIntersectionDomain.names domain.key
  · obtain ⟨entry, body, depth, ordinary, rfl, stored⟩ := known.bindings name member
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ stored entry.identity rfl
    simp only [SourceRecursiveIntersectionCode.compileReference, member, ite_true, At, read]
    cases left
    · exact request_node domain other (.mu entry body depth ordinary) state bound ⟨known, available, stored⟩
    · exact request_node domain (.mu entry body depth ordinary) other state bound ⟨known, stored, available⟩
  · simp only [SourceRecursiveIntersectionCode.compileReference, member, ite_false, At]

/-- Every actual node compiler branch derives its quantitative certificate from initial physical inputs. -/
theorem compileNode (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (stored : Stored bound state.heap)
    (ready : NodeReady state request) :
    At (SourceRecursiveIntersectionCode.compileNode request) state bound
      (fun after value => Available after.heap value) := by
  cases request with
  | mk domain left right =>
      obtain ⟨known, leftAvailable, rightAvailable⟩ := ready
      cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
      | empty => simpa only [SourceRecursiveIntersectionCode.compileNode, selected, At] using empty_available state.heap
      | reset =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          exact request_node IntersectionEmptyDomain.emptyDomain left right state bound
            ⟨empty_domain state, leftAvailable, rightAvailable⟩
      | self => simpa only [SourceRecursiveIntersectionCode.compileNode, selected, At] using leftAvailable
      | swap =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          exact request_node domain right left state bound ⟨known, rightAvailable, leftAvailable⟩
      | repeated key =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected, At]
          apply reference_available state.heap (.intersection key.1 key.2)
          intro name member
          simp [Value.free] at member
      | bothMu | leftMu | rightMu =>
          simpa only [SourceRecursiveIntersectionCode.compileNode, selected] using
            compileMu domain left right state bound valid known leftAvailable rightAvailable
      | leftUnion =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          cases left with
          | union entry members depth free =>
              exact compileUnion domain members right true state bound valid stored known rightAvailable
                (fun value member => leftAvailable.children value (by simpa only [children] using member))
                (union_width state.heap stored entry members depth free leftAvailable)
          | empty | reference | node | mu => trivial
      | rightUnion =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          cases right with
          | union entry members depth free =>
              exact compileUnion domain members left false state bound valid stored known leftAvailable
                (fun value member => rightAvailable.children value (by simpa only [children] using member))
                (union_width state.heap stored entry members depth free rightAvailable)
          | empty | reference | node | mu => trivial
      | leftReference =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          cases left <;> try trivial
          rename_i name
          cases name <;> first | exact compileReference _ _ _ _ state bound valid known rightAvailable | trivial
      | rightReference =>
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          cases right <;> try trivial
          rename_i name
          cases name <;> first | exact compileReference _ _ _ _ state bound valid known leftAvailable | trivial
      | ordinary =>
          have width := rows_width state.heap stored left right leftAvailable rightAvailable
          simp only [SourceRecursiveIntersectionCode.compileNode, selected]
          cases left <;> cases right <;> try trivial
          rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
          exact compileRows domain firstEdges secondEdges state bound valid stored known
            (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
            (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member) width
      | unsupported => simp only [SourceRecursiveIntersectionCode.compileNode, selected, unsupported, At]

end Compiler
end MicroCFTA.SourceRecursiveIntersectionCompileWidth
