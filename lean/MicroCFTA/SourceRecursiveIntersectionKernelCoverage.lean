import MicroCFTA.SourceRecursiveIntersectionKernelVerified
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage

/-!
# Payload coverage after completed actual recursive intersection

Actual source calls retain incoming pending-key coverage on success.
Ordinary work uses its physical coverage law. Completed optional binders
use their actual callback and reservation coverage law. Checked recursive
frames supply intermediate validity and domain provenance. Failed calls
can retain a new reservation and receive no coverage claim here.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernelCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedNestedFacts InternedBinderProtocol
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel

variable {Symbol Guard : Type} {pending : List NodeKey}

/-- Only completed source results retain the incoming payload permissions. -/
def OnDone (pending : List NodeKey) (outcome : Result Symbol Guard A) : Prop :=
  ∀ value after, outcome = .done value after → Covered pending after.heap

private def Covers
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ domain left right state, SourceRecursiveIntersectionKernel.Valid state → Domain state domain → Available state.heap left →
    Available state.heap right → Covered pending state.heap → OnDone pending (call domain left right state)

private theorem done_covered (value : A) (state : Machine Symbol Guard) (covered : Covered pending state.heap) :
    OnDone pending (.done value state) := by
  intro actual after returned
  cases returned
  exact covered

private theorem unsupported_covered {A : Type} (left right : Value Symbol Guard) (state : Machine Symbol Guard) :
    OnDone pending (unsupported (A := A) left right state) := by
  intro value after impossible
  cases impossible

private theorem bind_covered (outcome : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B) (first : OnDone pending outcome)
    (later : ∀ value after, outcome = .done value after → Covered pending after.heap → OnDone pending (next value after)) :
    OnDone pending (outcome.bind next) := by
  cases outcome with
  | failed failure state => intro value after impossible; cases impossible
  | done value state => exact later value state rfl (first value state rfl)

private theorem work_covered [DecidableEq (EdgeKey Symbol Guard)] (request : Work Symbol Guard A)
    (state : Machine Symbol Guard) (valid : InternedConstructorTemplates.Valid state.heap)
    (covered : Covered pending state.heap) : OnDone pending (work request state) := by
  intro value after returned
  cases returned
  exact InternedNestedCoverage.run_covered request state.heap valid covered

private theorem construction_covered (outcome : InternedNestedConstruction.Outcome Symbol Guard A)
    (state : Machine Symbol Guard) (covered : InternedNestedCoverage.OnDone pending outcome) :
    OnDone pending (construction outcome state) := by
  cases outcome with
  | pending key heap => intro value after impossible; cases impossible
  | done value heap =>
      intro actual after returned
      cases returned
      exact covered value heap rfl

private theorem walk_covered (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (stable : Stable input)
    (checks : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Checked state (call request state) output)
    (covering : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      Covered pending state.heap → OnDone pending (call request state))
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request)
    (covered : Covered pending state.heap) : OnDone pending (walk call requests state) := by
  induction requests generalizing state with
  | nil => exact done_covered [] state covered
  | cons head tail ih =>
      have first := checks head List.mem_cons_self state valid (inputs head List.mem_cons_self)
      simp only [walk]
      apply bind_covered _ _ (covering head List.mem_cons_self state valid (inputs head List.mem_cons_self) covered)
      intro value after returned afterCovered
      have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [returned, Result.state] using first.valid
      have growth : Extension state after := by simpa only [returned, Result.state] using first.extension
      have remaining := ih
        (fun request member => checks request (List.mem_cons_of_mem _ member))
        (fun request member => covering request (List.mem_cons_of_mem _ member)) after afterValid
        (fun request member => stable state after growth request (inputs request (List.mem_cons_of_mem _ member))) afterCovered
      apply bind_covered _ _ remaining
      intro values final completed finalCovered
      exact done_covered (value :: values) final finalCovered

private theorem mu_covered [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call)
    (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain) (leftAvailable : Available state.heap left)
    (rightAvailable : Available state.heap right) (covered : Covered pending state.heap) :
    OnDone pending (mu call domain left right state) := by
  cases first : SourceRecursiveIntersectionControl.identity left <;>
    cases second : SourceRecursiveIntersectionControl.identity right <;> simp only [mu, first, second]
  all_goals try exact unsupported_covered left right state
  rename_i firstId secondId
  let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right firstId secondId
  let after : Machine Symbol Guard := {state with domains := actual.2}
  obtain ⟨afterValid, _, afterDomain⟩ := entered state valid domain known left right
    leftAvailable rightAvailable firstId secondId
  have leftBody := body_available state.heap left leftAvailable
  have rightBody := body_available state.heap right rightAvailable
  have requested := calls actual.1 (body left) (body right) after afterValid afterDomain leftBody rightBody
  apply bind_covered _ _ (covering actual.1 (body left) (body right) after afterValid afterDomain leftBody rightBody covered)
  intro value final returned finalCovered
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [returned, Result.state] using requested.valid
  exact construction_covered _ final (SourceRecursiveIntersectionMaybeMu.maybeMu_covered _ value final.heap
    finalValid.1.coherent.valid finalCovered)

private theorem reference_covered
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (covering : Covers (pending := pending) call) (domain : Interned DomainKey) (name : Nat)
    (other : Value Symbol Guard) (left : Bool) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (available : Available state.heap other) (covered : Covered pending state.heap) :
    OnDone pending (reference call domain name other left state) := by
  by_cases bound : name ∈ names domain.key
  · obtain ⟨entry, stored, depth, ordinary, rfl, storedAvailable⟩ := known.bindings name bound
    have read := SourcePreparedSharedRows.read_identity state.heap valid.1 _ storedAvailable entry.identity rfl
    simp only [reference, bound, ite_true, read]
    cases left
    · exact covering domain other (.mu entry stored depth ordinary) state valid known available storedAvailable covered
    · exact covering domain (.mu entry stored depth ordinary) other state valid known storedAvailable available covered
  · simp only [reference, bound, ite_false]
    intro value after impossible
    cases impossible

private theorem children_covered
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (requests : List (Value Symbol Guard × Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (inputs : ∀ pair ∈ requests, Available state.heap pair.1 ∧ Available state.heap pair.2)
    (covered : Covered pending state.heap) :
    OnDone pending (walk (fun pair => call domain pair.1 pair.2) requests state) := by
  let input := fun (state : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap pair.1 ∧ Available state.heap pair.2
  have stable : Stable input := by
    intro before after growth pair available
    exact ⟨available.1.grows domain growth, growth.available _ available.2.1, growth.available _ available.2.2⟩
  exact walk_covered _ requests input _ stable
    (fun pair _ current currentValid available => calls domain pair.1 pair.2 current currentValid available.1 available.2.1 available.2.2)
    (fun pair _ current currentValid available => covering domain pair.1 pair.2 current currentValid available.1 available.2.1 available.2.2)
    state valid (fun pair member => ⟨known, inputs pair member⟩) covered

private theorem edge_covered [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (left right : EdgeValue Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : EdgeResident state.heap left) (rightResident : EdgeResident state.heap right)
    (covered : Covered pending state.heap) : OnDone pending (edge emptyGuard conjoin (call domain) left right state) := by
  have inputs : ∀ pair ∈ left.children.zip right.children, Available state.heap pair.1 ∧ Available state.heap pair.2 := by
    intro pair member
    have contained := List.of_mem_zip member
    exact ⟨valid.1.cached.edges left.entry.key left leftResident pair.1 contained.1,
      valid.1.cached.edges right.entry.key right rightResident pair.2 contained.2⟩
  unfold edge
  split
  · have checked := children_checked call calls domain _ state valid known inputs
    apply bind_covered _ _ (children_covered call calls covering domain _ state valid known inputs covered)
    intro values after returned afterCovered
    have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [returned, Result.state] using checked.valid
    exact work_covered _ after afterValid.1.coherent.valid afterCovered
  · exact work_covered _ state valid.1.coherent.valid covered

private theorem rows_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge)
    (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) (covered : Covered pending state.heap) :
    OnDone pending (walk (fun pair => edge emptyGuard conjoin (call domain) pair.1 pair.2) (pairs left right) state) := by
  let input := fun (state : Machine Symbol Guard) (pair : EdgeValue Symbol Guard × EdgeValue Symbol Guard) =>
    Domain state domain ∧ EdgeResident state.heap pair.1 ∧ EdgeResident state.heap pair.2
  have stable : Stable input := by
    intro before after growth pair available
    exact ⟨available.1.grows domain growth, edge_grows _ _ growth.heap _ available.2.1,
      edge_grows _ _ growth.heap _ available.2.2⟩
  exact walk_covered _ (pairs left right) input _ stable
    (fun pair _ current currentValid available => edge_checked emptyGuard conjoin call calls domain pair.1 pair.2
      current currentValid available.1 available.2.1 available.2.2)
    (fun pair _ current currentValid available => edge_covered emptyGuard conjoin call calls covering domain pair.1 pair.2
      current currentValid available.1 available.2.1 available.2.2)
    state valid (by
      intro pair member
      obtain ⟨first, second, _⟩ := (pairs_member left right pair).mp member
      exact ⟨known, leftResident pair.1 first, rightResident pair.2 second⟩) covered

private theorem node_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (left right : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (known : Domain state domain) (leftResident : ∀ edge ∈ left, EdgeResident state.heap edge)
    (rightResident : ∀ edge ∈ right, EdgeResident state.heap edge) (covered : Covered pending state.heap) :
    OnDone pending (node emptyGuard conjoin (call domain) left right state) := by
  have checked := rows_checked emptyGuard conjoin call calls domain left right state valid known leftResident rightResident
  unfold node
  apply bind_covered _ _ (rows_covered emptyGuard conjoin call calls covering domain left right state valid known
    leftResident rightResident covered)
  intro values after returned afterCovered
  have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [returned, Result.state] using checked.valid
  exact work_covered _ after afterValid.1.coherent.valid afterCovered

private theorem union_covered [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (members : List (Value Symbol Guard)) (other : Value Symbol Guard) (left : Bool)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (available : Available state.heap other) (membersAvailable : ∀ value ∈ members, Available state.heap value)
    (covered : Covered pending state.heap) :
    OnDone pending ((walk (fun member => if left then call domain member other else call domain other member) members state).bind
      fun values after => work (makeUnion values) after) := by
  let input := fun (state : Machine Symbol Guard) (value : Value Symbol Guard) =>
    Domain state domain ∧ Available state.heap other ∧ Available state.heap value
  have stable : Stable input := by
    intro before after growth value present
    exact ⟨present.1.grows domain growth, growth.available _ present.2.1, growth.available _ present.2.2⟩
  have checks : ∀ member ∈ members, ∀ current, SourceRecursiveIntersectionKernel.Valid current → input current member →
      Checked current ((if left then call domain member other else call domain other member) current)
        (fun after value => Available after.heap value) := by
    intro member _ current currentValid present
    cases left
    · exact calls domain other member current currentValid present.1 present.2.1 present.2.2
    · exact calls domain member other current currentValid present.1 present.2.2 present.2.1
  have coverage : ∀ member ∈ members, ∀ current, SourceRecursiveIntersectionKernel.Valid current → input current member → Covered pending current.heap →
      OnDone pending ((if left then call domain member other else call domain other member) current) := by
    intro member _ current currentValid present currentCovered
    cases left
    · exact covering domain other member current currentValid present.1 present.2.1 present.2.2 currentCovered
    · exact covering domain member other current currentValid present.1 present.2.2 present.2.1 currentCovered
  have inputs : ∀ member ∈ members, input state member := fun member present => ⟨known, available, membersAvailable member present⟩
  have checked := walk_checked _ members input _ stable available_stable checks state valid inputs
  apply bind_covered _ _ (walk_covered _ members input _ stable checks coverage state valid inputs covered)
  intro values after returned afterCovered
  have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [returned, Result.state] using checked.valid
  exact work_covered _ after afterValid.1.coherent.valid afterCovered

private theorem onNode_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (covering : Covers (pending := pending) call) (domain : Interned DomainKey)
    (left right : Value Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) (covered : Covered pending state.heap) :
    OnDone pending (onNode emptyGuard conjoin call domain left right state) := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty => simp only [onNode, selected]; exact done_covered _ state covered
  | reset => simp only [onNode, selected]; exact covering _ left right state valid (empty_domain state) leftAvailable rightAvailable covered
  | self => simp only [onNode, selected]; exact done_covered _ state covered
  | swap => simp only [onNode, selected]; exact covering domain right left state valid known rightAvailable leftAvailable covered
  | repeated key => simp only [onNode, selected]; exact done_covered _ state covered
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected]
      exact mu_covered call calls covering domain left right state valid known leftAvailable rightAvailable covered
  | leftUnion =>
      simp only [onNode, selected]
      cases left with
      | union entry members depth free =>
          exact union_covered call calls covering domain members right true state valid known rightAvailable
            (fun value member => leftAvailable.children value (by simpa only [children] using member)) covered
      | empty | reference | node | mu => exact unsupported_covered _ _ state
  | rightUnion =>
      simp only [onNode, selected]
      cases right with
      | union entry members depth free =>
          exact union_covered call calls covering domain members left false state valid known leftAvailable
            (fun value member => rightAvailable.children value (by simpa only [children] using member)) covered
      | empty | reference | node | mu => exact unsupported_covered _ _ state
  | leftReference =>
      simp only [onNode, selected]
      cases left with
      | reference name =>
          cases name <;> try exact unsupported_covered _ _ state
          rename_i identity
          exact reference_covered call covering domain identity right true state valid known rightAvailable covered
      | empty | node | union | mu => exact unsupported_covered _ _ state
  | rightReference =>
      simp only [onNode, selected]
      cases right with
      | reference name =>
          cases name <;> try exact unsupported_covered _ _ state
          rename_i identity
          exact reference_covered call covering domain identity left false state valid known leftAvailable covered
      | empty | node | union | mu => exact unsupported_covered _ _ state
  | ordinary =>
      simp only [onNode, selected]
      cases left <;> cases right <;> try exact unsupported_covered _ _ state
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact node_covered emptyGuard conjoin call calls covering domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member) covered
  | unsupported => simp only [onNode, selected]; exact unsupported_covered _ _ state

/-- Every bounded actual source call preserves its incoming coverage whenever it completes. -/
theorem execute_covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat) :
    ∀ domain left right (state : Machine Symbol Guard), SourceRecursiveIntersectionKernel.Valid state → Domain state domain →
      Available state.heap left → Available state.heap right → Covered pending state.heap →
      OnDone pending (execute emptyGuard conjoin fuel domain left right state) := by
  induction fuel with
  | zero =>
      intro domain left right state valid known leftAvailable rightAvailable covered value after impossible
      cases impossible
  | succ fuel ih =>
      intro domain left right state valid known leftAvailable rightAvailable covered
      exact onNode_covered emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) ih domain left right state
        valid known leftAvailable rightAvailable covered

end MicroCFTA.SourceRecursiveIntersectionKernelCoverage
