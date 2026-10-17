import MicroCFTA.SourceRecursiveIntersectionWorkMass
import MicroCFTA.SourceRecursiveIntersectionCodeSafety

/-!
# Quantitative safety of literal source continuations

The current numeric bound limits each literal constructor list. A recursive
return supplies physical availability or residency at its actual heap.
Continuations accept every larger causal store bound after physical growth.
The certificate does not assume a future constructor mass or width result.
Native completion frames retain the certificate of their remaining code.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCodeMass
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Guard : Type} {A B : Type}

/-- Increasing a literal list limit retains its exact physical input check. -/
theorem work_inputs_mono {state : State Symbol Guard} {job : Work Symbol Guard A} {first last : Nat}
    (inputs : SourceRecursiveIntersectionWorkMass.Inputs first state job) (increase : first ≤ last) :
    SourceRecursiveIntersectionWorkMass.Inputs last state job := by
  cases inputs with
  | pure value => exact .pure value
  | edge symbol guard values available length => exact .edge symbol guard values available (Nat.le_trans length increase)
  | node rows resident length => exact .node rows resident (Nat.le_trans length increase)
  | union values available length => exact .union values available (Nat.le_trans length increase)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Literal source code retains physical results and a numeric list-width certificate. -/
def At (code : Code Symbol Guard A) (state : Machine Symbol Guard) (bound : Nat)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next =>
      SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) state.heap job ∧
      ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        bound ≤ larger → Stored larger after.heap →
        SourceRecursiveIntersectionKernel.work job state = .done value after → At (next value) after larger post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      ∀ larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        bound ≤ larger → Stored larger after.heap → At (next actual.1) after larger post
  | .read name next => At (next (SourcePreparedSharedRows.read state.heap name)) state bound post
  | .optionalBinder _ body next =>
      Available state.heap body ∧
      ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        bound ≤ larger → Stored larger after.heap → Available after.heap value → At (next value) after larger post
  | .node request next =>
      NodeReady state request ∧
      ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        bound ≤ larger → Stored larger after.heap → Available after.heap value → At (next value) after larger post
  | .edge request next =>
      EdgeReady state request ∧
      ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        bound ≤ larger → Stored larger after.heap → EdgeResident after.heap value → At (next value) after larger post
  | .finishNode _ _ next | .finishEdge _ _ next => At next state bound post

/-- A larger numeric bound retains the same captured code and physical result contract. -/
theorem mono (code : Code Symbol Guard A) (state : Machine Symbol Guard) {first last : Nat}
    (safe : At code state first post) (increase : first ≤ last) : At code state last post := by
  induction code generalizing state with
  | pure | fail => exact safe
  | work job next ih =>
      refine ⟨work_inputs_mono safe.1 (Nat.mul_le_mul increase increase), ?_⟩
      intro value after larger valid growth enough stored done
      exact safe.2 value after larger valid growth (Nat.le_trans increase enough) stored done
  | enter domain left right first second next ih =>
      intro larger valid growth enough stored
      exact safe larger valid growth (Nat.le_trans increase enough) stored
  | read name next ih => exact ih _ state safe
  | optionalBinder key body next ih | node request next ih | edge request next ih =>
      refine ⟨safe.1, ?_⟩
      intro value after larger valid growth enough stored available
      exact safe.2 value after larger valid growth (Nat.le_trans increase enough) stored available
  | finishNode handle value next ih | finishEdge handle value next ih => exact ih state safe

/-- Source sequencing retains exact physical growth and the common numeric bound. -/
theorem bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) (intermediate : Machine Symbol Guard → A → Prop)
    (post : Machine Symbol Guard → B → Prop) (safe : At code state bound intermediate)
    (continuation : ∀ value after larger, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      bound ≤ larger → Stored larger after.heap → intermediate after value → At (next value) after larger post) :
    At (code.bind next) state bound post := by
  induction code generalizing state bound with
  | pure value => exact continuation value state bound valid (.refl state) (Nat.le_refl _) stored safe
  | fail => trivial
  | work job resume ih =>
      refine ⟨safe.1, ?_⟩
      intro value after larger afterValid growth increase current done
      exact ih value after larger afterValid current (safe.2 value after larger afterValid growth increase current done)
        (fun result final last finalValid later enough finalStored holds =>
          continuation result final last finalValid (growth.trans later) (Nat.le_trans increase enough) finalStored holds)
  | enter domain left right first second resume ih =>
      intro larger afterValid growth increase current
      exact ih _ _ larger afterValid current (safe larger afterValid growth increase current)
        (fun result final last finalValid later enough finalStored holds =>
          continuation result final last finalValid (growth.trans later) (Nat.le_trans increase enough) finalStored holds)
  | read name resume ih => exact ih _ state bound valid stored safe continuation
  | optionalBinder key body resume ih | node request resume ih | edge request resume ih =>
      refine ⟨safe.1, ?_⟩
      intro value after larger afterValid growth increase current available
      exact ih value after larger afterValid current (safe.2 value after larger afterValid growth increase current available)
        (fun result final last finalValid later enough finalStored holds =>
          continuation result final last finalValid (growth.trans later) (Nat.le_trans increase enough) finalStored holds)
  | finishNode handle value rest ih | finishEdge handle value rest ih => exact ih state bound valid stored safe continuation

/-- Ordered code walks retain physical outputs and their exact original occurrence count. -/
theorem walk (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state bound, SourceRecursiveIntersectionKernel.Valid state →
      Stored bound state.heap → input state request → At (call request) state bound output)
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (stored : Stored bound state.heap) (inputs : ∀ request ∈ requests, input state request) :
    At (SourceRecursiveIntersectionCode.walk call requests) state bound
      (fun after values => values.length = requests.length ∧ ∀ value ∈ values, output after value) := by
  induction requests generalizing state bound with
  | nil => exact ⟨rfl, fun value member => by cases member⟩
  | cons first rest ih =>
      apply bind _ _ state bound valid stored output _ (calls first List.mem_cons_self state bound valid stored (inputs first List.mem_cons_self))
      intro value after larger afterValid growth increase current available
      have remaining := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after larger afterValid current
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      apply bind _ _ after larger afterValid current _ _ remaining
      intro values final last finalValid later enough finalStored present
      refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ present.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | tail
      · exact outputStable after final later actual available
      · exact present.2 actual tail

/-- An original node request accepts each actual physically available recursive return. -/
theorem request_node (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (bound : Nat) (ready : NodeReady state ⟨domain, left, right⟩) :
    At (requestNode domain left right) state bound (fun after value => Available after.heap value) :=
  ⟨ready, fun _ _ _ _ _ _ _ available => available⟩

/-- An original edge request accepts each actual physically resident recursive return. -/
theorem request_edge (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (bound : Nat) (ready : EdgeReady state ⟨domain, left, right⟩) :
    At (requestEdge domain left right) state bound (fun after value => EdgeResident after.heap value) :=
  ⟨ready, fun _ _ _ _ _ _ _ resident => resident⟩

/-- Optional binding accepts its own actual physically available return at a larger causal bound. -/
theorem optional (key : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard) (bound : Nat)
    (available : Available state.heap body) :
    At (.optionalBinder key body .pure) state bound (fun after value => Available after.heap value) :=
  ⟨available, fun _ _ _ _ _ _ _ result => result⟩

/-- Verified literal Work derives the physical postcondition of its own exact returned instruction. -/
theorem work (job : Work Symbol Guard A) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (inputs : SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) state.heap job)
    (property : State Symbol Guard → A → Prop)
    (verified : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work job state.heap) property) :
    At (.work job .pure) state bound (fun after value => property after.heap value) := by
  have checked := SourceRecursiveIntersectionKernel.work_checked state valid job property verified
  exact ⟨inputs, fun value after _ _ _ _ _ done => checked.result value after done⟩

/-- Literal edge construction derives its width check and exact resident result. -/
theorem edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (state : Machine Symbol Guard) (bound : Nat) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (length : values.length ≤ bound * bound) :
    At (.work (makeEdge symbol guard values) .pure) state bound (fun after value => EdgeResident after.heap value) :=
  work _ state bound valid (.edge symbol guard values available length) EdgeResident
    (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available)

/-- Literal node construction derives its width check and exact available result. -/
theorem node (rows : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (resident : ∀ row ∈ rows, EdgeResident state.heap row) (length : rows.length ≤ bound * bound) :
    At (.work (makeNode rows) .pure) state bound (fun after value => Available after.heap value) :=
  work _ state bound valid (.node rows resident length) Available
    (InternedNestedFacts.node_verified rows state.heap valid.1 resident)

/-- Literal union construction derives its width check and exact available result. -/
theorem union (values : List (Value Symbol Guard)) (state : Machine Symbol Guard) (bound : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (available : ∀ value ∈ values, Available state.heap value) (length : values.length ≤ bound * bound) :
    At (.work (makeUnion values) .pure) state bound (fun after value => Available after.heap value) :=
  work _ state bound valid (.union values available length) Available
    (InternedNestedFacts.union_verified values state.heap valid.1 available)

end MicroCFTA.SourceRecursiveIntersectionCodeMass
