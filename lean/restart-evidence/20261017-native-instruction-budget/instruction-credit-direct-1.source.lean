import MicroCFTA.SourceRecursiveIntersectionInstructionProfile
import MicroCFTA.SourceRecursiveIntersectionCodeBounds

/-!
# Instruction credit for literal source continuations

Initial semantic ranks assign complete request credit. Literal effects and
native finish frames each consume one instruction. Ordered continuations
retain their exact remaining credit after actual physical growth.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInstructionCredit
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceRecursiveIntersectionNative IntersectSchedule
open SourceRecursiveIntersectionInstructionProfile (budget)
variable {Symbol Guard : Type} {A B : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A whole node request retains original scope and credit from its initial semantic rank. -/
def NodeCharge (source : State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (limit : Nat) (request : NodeRequest Symbol Guard) (amount : Nat) : Prop :=
  NodeScope source request ∧ ∃ complete : Completes (view source holds) (nodeSemantic request),
    budget limit (requiredFuel (view source holds) (nodeSemantic request) complete) ≤ amount

/-- A whole edge request retains original scope and credit from its initial semantic rank. -/
def EdgeCharge (source : State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (limit : Nat) (request : EdgeRequest Symbol Guard) (amount : Nat) : Prop :=
  EdgeScope source request ∧ ∃ complete : Completes (view source holds) (edgeSemantic holds request),
    budget limit (requiredFuel (view source holds) (edgeSemantic holds request) complete) ≤ amount

/-- Actual code reserves instruction credit for each effect, request, and remaining continuation. -/
def At (source : State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool) (limit : Nat)
    (code : Code Symbol Guard A) (state : Machine Symbol Guard) (amount : Nat)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next => ∃ rest, rest + 1 ≤ amount ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        SourceRecursiveIntersectionKernel.work job state = .done value after →
        At source holds limit (next value) after rest post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := {state with domains := actual.2}
      ∃ rest, rest + 1 ≤ amount ∧ ∀ (_ : SourceRecursiveIntersectionKernel.Valid after)
        (_ : Extension state after), At source holds limit (next actual.1) after rest post
  | .read name next => ∃ rest, rest + 1 ≤ amount ∧
      At source holds limit (next (SourcePreparedSharedRows.read state.heap name)) state rest post
  | .optionalBinder _ body next => Available state.heap body ∧ ∃ rest, rest + 1 ≤ amount ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → At source holds limit (next value) after rest post
  | .node request next => NodeReady state request ∧ ∃ callCost rest,
      NodeCharge source holds limit request callCost ∧ callCost + rest ≤ amount ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → At source holds limit (next value) after rest post
  | .edge request next => EdgeReady state request ∧ ∃ callCost rest,
      EdgeCharge source holds limit request callCost ∧ callCost + rest ≤ amount ∧
      ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → At source holds limit (next value) after rest post
  | .finishNode _ _ next | .finishEdge _ _ next => ∃ rest, rest + 1 ≤ amount ∧
      At source holds limit next state rest post

variable {source : State Symbol Guard} {holds : Guard → Language.Term Symbol → Bool} {limit : Nat}
variable {post : Machine Symbol Guard → A → Prop}

/-- Extra initial credit retains the same code and physical return contract. -/
theorem mono (code : Code Symbol Guard A) (state : Machine Symbol Guard) {first last : Nat}
    (safe : At source holds limit code state first post) (increase : first ≤ last) :
    At source holds limit code state last post := by
  cases code with
  | pure | fail => exact safe
  | work | enter | read | finishNode | finishEdge =>
      obtain ⟨rest, enough, next⟩ := safe
      exact ⟨rest, Nat.le_trans enough increase, next⟩
  | optionalBinder =>
      obtain ⟨ready, rest, enough, next⟩ := safe
      exact ⟨ready, rest, Nat.le_trans enough increase, next⟩
  | node | edge =>
      obtain ⟨ready, cost, rest, charged, enough, next⟩ := safe
      exact ⟨ready, cost, rest, charged, Nat.le_trans enough increase, next⟩

/-- Sequencing adds credits and retains the exact common physical machine. -/
theorem bind (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (first second : Nat)
    (valid : SourceRecursiveIntersectionKernel.Valid state)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (safe : At source holds limit code state first intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → At source holds limit (next value) after second post) :
    At source holds limit (code.bind next) state (first + second) post := by
  induction code generalizing state first with
  | pure value =>
      exact mono _ _ (continuation value state valid (.refl state) safe) (by omega)
  | fail => trivial
  | work job resume ih =>
      obtain ⟨rest, enough, bounded⟩ := safe
      refine ⟨rest + second, by omega, ?_⟩
      intro value after afterValid growth done
      exact ih value after rest afterValid (bounded value after afterValid growth done)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | enter domain left right leftName rightName resume ih =>
      obtain ⟨rest, enough, bounded⟩ := safe
      refine ⟨rest + second, by omega, ?_⟩
      intro afterValid growth
      exact ih _ _ rest afterValid (bounded afterValid growth)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | read name resume ih =>
      obtain ⟨rest, enough, bounded⟩ := safe
      exact ⟨rest + second, by omega, ih _ state rest valid bounded continuation⟩
  | optionalBinder key body resume ih =>
      obtain ⟨available, rest, enough, bounded⟩ := safe
      refine ⟨available, rest + second, by omega, ?_⟩
      intro value after afterValid growth present
      exact ih value after rest afterValid (bounded value after afterValid growth present)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | node request resume ih | edge request resume ih =>
      obtain ⟨ready, cost, rest, charged, enough, bounded⟩ := safe
      refine ⟨ready, cost, rest + second, charged, by omega, ?_⟩
      intro value after afterValid growth present
      exact ih value after rest afterValid (bounded value after afterValid growth present)
        (fun result final finalValid later property => continuation result final finalValid (growth.trans later) property)
  | finishNode handle value rest ih | finishEdge handle value rest ih =>
      obtain ⟨remaining, enough, bounded⟩ := safe
      exact ⟨remaining + second, by omega, ih state remaining valid bounded continuation⟩

/-- Ordered walks add one complete call credit per original occurrence. -/
theorem walk (call : A → Code Symbol Guard B) (requests : List A) (perCall : Nat)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      At source holds limit (call request) state perCall output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (inputs : ∀ request ∈ requests, input state request) :
    At source holds limit (SourceRecursiveIntersectionCode.walk call requests) state (requests.length * perCall)
      (fun after values => values.length = requests.length ∧ ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => exact ⟨rfl, fun value member => by cases member⟩
  | cons first rest ih =>
      have firstCall := calls first List.mem_cons_self state valid (inputs first List.mem_cons_self)
      have combined := bind (call first) (fun value =>
        (SourceRecursiveIntersectionCode.walk call rest).bind fun values => .pure (value :: values))
        state perCall (rest.length * perCall) valid output _ firstCall ?_
      · simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using combined
      intro value after afterValid growth present
      have tail := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterValid
        (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
      have appended := bind _ (fun values => .pure (value :: values)) after (rest.length * perCall) 0 afterValid _ _ tail ?_
      · simpa only [Nat.add_zero] using appended
      intro values final finalValid later produced
      refine ⟨by simpa only [List.length_cons] using congrArg Nat.succ produced.1, ?_⟩
      intro actual member
      rcases List.mem_cons.mp member with rfl | remaining
      · exact outputStable after final later value present
      · exact produced.2 actual remaining

/-- A whole node call reserves its initial semantic credit before any execution. -/
theorem request_node (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard) (amount : Nat)
    (ready : NodeReady state request) (charged : NodeCharge source holds limit request amount) :
    At source holds limit (requestNode request.domain request.left request.right) state amount
      (fun after value => Available after.heap value) :=
  ⟨ready, amount, 0, charged, Nat.le_refl _, fun _ _ _ _ available => available⟩

/-- A whole edge call reserves its initial semantic credit before any execution. -/
theorem request_edge (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) (amount : Nat)
    (ready : EdgeReady state request) (charged : EdgeCharge source holds limit request amount) :
    At source holds limit (requestEdge request.domain request.left request.right) state amount
      (fun after value => EdgeResident after.heap value) :=
  ⟨ready, amount, 0, charged, Nat.le_refl _, fun _ _ _ _ resident => resident⟩

/-- One verified literal Work instruction derives its own physical return contract. -/
theorem work (job : Work Symbol Guard A) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (property : State Symbol Guard → A → Prop)
    (verified : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work job state.heap) property) :
    At source holds limit (.work job .pure) state 1 (fun after value => property after.heap value) := by
  have checked := SourceRecursiveIntersectionKernel.work_checked state valid job property verified
  exact ⟨0, Nat.le_refl _, fun value after _ _ done => checked.result value after done⟩

/-- Literal node assembly consumes one checked instruction. -/
theorem node (rows : List (EdgeValue Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (resident : ∀ row ∈ rows, EdgeResident state.heap row) :
    At source holds limit (.work (makeNode rows) .pure) state 1 (fun after value => Available after.heap value) :=
  work _ state valid Available (InternedNestedFacts.node_verified rows state.heap valid.1 resident)

/-- Literal edge assembly consumes one checked instruction. -/
theorem edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (available : ∀ value ∈ values, Available state.heap value) :
    At source holds limit (.work (makeEdge symbol guard values) .pure) state 1 (fun after value => EdgeResident after.heap value) :=
  work _ state valid EdgeResident (InternedNestedFacts.edge_verified symbol guard values state.heap valid.1 available)

/-- Literal union assembly consumes one checked instruction. -/
theorem union (values : List (Value Symbol Guard)) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (available : ∀ value ∈ values, Available state.heap value) :
    At source holds limit (.work (makeUnion values) .pure) state 1 (fun after value => Available after.heap value) :=
  work _ state valid Available (InternedNestedFacts.union_verified values state.heap valid.1 available)

/-- One optional-binder instruction accepts its actual available physical return. -/
theorem optional (key : Nat × Nat) (body : Value Symbol Guard) (state : Machine Symbol Guard)
    (available : Available state.heap body) :
    At source holds limit (.optionalBinder key body .pure) state 1 (fun after value => Available after.heap value) :=
  ⟨available, 0, Nat.le_refl _, fun _ _ _ _ result => result⟩

end MicroCFTA.SourceRecursiveIntersectionInstructionCredit
