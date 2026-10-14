import MicroCFTA.SourceRecursiveIntersectionNativeRunning

/-!
# Physical safety of compiled source continuations

Source effects retain complete physical and domain facts. Recursive requests
require available original inputs. Their continuations accept every valid
available returned record after source growth. Machine word bounds and
concrete completed memo provenance remain separate obligations.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks

/-- Source safety retains exact effect caches and available recursive request inputs. -/
def Safe [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (state : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  match code with
  | .pure value => post state value
  | .fail _ => True
  | .work job next =>
      let actual := SourceRecursiveIntersectionKernel.work job state
      SourceRecursiveIntersectionKernel.Valid actual.state ∧ Extension state actual.state ∧
        ∀ value after, actual = .done value after → Safe (next value) after post
  | .enter domain left right first second next =>
      let actual := SourceRecursiveIntersectionEnvironment.enter state.domains domain.key left right first second
      let after : Machine Symbol Guard := { state with domains := actual.2 }
      SourceRecursiveIntersectionKernel.Valid after ∧ Extension state after ∧ Safe (next actual.1) after post
  | .read name next => Safe (next (SourcePreparedSharedRows.read state.heap name)) state post
  | .optionalBinder key body next =>
      let actual := construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.heap) state
      SourceRecursiveIntersectionKernel.Valid actual.state ∧ Extension state actual.state ∧
        ∀ value after, actual = .done value after → Safe (next value) after post
  | .node request next =>
      NodeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        Available after.heap value → Safe (next value) after post
  | .edge request next =>
      EdgeReady state request ∧ ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
        EdgeResident after.heap value → Safe (next value) after post
  | .finishNode .. | .finishEdge .. => False

/-- Safe source sequencing composes actual cache growth and returned record properties. -/
theorem safe_bind [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (next : A → Code Symbol Guard B)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (intermediate : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (safe : Safe code state intermediate)
    (continuation : ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension state after →
      intermediate after value → Safe (next value) after post) : Safe (code.bind next) state post := by
  induction code generalizing state with
  | pure value => exact continuation value state valid (.refl state) safe
  | fail failure => trivial
  | work job resume ih | optionalBinder key body resume ih =>
    refine ⟨safe.1, safe.2.1, ?_⟩
    intro value after done
    have afterValid : SourceRecursiveIntersectionKernel.Valid after := by simpa only [done, Result.state] using safe.1
    have growth : Extension state after := by simpa only [done, Result.state] using safe.2.1
    exact ih value after afterValid (safe.2.2 value after done)
      (fun result final finalValid later holds => continuation result final finalValid (growth.trans later) holds)
  | enter domain left right first second resume ih =>
    refine ⟨safe.1, safe.2.1, ?_⟩
    exact ih _ _ safe.1 safe.2.2
      (fun result final finalValid later holds => continuation result final finalValid (safe.2.1.trans later) holds)
  | read name resume ih => exact ih _ state valid safe continuation
  | node request resume ih | edge request resume ih =>
    refine ⟨safe.1, ?_⟩
    intro value after afterValid growth available
    exact ih value after afterValid (safe.2 value after afterValid growth available)
      (fun result final finalValid later holds => continuation result final finalValid (growth.trans later) holds)
  | finishNode | finishEdge => cases safe

/-- Ordered source walks retain all available results at the exact final source cache. -/
theorem safe_walk [DecidableEq (EdgeKey Symbol Guard)] (call : A → Code Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (calls : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request → Safe (call request) state output)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (inputs : ∀ request ∈ requests, input state request) :
    Safe (walk call requests) state (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => intro value member; cases member
  | cons first rest ih =>
    apply safe_bind _ _ state valid output _ (calls first List.mem_cons_self state valid (inputs first List.mem_cons_self))
    intro value after afterValid growth available
    have remaining := ih (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterValid
      (fun request member => inputStable state after growth request (inputs request (List.mem_cons_of_mem _ member)))
    apply safe_bind _ _ after afterValid _ _ remaining
    intro values final finalValid later present
    intro actual member
    cases member with
    | head => exact outputStable after final later value available
    | tail head member => exact present actual member

/-- Actual constructor verification supplies physical safety for the emitted source work. -/
theorem safe_work [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard A) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (property : InternedConstructorTemplates.State Symbol Guard → A → Prop)
    (verified : InternedNestedFacts.Verified state.heap (InternedNestedConstruction.work job state.heap) property) :
    Safe (.work job .pure) state (fun after value => property after.heap value) := by
  have checked := work_checked state valid job property verified
  exact ⟨checked.valid, checked.extension, fun value after done => checked.result value after done⟩

/-- Actual optional-binder verification supplies physical safety without assuming completion. -/
theorem safe_optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state) (available : Available state.heap body) :
    Safe (.optionalBinder key body .pure) state (fun after value => Available after.heap value) := by
  have checked := construction_checked state valid _ Available (SourceRecursiveIntersectionMaybeMu.verified key body state.heap valid.1 available)
  exact ⟨checked.valid, checked.extension, fun value after done => checked.result value after done⟩

/-- An original available node request safely returns any valid available child result. -/
theorem safe_requestNode [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (left right : Value Symbol Guard)
    (state : Machine Symbol Guard) (ready : NodeReady state ⟨domain, left, right⟩) :
    Safe (requestNode domain left right) state (fun after value => Available after.heap value) :=
  ⟨ready, fun _ _ _ _ available => available⟩

/-- An original resident row request safely returns any valid resident edge result. -/
theorem safe_requestEdge [DecidableEq (EdgeKey Symbol Guard)] (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (state : Machine Symbol Guard) (ready : EdgeReady state ⟨domain, left, right⟩) :
    Safe (requestEdge domain left right) state (fun after value => EdgeResident after.heap value) :=
  ⟨ready, fun _ _ _ _ resident => resident⟩

end MicroCFTA.SourceRecursiveIntersectionCode
