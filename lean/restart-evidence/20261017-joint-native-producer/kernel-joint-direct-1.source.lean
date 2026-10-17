import MicroCFTA.SourceCurrentConstrainedCapGuardNative
import MicroCFTA.SourceCurrentConstrainedCapOriginalSupport
import MicroCFTA.SourceRecursiveIntersectionKernelScope

/-!
# Joint observations at actual recursive source returns

The actual return retains its semantic heap, causal guard heap, and fixed
source history. Ordered walks pass those facts through each preceding call.
The recursive call contract includes cap, ranked occurrence, and pair scope.
It is an induction interface. It does not assert recursive completion.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJoint
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConstrainedCapGuardHeap (Heap)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapNativeOccurrenceCache (OriginalBindings NodeInputs)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceRecursiveIntersectionResultScope (Scope)
variable {Symbol Guard : Type}

/-- One actual source point retains the two cache invariants and immutable source records. -/
structure Context (annotation : Guard → Prop) (source : State Symbol Guard) (state : Machine Symbol Guard) : Prop where
  /-- Both actual cache families satisfy their physical invariants. -/
  valid : SourceRecursiveIntersectionKernel.Valid state
  /-- The actual constructor heap retains its semantic observations. -/
  semantic : SemanticHeap state.heap
  /-- Every earlier completed Mu retains its produced guard observation. -/
  guards : Heap annotation state.heap
  /-- Every immutable source record remains in the current heap. -/
  growth : Grows source state.heap
  /-- Every immutable source identity retains its issued key. -/
  history : Extends source.nodes.issued state.heap.nodes.issued

/-- A successful actual return retains the same joint context and its local result law. -/
def Checked (annotation : Guard → Prop) (source : State Symbol Guard) (result : Result Symbol Guard A)
    (post : Machine Symbol Guard → A → Prop) : Prop :=
  ∀ value after, result = .done value after → Context annotation source after ∧ post after value

/-- Actual returned physical effects compose the immutable source history. -/
theorem Context.after {annotation : Guard → Prop} {source : State Symbol Guard} {before after : Machine Symbol Guard}
    (context : Context annotation source before) (valid : SourceRecursiveIntersectionKernel.Valid after)
    (semantic : SemanticHeap after.heap) (guards : Heap annotation after.heap) (extension : Extension before after) :
    Context annotation source after :=
  ⟨valid, semantic, guards, grows_trans context.growth extension.heap, extends_trans context.history extension.history⟩

/-- An unchanged actual return retains every initial joint fact. -/
theorem pure (annotation : Guard → Prop) (source : State Symbol Guard) (state : Machine Symbol Guard)
    (context : Context annotation source state) (value : A) (post : Machine Symbol Guard → A → Prop)
    (property : post state value) : Checked annotation source (.done value state) post := by
  intro actual after same
  cases same
  exact ⟨context, property⟩

/-- Failed source execution has no successful returned-value assertion. -/
theorem failed (annotation : Guard → Prop) (source : State Symbol Guard) (state : Machine Symbol Guard)
    (failure : Failure) (post : Machine Symbol Guard → A → Prop) :
    Checked annotation source (.failed failure state) post := by
  intro value after impossible
  cases impossible

/-- The next source call receives the preceding actual return and its produced context. -/
theorem bind (annotation : Guard → Prop) (source : State Symbol Guard) (result : Result Symbol Guard A)
    (next : A → Machine Symbol Guard → Result Symbol Guard B)
    (first : Machine Symbol Guard → A → Prop) (post : Machine Symbol Guard → B → Prop)
    (checked : Checked annotation source result first)
    (later : ∀ value after, result = .done value after → Context annotation source after → first after value →
      Checked annotation source (next value after) post) : Checked annotation source (result.bind next) post := by
  cases result with
  | failed failure state => exact failed annotation source state failure post
  | done value state => exact later value state rfl (checked value state rfl).1 (checked value state rfl).2

/-- A weaker local post uses the same actual result and produced context. -/
theorem map (annotation : Guard → Prop) (source : State Symbol Guard) (result : Result Symbol Guard A)
    (first post : Machine Symbol Guard → A → Prop) (checked : Checked annotation source result first)
    (convert : ∀ value after, Context annotation source after → first after value → post after value) :
    Checked annotation source result post := by
  intro value after done
  have actual := checked value after done
  exact ⟨actual.1, convert value after actual.1 actual.2⟩

/-- Ordered actual walks retain the joint context and every earlier output after later effects. -/
theorem walk (annotation : Guard → Prop) (source : State Symbol Guard)
    (call : A → Machine Symbol Guard → Result Symbol Guard B) (requests : List A)
    (input : Machine Symbol Guard → A → Prop) (output : Machine Symbol Guard → B → Prop)
    (inputStable : Stable input) (outputStable : Stable output)
    (physical : ∀ request ∈ requests, ∀ state, SourceRecursiveIntersectionKernel.Valid state → input state request →
      SourceRecursiveIntersectionKernel.Checked state (call request state) output)
    (calls : ∀ request ∈ requests, ∀ state, Context annotation source state → input state request →
      Checked annotation source (call request state) output)
    (state : Machine Symbol Guard) (context : Context annotation source state) (inputs : ∀ request ∈ requests, input state request) :
    Checked annotation source (SourceRecursiveIntersectionKernel.walk call requests state)
      (fun after values => ∀ value ∈ values, output after value) := by
  induction requests generalizing state with
  | nil => exact pure annotation source state context [] _ (by intro value member; cases member)
  | cons first rest ih =>
      have firstPhysical := physical first List.mem_cons_self state context.valid (inputs first List.mem_cons_self)
      rw [SourceRecursiveIntersectionKernel.walk]
      apply bind annotation source _ _ _ _ (calls first List.mem_cons_self state context (inputs first List.mem_cons_self))
      intro value after done afterContext returned
      have extension : Extension state after := by simpa only [done, Result.state] using firstPhysical.extension
      have restInputs := fun request member => inputStable state after extension request (inputs request (List.mem_cons_of_mem _ member))
      have restPhysical := SourceRecursiveIntersectionKernel.walk_checked call rest input output inputStable outputStable
        (fun request member => physical request (List.mem_cons_of_mem _ member)) after afterContext.valid restInputs
      apply bind annotation source _ _ _ _
        (ih (fun request member => physical request (List.mem_cons_of_mem _ member))
          (fun request member => calls request (List.mem_cons_of_mem _ member)) after afterContext restInputs)
      intro values final completed finalContext remaining
      have later : Extension after final := by simpa only [completed, Result.state] using restPhysical.extension
      apply pure annotation source final finalContext
      intro actual member
      rcases List.mem_cons.mp member with rfl | included
      · exact outputStable after final later actual returned
      · exact remaining actual included

/-- Each smaller actual request supplies the three laws at its complete original input rank. -/
def Calls (annotation : Guard → Prop) (source : State Symbol Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ depth domain left right state, Context annotation source state → Domain state domain →
    OriginalBindings annotation source domain.key → NodeInputs source ⟨domain, left, right⟩ →
    Cap annotation depth left → Cap annotation depth right →
    Checked annotation source (call domain left right state)
      (fun after value => Available after.heap value ∧ Cap annotation depth value ∧
        Classified (sourceWeight annotation source) (pairRank annotation left right) value ∧ Scope domain.key.seen value)

end MicroCFTA.SourceCurrentConstrainedCapKernelJoint
