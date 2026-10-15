import MicroCFTA.SourceMergedWorker

/-!
# Successful general merge contracts

Each result retains the actual cache and its closed resident payload.
Language coverage uses the independent guarded least language. Ordered
requests retain a certificate at each original request position.
-/
namespace MicroCFTA.SourceMergedContracts
open Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedEdgeResidency (EdgeResident)
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map retainedColumn small)
open InternedGuardedLanguage (meaning)
open MergedColdInterpretation (EdgeMeaning)

/-- A returned closed value covers the independent union language of its inputs. -/
structure ValuePost (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) (result : Value Symbol Guard) : Prop where
  available : Available state result
  closed : result.free = []
  covers : ∀ value ∈ inputs, ∀ term, meaning holds ambient value term → meaning holds ambient result term

/-- A returned closed edge covers all original row languages. -/
structure EdgePost (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (inputs : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (result : EdgeValue Symbol Guard) : Prop where
  resident : EdgeResident state result
  closed : ClosedValues result.children
  covers : ∀ edge ∈ inputs, ∀ term, EdgeMeaning (meaning holds ambient) holds edge term → EdgeMeaning (meaning holds ambient) holds result term

/-- A returned closed row list covers every original row language. -/
structure RowsPost (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (inputs : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) (results : List (EdgeValue Symbol Guard)) : Prop where
  resident : Edges state results
  closed : ClosedEdges results
  covers : ∀ edge ∈ inputs, ∀ term, EdgeMeaning (meaning holds ambient) holds edge term →
    ∃ result ∈ results, EdgeMeaning (meaning holds ambient) holds result term

/-- Actual later effects retain a value certificate. -/
theorem ValuePost.grows {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol}
    {inputs : List (Value Symbol Guard)} {before after : State Symbol Guard} (effects : Effect before after)
    {value : Value Symbol Guard} (post : ValuePost holds ambient inputs before value) : ValuePost holds ambient inputs after value :=
  ⟨effects.1.available value post.available, post.closed, post.covers⟩

/-- Actual later effects retain an edge certificate. -/
theorem EdgePost.grows {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol}
    {inputs : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} (effects : Effect before after)
    {value : EdgeValue Symbol Guard} (post : EdgePost holds ambient inputs before value) : EdgePost holds ambient inputs after value :=
  ⟨InternedEdgeResidency.edge_grows before after effects.1.growth value post.resident, post.closed, post.covers⟩

/-- Actual later effects retain a complete row-list certificate. -/
theorem RowsPost.grows {holds : Guard → Term Symbol → Bool} {ambient : InternedGuardedLanguage.Env Symbol}
    {inputs : List (EdgeValue Symbol Guard)} {before after : State Symbol Guard} (effects : Effect before after)
    {values : List (EdgeValue Symbol Guard)} (post : RowsPost holds ambient inputs before values) : RowsPost holds ambient inputs after values :=
  ⟨(fun edge member => InternedEdgeResidency.edge_grows before after effects.1.growth edge (post.resident edge member)), post.closed, post.covers⟩

/-- A successful ordered map retains both full cache effects and each positional certificate. -/
theorem map_done (call : Request → Action Symbol Guard Output)
    (pre : State Symbol Guard → Request → Prop) (post : State Symbol Guard → Request → Output → Prop)
    (preGrows : ∀ before after, Effect before after → ∀ request, pre before request → pre after request)
    (postGrows : ∀ before after, Effect before after → ∀ request value, post before request value → post after request value)
    (requests : List Request)
    (verified : ∀ request ∈ requests, ∀ before, SemanticReady before → pre before request →
      ∀ result after, call request before = .done result after → Effect before after ∧ post after request result)
    (before : State Symbol Guard) (semantic : SemanticReady before) (inputs : ∀ request ∈ requests, pre before request)
    (results : List Output) (after : State Symbol Guard) (done : map call requests before = .done results after) :
    Effect before after ∧ All₂ (post after) requests results := by
  induction requests generalizing before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact ⟨⟨pure_keeps _ semantic.ready, semantic⟩, .nil⟩
  | cons request requests ih =>
      obtain ⟨first, middle, called, later⟩ := (bind_done _ _ results after).mp done
      have checked := verified request List.mem_cons_self before semantic (inputs request List.mem_cons_self) first middle called
      obtain ⟨rest, final, mapped, returned⟩ := (bind_done _ _ results after).mp later
      have tail := ih (fun request member => verified request (List.mem_cons_of_mem _ member)) middle checked.1.2
        (fun request member => preGrows before middle checked.1 request (inputs request (List.mem_cons_of_mem _ member))) rest final mapped
      have parts := Result.done.inj returned
      cases parts.1; cases parts.2
      exact ⟨checked.1.trans tail.1, .cons (postGrows middle after tail.1 request first checked.2) tail.2⟩

/-- Recursive call correctness is required only at its actual closed available input cache. -/
def RecurseLaw (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) : Prop :=
  ∀ value before, SemanticReady before → Available before value → value.free = [] →
    ∀ result after, call value before = .done result after → Effect before after ∧ ValuePost holds ambient [value] after result

/-- Actual successful child traversal retains every positional coverage certificate. -/
theorem children_done (call : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (law : RecurseLaw call holds ambient)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (results : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : map call inputs before = .done results after) :
    Effect before after ∧ All₂ (fun value result => ValuePost holds ambient [value] after result) inputs results := by
  exact map_done call (fun state value => Available state value ∧ value.free = [])
    (fun state value result => ValuePost holds ambient [value] state result)
    (fun _ _ effects value ready => ⟨effects.1.available value ready.1, ready.2⟩)
    (fun _ _ effects _ _ post => post.grows effects) inputs
    (fun value _ state ready input result final done => law value state ready input.1 input.2 result final done)
    before semantic (fun value member => ⟨available value member, closed value member⟩) results after done

end MicroCFTA.SourceMergedContracts
